/*
 * Copyright (c) 2016, 2016, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package com.oracle.graal.phases.common;

import java.util.ArrayList;

import com.oracle.graal.compiler.common.type.ObjectStamp;
import com.oracle.graal.compiler.common.type.StampFactory;
import com.oracle.graal.graph.Node;
import com.oracle.graal.nodes.AbstractBeginNode;
import com.oracle.graal.nodes.BeginNode;
import com.oracle.graal.nodes.DeoptimizeNode;
import com.oracle.graal.nodes.EndNode;
import com.oracle.graal.nodes.FixedGuardNode;
import com.oracle.graal.nodes.FixedNode;
import com.oracle.graal.nodes.FixedWithNextNode;
import com.oracle.graal.nodes.FrameState;
import com.oracle.graal.nodes.GuardPhiNode;
import com.oracle.graal.nodes.IfNode;
import com.oracle.graal.nodes.LogicNode;
import com.oracle.graal.nodes.MergeNode;
import com.oracle.graal.nodes.PiNode;
import com.oracle.graal.nodes.ShortCircuitOrNode;
import com.oracle.graal.nodes.StateSplit;
import com.oracle.graal.nodes.StructuredGraph;
import com.oracle.graal.nodes.StructuredGraph.ScheduleResult;
import com.oracle.graal.nodes.ValueNode;
import com.oracle.graal.nodes.ValuePhiNode;
import com.oracle.graal.nodes.calc.ConditionalNode;
import com.oracle.graal.nodes.calc.IsNullNode;
import com.oracle.graal.nodes.cfg.Block;
import com.oracle.graal.nodes.extended.LoadHubNode;
import com.oracle.graal.nodes.java.InstanceOfNode;
import com.oracle.graal.nodes.java.LoweredInstanceOfNode;
import com.oracle.graal.nodes.spi.StampProvider;
import com.oracle.graal.phases.BasePhase;
import com.oracle.graal.phases.schedule.SchedulePhase;
import com.oracle.graal.phases.schedule.SchedulePhase.SchedulingStrategy;
import com.oracle.graal.phases.tiers.PhaseContext;

import jdk.vm.ci.meta.ConstantReflectionProvider;
import jdk.vm.ci.meta.MetaAccessProvider;

public class ExpandInstanceOfPhase extends BasePhase<PhaseContext> {

    @Override
    protected void run(StructuredGraph graph, PhaseContext context) {
        SchedulePhase schedulePhase = new SchedulePhase(SchedulingStrategy.EARLIEST);
        schedulePhase.apply(graph);
        ScheduleResult schedule = graph.getLastSchedule();

        for (InstanceOfNode node : graph.getNodes(InstanceOfNode.TYPE)) {
            processNotAnchoredInstanceOf(graph, node, schedule, context.getStampProvider(), context.getMetaAccess(), context.getConstantReflection());
        }

        for (InstanceOfNode node : graph.getNodes(InstanceOfNode.TYPE)) {
            processInstanceOf(graph, node, context.getStampProvider(), context.getMetaAccess(), context.getConstantReflection());
        }
        // TODO uncomment assert graph.getNodes(InstanceOfNode.TYPE).isEmpty();
    }

    public static final double NULL_PROBABILITY = 0.1;
    public static final double HIT_PROBABILITY = 0.4;

    private static void createDiamonds(InstanceOfNode instanceOf, FixedNode insertBefore, ArrayList<AbstractBeginNode> trueBranches, ArrayList<AbstractBeginNode> falseBranches,
                    StampProvider stampProvider, MetaAccessProvider metaAccessProvider, ConstantReflectionProvider constantReflectionProvider) {
        FixedWithNextNode lastFixed = (FixedWithNextNode) insertBefore.predecessor();
        lastFixed.setNext(null);
        StructuredGraph graph = instanceOf.graph();

        ObjectStamp checkedStamp = instanceOf.getCheckedStamp();
        ValueNode object = instanceOf.getValue();
        ObjectStamp objectStamp = ((ObjectStamp) object.stamp());

        // insert null check if needed
        ValueNode nonNullObject = null;
        if (!objectStamp.nonNull()) {
            LogicNode nullCheck = graph.unique(new IsNullNode(object));
            BeginNode nullSuccessor = graph.createBegin();
            BeginNode nonNullSuccessor = graph.createBegin();
            IfNode ifNode = graph.add(new IfNode(nullCheck, nullSuccessor, nonNullSuccessor, 1.0 - NULL_PROBABILITY));
            nonNullObject = graph.addOrUnique(new PiNode(object, objectStamp.join(StampFactory.objectNonNull()), nonNullSuccessor));
            // append ifNode for null check
            lastFixed.setNext(ifNode);
            lastFixed = nonNullSuccessor;
            if (checkedStamp.nonNull()) {
                // This is a check where x == null returns a false result.
                falseBranches.add(nullSuccessor);
            } else {
                // This is a check where x == null returns a true result.
                trueBranches.add(nullSuccessor);
            }
        } else {
            nonNullObject = object;
        }

        // We have now the object checked for nullness.
        ValueNode hub = graph.addOrUnique(LoadHubNode.create(nonNullObject, stampProvider, metaAccessProvider, constantReflectionProvider));
        LogicNode loweredInstanceOfNode = graph.addOrUnique(LoweredInstanceOfNode.create(checkedStamp.getTypeReference(), nonNullObject, hub));

        BeginNode trueSuccessor = graph.createBegin();
        BeginNode falseSuccessor = graph.createBegin();
        IfNode ifNode = graph.add(new IfNode(loweredInstanceOfNode, trueSuccessor, falseSuccessor, HIT_PROBABILITY));
        // append ifNode for instanceof
        lastFixed.setNext(ifNode);
        trueBranches.add(trueSuccessor);
        falseBranches.add(falseSuccessor);

        assert trueBranches.size() > 0;
        assert falseBranches.size() > 0;
    }

    private static void processNotAnchoredInstanceOf(StructuredGraph graph, InstanceOfNode instanceOf, ScheduleResult schedule, StampProvider stampProvider,
                    MetaAccessProvider metaAccessProvider, ConstantReflectionProvider constantReflectionProvider) {
        for (Node n : instanceOf.usages().snapshot()) {
            ArrayList<AbstractBeginNode> trueBranches = new ArrayList<>();
            ArrayList<AbstractBeginNode> falseBranches = new ArrayList<>();

            if (n instanceof ConditionalNode) {
                FixedWithNextNode anchor = getAnchor(instanceOf, schedule);
                FrameState lastFrameState = findLastFrameState(anchor);
                FixedNode insertBefore = anchor.next();
                createDiamonds(instanceOf, insertBefore, trueBranches, falseBranches, stampProvider, metaAccessProvider, constantReflectionProvider);

                MergeNode merge = graph.createMerge();
                merge.setStateAfter(lastFrameState);

                ConditionalNode conditionalNode = (ConditionalNode) n;
                ValuePhiNode valuePhi = graph.addWithoutUnique(new ValuePhiNode(conditionalNode.stamp(), merge));

                // Connect false branches.
                for (AbstractBeginNode branch : falseBranches) {
                    EndNode end = graph.createEnd();
                    branch.setNext(end);
                    valuePhi.addInput(conditionalNode.falseValue());
                    merge.addForwardEnd(end);
                }

                // Connect true branches.
                for (AbstractBeginNode branch : trueBranches) {
                    EndNode end = graph.createEnd();
                    branch.setNext(end);
                    valuePhi.addInput(conditionalNode.trueValue());
                    merge.addForwardEnd(end);
                }

                merge.setNext(insertBefore);
                conditionalNode.replaceAtUsages(valuePhi);
                conditionalNode.safeDelete();
            } else if (n instanceof ShortCircuitOrNode) {
                // TODO unwind ShortCircuitOrNode
            }
        }
    }

    private static void processInstanceOf(StructuredGraph graph, InstanceOfNode instanceOf, StampProvider stampProvider,
                    MetaAccessProvider metaAccessProvider, ConstantReflectionProvider constantReflectionProvider) {
        for (Node n : instanceOf.usages().snapshot()) {
            // The InstanceOfNode will be expanded into a potential null check (IsNullNode) and a
            // lowered instanceof check (loweredInstanceOfNode). In case it results into 3 branches,
            // we need to record them and connect to the corresponding successors.
            ArrayList<AbstractBeginNode> trueBranches = new ArrayList<>();
            ArrayList<AbstractBeginNode> falseBranches = new ArrayList<>();

            if (n instanceof IfNode) {
                IfNode ifNode = (IfNode) n;
                FrameState lastFrameState = findLastFrameState(ifNode);

                createDiamonds(instanceOf, ifNode, trueBranches, falseBranches, stampProvider, metaAccessProvider, constantReflectionProvider);

                AbstractBeginNode trueSuccessor = ifNode.trueSuccessor();
                AbstractBeginNode falseSuccessor = ifNode.falseSuccessor();

                // at this point we are safe to drop the original IfNode
                ifNode.safeDelete();

                connectBranches(graph, lastFrameState, falseBranches, falseSuccessor);
                connectBranches(graph, lastFrameState, trueBranches, trueSuccessor);
            } else if (n instanceof FixedGuardNode) {
                FixedGuardNode fixedGuardNode = (FixedGuardNode) n;
                FrameState lastFrameState = findLastFrameState(fixedGuardNode);

                createDiamonds(instanceOf, fixedGuardNode, trueBranches, falseBranches, stampProvider, metaAccessProvider, constantReflectionProvider);

                ArrayList<AbstractBeginNode> deoptBranches = falseBranches;
                ArrayList<AbstractBeginNode> continueBranches = trueBranches;
                if (fixedGuardNode.isNegated()) {
                    deoptBranches = trueBranches;
                    continueBranches = falseBranches;
                }

                AbstractBeginNode deoptBranch = BeginNode.begin(graph.add(new DeoptimizeNode(fixedGuardNode.getAction(), fixedGuardNode.getReason(), fixedGuardNode.getSpeculation())));
                connectBranches(graph, lastFrameState, deoptBranches, deoptBranch);

                FixedNode successor = fixedGuardNode.next();
                fixedGuardNode.setNext(null);

                AbstractBeginNode continueBranch = BeginNode.begin(successor);
                fixedGuardNode.replaceAtUsages(continueBranch);
                fixedGuardNode.safeDelete();

                connectBranches(graph, lastFrameState, continueBranches, continueBranch);
            } else if (n instanceof ShortCircuitOrNode) {
                // TODO should have been handled in processNotAnchoredInstanceOf
            } else {
                System.out.println(n.toString());
                assert false;
            }
        }

        if (instanceOf.hasNoUsages()) { // TODO remove this
            instanceOf.safeDelete();
        }
    }

    private static void connectBranches(StructuredGraph graph, FrameState lastFrameState, ArrayList<AbstractBeginNode> branches, AbstractBeginNode successor) {
        if (branches.size() > 1) {
            MergeNode merge = graph.createMerge();
            merge.setStateAfter(lastFrameState);
            GuardPhiNode guardPhi = null;
            if (successor.hasUsages() && successor instanceof BeginNode) {
                guardPhi = graph.addWithoutUnique(new GuardPhiNode(merge));
                successor.replaceAtUsages(guardPhi);
            }

            // Connect false branches.
            for (AbstractBeginNode branch : branches) {
                EndNode end = graph.createEnd();
                branch.setNext(end);
                if (guardPhi != null) {
                    guardPhi.addInput(branch);
                }
                merge.addForwardEnd(end);
            }

            if (successor instanceof BeginNode) {
                FixedNode next = successor.next();
                successor.setNext(null);
                merge.setNext(next);
                successor.safeDelete();
            } else {
                merge.setNext(successor);
            }
        } else {
            AbstractBeginNode soloBranch = branches.get(0);
            soloBranch.replaceAtPredecessor(successor);
            soloBranch.safeDelete();
        }
    }

    private static FrameState findLastFrameState(FixedNode node) {
        FixedNode lastFixed = node;
        while (!(lastFixed instanceof StateSplit)) {
            lastFixed = (FixedNode) lastFixed.predecessor();
        }
        return ((StateSplit) lastFixed).stateAfter();
    }

    private static FixedWithNextNode getAnchor(InstanceOfNode instanceOf, ScheduleResult schedule) {
        if (instanceOf.getAnchor() != null) {
            return instanceOf.getAnchor().asNode();
        } else {
            Block block = schedule.getNodeToBlockMap().get(instanceOf);
            FixedWithNextNode lastFixed = block.getBeginNode();

            for (Node node : schedule.nodesFor(block)) {
                if (node.isDeleted()) {
                    continue;
                }
                if (node instanceof FixedWithNextNode) {
                    lastFixed = (FixedWithNextNode) node;
                }
                if (node == instanceOf) {
                    break;
                }
            }
            return lastFixed;
        }
    }

}
