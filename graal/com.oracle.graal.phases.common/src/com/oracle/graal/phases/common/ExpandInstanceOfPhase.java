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

/**
 * The {code ExpandInstanceOfPhase} expands {@code InstanceOfNode} into a potential null check plus
 * an instanceof test on a non-null object and without profile. If the {@code InstanceOfNode} is
 * used by a {@FixedNode}, the expanded subgraph will be inserted before the {@FixedNode}.
 * Otherwise, the subgrpah will be inserted at {@code InstanceOfNode.getAnchor()}, or at the latest
 * {@FixedNode} in the current schedule.
 */
public class ExpandInstanceOfPhase extends BasePhase<PhaseContext> {

    @Override
    protected void run(StructuredGraph graph, PhaseContext context) {
        // First pass, expand InstanceOfNode at its FloatingNode usage. In terms of not
        // anchored InstanceOfNode (InstanceOfNode.anchor == null), we rely on a SchedulePhase to
        // locate the place for expanded subgraph.
        SchedulePhase schedulePhase = new SchedulePhase(SchedulingStrategy.EARLIEST);
        schedulePhase.apply(graph);
        ScheduleResult schedule = graph.getLastSchedule();
        for (InstanceOfNode instanceOf : graph.getNodes(InstanceOfNode.TYPE)) {
            processNotAnchoredInstanceOf(instanceOf, schedule, context.getStampProvider(), context.getMetaAccess(), context.getConstantReflection());
        }
        // Second pass, expand InstanceOfNode at its FixedNode usage.
        for (InstanceOfNode instanceOf : graph.getNodes(InstanceOfNode.TYPE)) {
            processAnchoredInstanceOf(instanceOf, context.getStampProvider(), context.getMetaAccess(), context.getConstantReflection());
        }
        // TODO uncomment assert graph.getNodes(InstanceOfNode.TYPE).isEmpty();
    }

    public static final double NULL_PROBABILITY = 0.1;
    public static final double HIT_PROBABILITY = 0.4;

    /**
     * Expand the given {@code InstanceOfNode instanceOf} preceding the given
     * {@code FixedNode insertBefore}. After the expansion, {@code insertBefore} (and its subsequent
     * control flow) will be temporarily disconnected. The caller is responsible for re-wiring the
     * control flow with the output {@code ArrayList<AbstractBeginNode> retTrueBranches} and
     * {@code ArrayList<AbstractBeginNode> retFalseBranches}, representing the branches of succeeded
     * or failed test for the given {@code instanceOf}, respectively.
     */
    private static void createDiamonds(InstanceOfNode instanceOf, FixedNode insertBefore, StampProvider stampProvider,
                    MetaAccessProvider metaAccessProvider, ConstantReflectionProvider constantReflectionProvider,
                    /* outputs */ ArrayList<AbstractBeginNode> retTrueBranches, ArrayList<AbstractBeginNode> retFalseBranches) {
        StructuredGraph graph = instanceOf.graph();
        FixedWithNextNode lastFixed = (FixedWithNextNode) insertBefore.predecessor();
        lastFixed.setNext(null);

        ObjectStamp checkedStamp = instanceOf.getCheckedStamp();
        ValueNode object = instanceOf.getValue();
        ObjectStamp objectStamp = ((ObjectStamp) object.stamp());

        // TODO add profile-based optimizations
        // Append IfNode for null check if needed.
        ValueNode nonNullObject = null;
        if (!objectStamp.nonNull()) {
            LogicNode nullCheck = graph.unique(new IsNullNode(object));
            BeginNode nullSuccessor = graph.createBegin();
            BeginNode nonNullSuccessor = graph.createBegin();
            IfNode ifNode = graph.add(new IfNode(nullCheck, nullSuccessor, nonNullSuccessor, 1.0 - NULL_PROBABILITY));
            nonNullObject = graph.addOrUnique(new PiNode(object, objectStamp.join(StampFactory.objectNonNull()), nonNullSuccessor));
            lastFixed.setNext(ifNode);
            lastFixed = nonNullSuccessor;
            if (checkedStamp.nonNull()) {
                // This is a check where x == null returns a false result.
                retFalseBranches.add(nullSuccessor);
            } else {
                // This is a check where x == null returns a true result.
                retTrueBranches.add(nullSuccessor);
            }
        } else {
            nonNullObject = object;
        }

        // We have now the object checked for nullness. Append IfNode for type check.
        ValueNode hub = graph.addOrUnique(LoadHubNode.create(nonNullObject, stampProvider, metaAccessProvider, constantReflectionProvider));
        LogicNode loweredInstanceOfNode = graph.addOrUnique(LoweredInstanceOfNode.create(checkedStamp.getTypeReference(), nonNullObject, hub));
        BeginNode trueSuccessor = graph.createBegin();
        BeginNode falseSuccessor = graph.createBegin();
        IfNode ifNode = graph.add(new IfNode(loweredInstanceOfNode, trueSuccessor, falseSuccessor, HIT_PROBABILITY));
        lastFixed.setNext(ifNode);
        retTrueBranches.add(trueSuccessor);
        retFalseBranches.add(falseSuccessor);

        assert retTrueBranches.size() > 0;
        assert retFalseBranches.size() > 0;
    }

    /**
     * Expand InstanceOfNode at its FloatingNode usage. The expanded subgraph will be inserted at
     * {@code InstanceOfNode.getAnchor()} if not null, or otherwise at the scheduled location.
     */
    private static void processNotAnchoredInstanceOf(InstanceOfNode instanceOf, ScheduleResult schedule, StampProvider stampProvider,
                    MetaAccessProvider metaAccessProvider, ConstantReflectionProvider constantReflectionProvider) {
        StructuredGraph graph = instanceOf.graph();

        for (Node usage : instanceOf.usages().snapshot()) {
            ArrayList<AbstractBeginNode> trueBranches = new ArrayList<>();
            ArrayList<AbstractBeginNode> falseBranches = new ArrayList<>();

            if (usage instanceof ConditionalNode) {
                FixedWithNextNode anchor = getAnchor(instanceOf, schedule);
                FrameState lastFrameState = findLastFrameState(anchor);
                FixedNode insertBefore = anchor.next();
                createDiamonds(instanceOf, insertBefore, stampProvider, metaAccessProvider, constantReflectionProvider, trueBranches, falseBranches);

                MergeNode merge = graph.createMerge();
                merge.setStateAfter(lastFrameState);

                ConditionalNode conditionalNode = (ConditionalNode) usage;
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
            } else if (usage instanceof ShortCircuitOrNode) {
                // TODO unwind ShortCircuitOrNode
            }
        }
    }

    /**
     * Expand InstanceOfNode at its FixedNode usage. The expanded subgraph will be inserted at the
     * FixedNode.
     */
    private static void processAnchoredInstanceOf(InstanceOfNode instanceOf, StampProvider stampProvider,
                    MetaAccessProvider metaAccessProvider, ConstantReflectionProvider constantReflectionProvider) {
        StructuredGraph graph = instanceOf.graph();
        for (Node usage : instanceOf.usages().snapshot()) {
            ArrayList<AbstractBeginNode> trueBranches = new ArrayList<>();
            ArrayList<AbstractBeginNode> falseBranches = new ArrayList<>();

            if (usage instanceof IfNode) {
                IfNode ifNode = (IfNode) usage;
                FrameState lastFrameState = findLastFrameState(ifNode);

                createDiamonds(instanceOf, ifNode, stampProvider, metaAccessProvider, constantReflectionProvider, trueBranches, falseBranches);

                AbstractBeginNode trueSuccessor = ifNode.trueSuccessor();
                AbstractBeginNode falseSuccessor = ifNode.falseSuccessor();

                ifNode.safeDelete();

                connectBranches(graph, lastFrameState, falseBranches, falseSuccessor);
                connectBranches(graph, lastFrameState, trueBranches, trueSuccessor);
            } else if (usage instanceof FixedGuardNode) {
                FixedGuardNode fixedGuardNode = (FixedGuardNode) usage;
                FrameState lastFrameState = findLastFrameState(fixedGuardNode);

                createDiamonds(instanceOf, fixedGuardNode, stampProvider, metaAccessProvider, constantReflectionProvider, trueBranches, falseBranches);

                ArrayList<AbstractBeginNode> deoptBranches = falseBranches;
                ArrayList<AbstractBeginNode> continueBranches = trueBranches;
                if (fixedGuardNode.isNegated()) {
                    deoptBranches = trueBranches;
                    continueBranches = falseBranches;
                }

                FixedNode successor = fixedGuardNode.next();
                fixedGuardNode.setNext(null);
                // create deoptimize branch
                DeoptimizeNode deoptizeNode = new DeoptimizeNode(fixedGuardNode.getAction(), fixedGuardNode.getReason(), fixedGuardNode.getSpeculation());
                AbstractBeginNode deoptBranch = BeginNode.begin(graph.add(deoptizeNode));
                AbstractBeginNode continueBranch = BeginNode.begin(successor);

                fixedGuardNode.replaceAtUsages(continueBranch);
                fixedGuardNode.safeDelete();

                connectBranches(graph, lastFrameState, deoptBranches, deoptBranch);
                connectBranches(graph, lastFrameState, continueBranches, continueBranch);
            } else if (usage instanceof ShortCircuitOrNode) {
                // TODO should have been handled in processNotAnchoredInstanceOf
            } else {
                System.out.println(usage.toString());
                assert false;
            }
        }

        if (instanceOf.hasNoUsages()) { // TODO remove this
            instanceOf.safeDelete();
        }
    }

    /**
     * Connect the given {@code ArrayList<AbstractBeginNode> branches} to the given
     * {@code AbstractBeginNode successor}.
     */
    private static void connectBranches(StructuredGraph graph, FrameState lastFrameState,
                    ArrayList<AbstractBeginNode> branches, AbstractBeginNode successor) {
        if (branches.size() > 1) {
            MergeNode merge = graph.createMerge();
            if (lastFrameState != null && lastFrameState.isAlive()) {
                // lastFrameState may be monopolistic and gets eliminated without checking
                // additional usage by other phases.
                merge.setStateAfter(lastFrameState.duplicate());
            }
            // If successor is of type BeginNode, it is safe to drop providing all its usages are
            // updated.
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
                // We preserve the successor if it is of type BeginStateSplitNode or
                // KillingBeginNode.
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

    /**
     * @return the anchor in the control flow graph for the given {@code InstanceOfNode instanceOf}.
     *         In case {@code InstanceOfNode.getAnchor()} is null, the scheduled location is
     *         returned.
     */
    private static FixedWithNextNode getAnchor(InstanceOfNode instanceOf, ScheduleResult schedule) {
        if (instanceOf.getAnchor() != null) {
            return instanceOf.getAnchor().asNode();
        } else {
            // We rely on Node order within a Block being the schedule, i.e., if the InstanceOfNode
            // is after a FixedWithNextNode, it is scheduled after that.
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
