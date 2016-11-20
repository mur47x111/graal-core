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

import com.oracle.graal.compiler.common.cfg.Loop;
import com.oracle.graal.compiler.common.type.ObjectStamp;
import com.oracle.graal.compiler.common.type.StampFactory;
import com.oracle.graal.debug.GraalError;
import com.oracle.graal.graph.Node;
import com.oracle.graal.nodes.AbstractBeginNode;
import com.oracle.graal.nodes.AbstractMergeNode;
import com.oracle.graal.nodes.BeginNode;
import com.oracle.graal.nodes.BeginStateSplitNode;
import com.oracle.graal.nodes.ConstantNode;
import com.oracle.graal.nodes.DeoptimizeNode;
import com.oracle.graal.nodes.EndNode;
import com.oracle.graal.nodes.FixedGuardNode;
import com.oracle.graal.nodes.FixedNode;
import com.oracle.graal.nodes.FixedWithNextNode;
import com.oracle.graal.nodes.FrameState;
import com.oracle.graal.nodes.GuardPhiNode;
import com.oracle.graal.nodes.IfNode;
import com.oracle.graal.nodes.LogicNode;
import com.oracle.graal.nodes.LoopBeginNode;
import com.oracle.graal.nodes.LoopExitNode;
import com.oracle.graal.nodes.MergeNode;
import com.oracle.graal.nodes.PiNode;
import com.oracle.graal.nodes.ShortCircuitOrNode;
import com.oracle.graal.nodes.StateSplit;
import com.oracle.graal.nodes.StructuredGraph;
import com.oracle.graal.nodes.StructuredGraph.ScheduleResult;
import com.oracle.graal.nodes.ValueNode;
import com.oracle.graal.nodes.ValuePhiNode;
import com.oracle.graal.nodes.calc.ConditionalNode;
import com.oracle.graal.nodes.calc.IntegerEqualsNode;
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
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;

/**
 * The {@code ExpandInstanceOfPhase} expands {@code InstanceOfNode} into an instanceof test on a
 * non-null object and without profile preceded by a potential null check. If the
 * {@code InstanceOfNode} is used by a {@code FixedNode} or its anchor is not null, the expanded
 * subgraph will be inserted before the {@code FixedNode} or the anchor. Otherwise, the subgrpah
 * will be inserted at the latest {@code FixedNode} in the current schedule.
 */
public class ExpandInstanceOfPhase extends BasePhase<PhaseContext> {

    @Override
    protected void run(StructuredGraph graph, PhaseContext context) {
        // The first SchedulePhase is for generating loop exit nodes for transforming fixed guard
        // within loops.
        new SchedulePhase(SchedulingStrategy.LATEST).apply(graph, false);
        // Expand ShortCircuitOrNode.
        // TODO Drop ShortCircuitOrNodeTest.testSharedCondition test.
        for (InstanceOfNode instanceOf : graph.getNodes(InstanceOfNode.TYPE)) {
            for (Node usage : instanceOf.usages().snapshot()) {
                if (usage instanceof ShortCircuitOrNode) {
                    expandShortCircuitOrUsage((ShortCircuitOrNode) usage);
                }
            }
        }

        for (InstanceOfNode instanceOf : graph.getNodes(InstanceOfNode.TYPE)) {
            processAnchoredInstanceOf(instanceOf, context.getStampProvider(), context.getMetaAccess(), context.getConstantReflection());
        }
        new IterativeConditionalEliminationPhase(new CanonicalizerPhase(), false).apply(graph, context);

        assert graph.getNodes(InstanceOfNode.TYPE).isEmpty();
    }

    public static final double NULL_PROBABILITY = 0.1;
    public static final double HIT_PROBABILITY = 0.4;

    /**
     * Expand the given {@code InstanceOfNode instanceOf} into a subgraph. The caller is responsible
     * for connecting the subgraph. The return value is the only entrance, while various exists are
     * stored in {@code retTrueBranches} and {@code retFalseBranches}, representing the branches of
     * succeeded or failed test for the given {@code instanceOf}, respectively.
     *
     * @return the starting node of the expanded subgraph.
     */
    private static FixedNode createDiamonds(InstanceOfNode instanceOf, StampProvider stampProvider,
                    MetaAccessProvider metaAccessProvider, ConstantReflectionProvider constantReflectionProvider,
                    /* outputs */ ArrayList<AbstractBeginNode> retTrueBranches, ArrayList<AbstractBeginNode> retFalseBranches) {
        StructuredGraph graph = instanceOf.graph();
        FixedNode subGraphStart = null;

        ObjectStamp checkedStamp = instanceOf.getCheckedStamp();
        ValueNode object = instanceOf.getValue();
        ObjectStamp objectStamp = ((ObjectStamp) object.stamp());

        // TODO add profile-based optimizations
        // Append IfNode for null check if needed.
        ValueNode nonNullObject = null;
        BeginNode nonNullSuccessor = null;

        if (!objectStamp.nonNull()) {
            LogicNode nullCheck = graph.unique(new IsNullNode(object));
            BeginNode nullSuccessor = graph.createBegin();

            nonNullSuccessor = graph.createBegin();
            IfNode ifNode = graph.add(new IfNode(nullCheck, nullSuccessor, nonNullSuccessor, 1.0 - NULL_PROBABILITY));
            nonNullObject = graph.addOrUnique(new PiNode(object, objectStamp.join(StampFactory.objectNonNull()), nonNullSuccessor));
            subGraphStart = ifNode;
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
        if (nonNullSuccessor == null) {
            subGraphStart = ifNode;
        } else {
            nonNullSuccessor.setNext(ifNode);
        }
        retTrueBranches.add(trueSuccessor);
        retFalseBranches.add(falseSuccessor);

        assert retTrueBranches.size() > 0;
        assert retFalseBranches.size() > 0;

        return subGraphStart;
    }

    /**
     * Expand InstanceOfNode at its FixedNode usage.
     */
    private static void processAnchoredInstanceOf(InstanceOfNode instanceOf, StampProvider stampProvider,
                    MetaAccessProvider metaAccessProvider, ConstantReflectionProvider constantReflectionProvider) {
        StructuredGraph graph = instanceOf.graph();

        for (Node usage : instanceOf.usages().snapshot()) {

            if (usage instanceof IfNode) {
                // Replace the IfNode with the generated subgraph. Connect the
                // trueBranches/falseSuccessor of the subgraph to its trueSuccessor/falseSuccessor.
                IfNode ifNode = (IfNode) usage;
                FrameState lastFrameState = findLastFrameState(ifNode);

                ArrayList<AbstractBeginNode> trueBranches = new ArrayList<>();
                ArrayList<AbstractBeginNode> falseBranches = new ArrayList<>();
                FixedNode subGraphStart = createDiamonds(instanceOf, stampProvider, metaAccessProvider, constantReflectionProvider, trueBranches, falseBranches);
                ifNode.replaceAtPredecessor(subGraphStart);

                AbstractBeginNode trueSuccessor = ifNode.trueSuccessor();
                AbstractBeginNode falseSuccessor = ifNode.falseSuccessor();

                ifNode.safeDelete();

                connectBranches(graph, lastFrameState, falseBranches, falseSuccessor);
                connectBranches(graph, lastFrameState, trueBranches, trueSuccessor);
            } else if (usage instanceof FixedGuardNode) {
                // Replace the FixedGuardNode with the generated subgraph. Connect the
                // trueBranches/falseSuccessor of the subgraph to the successor node or a
                // deoptimization branch.
                FixedGuardNode fixedGuardNode = (FixedGuardNode) usage;
                FrameState lastFrameState = findLastFrameState(fixedGuardNode);

                ArrayList<AbstractBeginNode> trueBranches = new ArrayList<>();
                ArrayList<AbstractBeginNode> falseBranches = new ArrayList<>();
                FixedNode subGraphStart = createDiamonds(instanceOf, stampProvider, metaAccessProvider, constantReflectionProvider, trueBranches, falseBranches);
                FixedNode successor = fixedGuardNode.next();
                fixedGuardNode.setNext(null);
                fixedGuardNode.replaceAtPredecessor(subGraphStart);

                ArrayList<AbstractBeginNode> deoptBranches;
                ArrayList<AbstractBeginNode> continueBranches;

                if (fixedGuardNode.isNegated()) {
                    deoptBranches = trueBranches;
                    continueBranches = falseBranches;
                } else {
                    deoptBranches = falseBranches;
                    continueBranches = trueBranches;
                }

                // create deoptimization branch
                DeoptimizeNode deoptizeNode = new DeoptimizeNode(fixedGuardNode.getAction(), fixedGuardNode.getReason(), fixedGuardNode.getSpeculation());
                AbstractBeginNode deoptBranch = BeginNode.begin(graph.add(deoptizeNode));
                AbstractBeginNode continueBranch = BeginNode.begin(successor);

                ScheduleResult schedule = graph.getLastSchedule();
                Block block = schedule.getNodeToBlockMap().get(fixedGuardNode);
                insertLoopExits(block, deoptizeNode);

                fixedGuardNode.replaceAtUsages(continueBranch);
                fixedGuardNode.safeDelete();

                connectBranches(graph, lastFrameState, deoptBranches, deoptBranch);
                connectBranches(graph, lastFrameState, continueBranches, continueBranch);
            } else if (usage instanceof ConditionalNode) {
                // Insert the generated subgraph after the InstanceOfNode's anchor. Replace the
                // InstanceOfNode at the ConditionalNode's inputs with an IntegerEqualsNode
                // that tests whether the trueBranches are taken.
                ConditionalNode conditionalNode = (ConditionalNode) usage;
                assert conditionalNode.condition() == instanceOf;

                ArrayList<Node> path = new ArrayList<>();
                while (findPathFromFixedNode(conditionalNode, path) && conditionalNode.condition() == instanceOf) {
                    FixedNode insertBefore = (FixedNode) path.get(0);
                    Node current = insertBefore;
                    for (int i = 1; i < path.size(); i++) {
                        Node input = path.get(i);
                        if (input instanceof ValuePhiNode || input.getUsageCount() <= 1) {
                            current = input;
                        } else {
                            Node clone = input.copyWithInputs();
                            current.replaceFirstInput(input, clone);
                            current = clone;
                        }
                    }

                    if (insertBefore instanceof AbstractMergeNode) {
                        // use last schedule
                        ScheduleResult result = graph.getLastSchedule();
                        Block b = result.getNodeToBlockMap().get(instanceOf);
                        FixedWithNextNode lastFixed = null;

                        for (Node n : result.getBlockToNodesMap().get(b)) {
                            if (n instanceof FixedWithNextNode && n.isAlive()) {
                                lastFixed = (FixedWithNextNode) n;
                            } else if (n == instanceOf) {
                                break;
                            }
                        }

                        assert lastFixed != null;
                        insertBefore = lastFixed.next();
                    } else if (insertBefore instanceof BeginStateSplitNode) {
                        insertBefore = (FixedNode) ((BeginStateSplitNode) insertBefore).predecessor();
                    }
                    FrameState lastFrameState = findLastFrameState((FixedNode) insertBefore.predecessor());

                    ArrayList<AbstractBeginNode> trueBranches = new ArrayList<>();
                    ArrayList<AbstractBeginNode> falseBranches = new ArrayList<>();
                    FixedNode subGraphStart = createDiamonds(instanceOf, stampProvider, metaAccessProvider, constantReflectionProvider, trueBranches, falseBranches);
                    ValuePhiNode valuePhi = mergeBranches(graph, trueBranches, falseBranches);

                    insertBefore.replaceAtPredecessor(subGraphStart);
                    AbstractMergeNode merge = valuePhi.merge();
                    merge.setNext(insertBefore);
                    if (lastFrameState != null && lastFrameState.isAlive()) {
                        merge.setStateAfter(lastFrameState.duplicate());
                    }

                    IntegerEqualsNode compare = graph.addWithoutUnique(new IntegerEqualsNode(valuePhi, ConstantNode.forBoolean(true, graph)));
                    current.replaceFirstInput(instanceOf, compare);
                    path = new ArrayList<>();
                }
            } else {
                throw GraalError.shouldNotReachHere("Unexpected InstanceOfNode usage of type " + usage.getNodeClass());
            }
        }

        assert instanceOf.hasNoUsages();
        instanceOf.safeDelete();
    }

    /**
     * @return true if any usage path from a FixedNode to the given ValueNode can be found. Nodes
     *         along the path will be stored in {@code pathFromFixed}.
     */
    private static boolean findPathFromFixedNode(Node to, /* output */ ArrayList<Node> pathFromFixed) {
        boolean found = false;
        for (Node usage : to.usages()) {
            if (usage instanceof FixedNode) {
                pathFromFixed.add(usage);
                found = true;
                break;
            } else if (usage instanceof ValuePhiNode) {
                ValuePhiNode phi = (ValuePhiNode) usage;
                int index = phi.values().indexOf(to);
                pathFromFixed.add(phi.merge().forwardEndAt(index));
                pathFromFixed.add(phi);
                found = true;
                break;
            } else if ((usage instanceof ValueNode || usage instanceof FrameState) && findPathFromFixedNode(usage, pathFromFixed)) {
                found = true;
                break;
            }
        }
        if (found) {
            pathFromFixed.add(to);
            return true;
        } else {
            return false;
        }
    }

    /**
     * Expand ShortCircuitOrNode. The method is identical to ExpandLogicPhase.processBinary except
     * FixedGuardNode usage is also addressed in this method.
     */
    private static void expandShortCircuitOrUsage(ShortCircuitOrNode binary) {
        while (binary.usages().isNotEmpty()) {
            Node usage = binary.usages().first();
            if (usage instanceof ShortCircuitOrNode) {
                expandShortCircuitOrUsage((ShortCircuitOrNode) usage);
            } else if (usage instanceof IfNode) {
                ExpandLogicPhase.processIf(binary.getX(), binary.isXNegated(), binary.getY(), binary.isYNegated(), (IfNode) usage, binary.getShortCircuitProbability());
            } else if (usage instanceof ConditionalNode) {
                ExpandLogicPhase.processConditional(binary.getX(), binary.isXNegated(), binary.getY(), binary.isYNegated(), (ConditionalNode) usage);
            } else if (usage instanceof FixedGuardNode) {
                // Expand FixedGuardNode
                StructuredGraph graph = binary.graph();
                FixedGuardNode fixedGuardNode = (FixedGuardNode) usage;
                FixedNode successor = fixedGuardNode.next();
                fixedGuardNode.setNext(null);

                DeoptimizeNode deoptizeNode = new DeoptimizeNode(fixedGuardNode.getAction(), fixedGuardNode.getReason(), fixedGuardNode.getSpeculation());
                AbstractBeginNode deoptBranch = BeginNode.begin(graph.add(deoptizeNode));
                AbstractBeginNode continueBranch = BeginNode.begin(successor);

                AbstractBeginNode trueSuccessor;
                AbstractBeginNode falseSuccessor;

                ScheduleResult schedule = graph.getLastSchedule();
                Block block = schedule.getNodeToBlockMap().get(fixedGuardNode);
                insertLoopExits(block, deoptizeNode);

                if (fixedGuardNode.isNegated()) {
                    trueSuccessor = deoptBranch;
                    falseSuccessor = continueBranch;
                } else {
                    trueSuccessor = continueBranch;
                    falseSuccessor = deoptBranch;
                }

                IfNode ifNode = graph.add(new IfNode(binary, trueSuccessor, falseSuccessor, trueSuccessor == continueBranch ? 1 : 0));
                fixedGuardNode.replaceAtPredecessor(ifNode);

                fixedGuardNode.replaceAtUsages(continueBranch);
                fixedGuardNode.safeDelete();
            } else {
                throw GraalError.shouldNotReachHere();
            }
        }
        binary.safeDelete();
    }

    private static void insertLoopExits(Block block, DeoptimizeNode deopt) {
        Loop<Block> loop = block.getLoop();
        StructuredGraph graph = deopt.graph();
        while (loop != null) {
            LoopExitNode exit = graph.add(new LoopExitNode((LoopBeginNode) loop.getHeader().getBeginNode()));
            graph.addBeforeFixed(deopt, exit);
            loop = loop.getParent();
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

    private static ValuePhiNode mergeBranches(StructuredGraph graph, ArrayList<AbstractBeginNode> trueBranches, ArrayList<AbstractBeginNode> falseBranches) {
        MergeNode merge = graph.createMerge();
        ValuePhiNode valuePhi = graph.addWithoutUnique(new ValuePhiNode(StampFactory.forKind(JavaKind.Boolean), merge));

        // Connect true branches.
        for (AbstractBeginNode branch : trueBranches) {
            EndNode end = graph.createEnd();
            branch.setNext(end);
            merge.addForwardEnd(end);
            valuePhi.addInput(ConstantNode.forBoolean(true, graph));
        }

        // Connect false branches.
        for (AbstractBeginNode branch : falseBranches) {
            EndNode end = graph.createEnd();
            branch.setNext(end);
            merge.addForwardEnd(end);
            valuePhi.addInput(ConstantNode.forBoolean(false, graph));
        }

        return valuePhi;
    }

    private static FrameState findLastFrameState(FixedNode node) {
        FixedNode lastFixed = node;
        while (!(lastFixed instanceof StateSplit)) {
            lastFixed = (FixedNode) lastFixed.predecessor();
        }
        return ((StateSplit) lastFixed).stateAfter();
    }

}
