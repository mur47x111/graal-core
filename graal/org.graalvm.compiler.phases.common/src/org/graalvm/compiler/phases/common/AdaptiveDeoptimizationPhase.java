/*
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved.
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
package org.graalvm.compiler.phases.common;

import static jdk.vm.ci.code.MemoryBarriers.JMM_POST_VOLATILE_READ;
import static jdk.vm.ci.code.MemoryBarriers.JMM_POST_VOLATILE_WRITE;
import static jdk.vm.ci.code.MemoryBarriers.JMM_PRE_VOLATILE_READ;
import static jdk.vm.ci.code.MemoryBarriers.JMM_PRE_VOLATILE_WRITE;

import java.lang.reflect.Field;
import java.util.Map.Entry;
import java.util.concurrent.ConcurrentHashMap;

import org.graalvm.compiler.core.common.type.StampFactory;
import org.graalvm.compiler.graph.NodeSourcePosition;
import org.graalvm.compiler.nodes.ConstantNode;
import org.graalvm.compiler.nodes.DeoptimizeNode;
import org.graalvm.compiler.nodes.FieldLocationIdentity;
import org.graalvm.compiler.nodes.IfNode;
import org.graalvm.compiler.nodes.StructuredGraph;
import org.graalvm.compiler.nodes.calc.AddNode;
import org.graalvm.compiler.nodes.calc.IntegerBelowNode;
import org.graalvm.compiler.nodes.extended.MembarNode;
import org.graalvm.compiler.nodes.memory.HeapAccess.BarrierType;
import org.graalvm.compiler.nodes.memory.ReadNode;
import org.graalvm.compiler.nodes.memory.WriteNode;
import org.graalvm.compiler.nodes.memory.address.AddressNode;
import org.graalvm.compiler.nodes.memory.address.OffsetAddressNode;
import org.graalvm.compiler.phases.BasePhase;
import org.graalvm.compiler.phases.tiers.LowTierContext;

import jdk.vm.ci.common.JVMCIError;
import jdk.vm.ci.meta.DeoptimizationAction;
import jdk.vm.ci.meta.DeoptimizationReason;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import sun.misc.Unsafe;

public class AdaptiveDeoptimizationPhase extends BasePhase<LowTierContext> {

    public static class Counter {
        public volatile int value = 0;
    }

    public static final ConcurrentHashMap<String, Counter> executionCounters = new ConcurrentHashMap<>();
    public static final ConcurrentHashMap<String, Counter> agedCounters = new ConcurrentHashMap<>();

    public static Counter getCounter(ConcurrentHashMap<String, Counter> counters, String key) {
        counters.putIfAbsent(key, new Counter());
        return counters.get(key);
    }

    static final Unsafe UNSAFE = initUnsafe();

    private static Unsafe initUnsafe() {
        try {
            // Fast path when we are trusted.
            return Unsafe.getUnsafe();
        } catch (SecurityException se) {
            // Slow path when we are not trusted.
            try {
                Field theUnsafe = Unsafe.class.getDeclaredField("theUnsafe");
                theUnsafe.setAccessible(true);
                return (Unsafe) theUnsafe.get(Unsafe.class);
            } catch (Exception e) {
                throw new RuntimeException("exception while trying to get Unsafe", e);
            }
        }
    }

    public static String fullName(ResolvedJavaMethod method) {
        if (method != null) {
            return method.format("%H.%n") + method.getSignature().toMethodDescriptor();
        } else {
            return "unknown method";
        }
    }

    private long fieldOffset;
    private ResolvedJavaField fieldCache;

    private final int aging;
    private final int lowerBound;
    private final int upperBound;

    public AdaptiveDeoptimizationPhase(int aging, int lowerBound, int upperBound) {
        this.aging = aging;
        this.lowerBound = lowerBound;
        this.upperBound = upperBound;

        if (aging > 0) {
            Thread thread = new Thread() {
                @Override
                public void run() {
                    while (true) {
                        try {
                            Thread.sleep(aging);
                        } catch (InterruptedException e) {
                        }
                        for (Entry<String, Counter> entry : executionCounters.entrySet()) {
                            getCounter(agedCounters, entry.getKey()).value += entry.getValue().value;
                            entry.getValue().value = 0;
                        }
                    }
                }
            };
            thread.setDaemon(true);
            thread.setPriority(Thread.MAX_PRIORITY);
            thread.start();
        }
    }

    @Override
    protected void run(StructuredGraph graph, LowTierContext context) {
        if (fieldCache == null) {
            try {
                Field value = Counter.class.getDeclaredField("value");
                fieldCache = context.getMetaAccess().lookupJavaField(value);
                fieldOffset = UNSAFE.objectFieldOffset(value);
            } catch (Exception e) {
                JVMCIError.shouldNotReachHere(e);
            }
        }
        if (graph.method() == null) {
            return;
        }
        String klassName = graph.method().format("%H");
        if (klassName.startsWith("org.graalvm.compiler") || klassName.startsWith("jdk.vm.ci")) {
            return;
        }

        for (DeoptimizeNode deopt : graph.getNodes().filter(DeoptimizeNode.class)) {
            if (deopt.action() != DeoptimizationAction.InvalidateReprofile) {
                continue;
            }
            if (!(deopt.reason() == DeoptimizationReason.UnreachedCode ||
                            deopt.reason() == DeoptimizationReason.TypeCheckedInliningViolated ||
                            deopt.reason() == DeoptimizationReason.OptimizedTypeCheckViolated)) {
                continue;
            }
            NodeSourcePosition pos = deopt.getNodeSourcePosition();
            if (pos == null) {
                continue;
            }

            String key = fullName(pos.getMethod()) + "#" + pos.getBCI() + ":" + deopt.action().toString() + ":" + deopt.reason().toString();
            Counter executionCounter = getCounter(executionCounters, key);
            Counter agedCounter = getCounter(agedCounters, key);
            int total = executionCounter.value + agedCounter.value;

            if (total >= upperBound) {
                if (graph.method() == pos.getMethod()) {
                    DeoptimizeNode stopCompiling = graph.add(new DeoptimizeNode(DeoptimizationAction.InvalidateStopCompiling, deopt.reason(), deopt.getSpeculation()));
                    deopt.replaceAndDelete(stopCompiling);
                } else {
                    pos.getMethod().setNotInlineable();
                    DeoptimizeNode recompile = graph.add(new DeoptimizeNode(DeoptimizationAction.InvalidateRecompile, deopt.reason(), deopt.getSpeculation()));
                    deopt.replaceAndDelete(recompile);
                }
            } else if (total < lowerBound) {
                if (aging == 0) {
                    // De-optimization profile is not aging. The execution time profile is aged for
                    // each re-compilation.
                    agedCounter.value += executionCounter.value;
                    executionCounter.value = 0;
                }

                JavaConstant counter = context.getConstantReflection().forObject(executionCounter);
                ConstantNode counterCst = ConstantNode.forConstant(counter, context.getMetaAccess(), graph);
                ConstantNode threshold = ConstantNode.forLong(lowerBound, graph);
                AddressNode address = graph.unique(new OffsetAddressNode(counterCst, ConstantNode.forIntegerKind(context.getTarget().wordJavaKind, fieldOffset, graph)));
                FieldLocationIdentity location = new FieldLocationIdentity(fieldCache);

                ReadNode memoryRead = graph.add(new ReadNode(address, location, StampFactory.forKind(JavaKind.Long), BarrierType.NONE));
                graph.addBeforeFixed(deopt, memoryRead);

                AddNode add = graph.unique(new AddNode(memoryRead, ConstantNode.forLong(1, graph)));
                WriteNode memoryWrite = graph.add(new WriteNode(address, location, add, BarrierType.NONE));
                graph.addBeforeFixed(deopt, memoryWrite);

                memoryWrite.setNext(null);

                DeoptimizeNode deoptNone = graph.add(new DeoptimizeNode(DeoptimizationAction.None, deopt.reason(), deopt.getSpeculation()));
                deoptNone.setStateBefore(deopt.stateBefore());
                IntegerBelowNode below = graph.unique(new IntegerBelowNode(memoryRead, threshold));
                IfNode ifNode = graph.add(new IfNode(below, deoptNone, deopt, 0.5));
                memoryWrite.setNext(ifNode);

                graph.addBeforeFixed(memoryRead, graph.add(new MembarNode(JMM_PRE_VOLATILE_READ)));
                graph.addAfterFixed(memoryRead, graph.add(new MembarNode(JMM_POST_VOLATILE_READ)));

                graph.addBeforeFixed(memoryWrite, graph.add(new MembarNode(JMM_PRE_VOLATILE_WRITE)));
                graph.addAfterFixed(memoryWrite, graph.add(new MembarNode(JMM_POST_VOLATILE_WRITE)));

            }
        }
    }

}
