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

import org.graalvm.compiler.graph.NodeSourcePosition;
import org.graalvm.compiler.nodes.DeoptimizeNode;
import org.graalvm.compiler.nodes.FrameState;
import org.graalvm.compiler.nodes.StructuredGraph;
import org.graalvm.compiler.nodes.debug.DynamicCounterNode;
import org.graalvm.compiler.phases.BasePhase;
import org.graalvm.compiler.phases.tiers.LowTierContext;

import jdk.vm.ci.meta.ResolvedJavaMethod;

public class ProfileDeoptimizationPhase extends BasePhase<LowTierContext> {

    private static final String BCI_SEP = "#";

    private static String fullName(ResolvedJavaMethod method) {
        if (method != null) {
            return method.format("%h.%n") + method.getSignature().toMethodDescriptor();
        } else {
            return "unknown method";
        }
    }

    @Override
    protected void run(StructuredGraph graph, LowTierContext context) {
        for (DeoptimizeNode deopt : graph.getNodes().filter(DeoptimizeNode.class)) {
            String contextInfo;
            NodeSourcePosition pos = deopt.getNodeSourcePosition();

            if (pos != null) {
                StringBuilder sb = new StringBuilder(100);

                while (pos != null) {
                    sb.append(fullName(pos.getMethod()));
                    sb.append(BCI_SEP);
                    sb.append(pos.getBCI());

                    pos = pos.getCaller();
                    if (pos != null) {
                        sb.append('|');
                    }
                }
                contextInfo = sb.toString();
            } else {
                FrameState state = deopt.stateBefore();
                contextInfo = "~" + fullName(state.getCode().getMethod()) + BCI_SEP + state.bci;
            }

            DynamicCounterNode.addCounterBefore(deopt.action().toString() + " " + deopt.reason().toString(), contextInfo.replace(';', ','), 1, true, deopt);
        }
    }

}
