/*
 * Copyright (c) 2012, 2016, Oracle and/or its affiliates. All rights reserved.
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

import org.graalvm.compiler.debug.MethodFilter;
import org.graalvm.compiler.graph.NodeSourcePosition;
import org.graalvm.compiler.nodeinfo.Verbosity;
import org.graalvm.compiler.nodes.FixedNode;
import org.graalvm.compiler.nodes.FixedWithNextNode;
import org.graalvm.compiler.nodes.StructuredGraph;
import org.graalvm.compiler.nodes.debug.DynamicCounterNode;
import org.graalvm.compiler.phases.Phase;

import jdk.vm.ci.meta.MetaUtil;

public class ProfileFixedNodePhase extends Phase {

    private static final char SEPARATOR = '@';

    private final MethodFilter[] methodFilters;
    private final boolean insertAfter;

    public ProfileFixedNodePhase(String commaSeparatedPatterns, boolean insertAfter) {
        this.methodFilters = parse(commaSeparatedPatterns);
        this.insertAfter = insertAfter;
    }

    @Override
    protected void run(StructuredGraph graph) {
        for (FixedNode node : graph.getNodes().filter(FixedNode.class)) {
            if (MethodFilter.matchesClassName(methodFilters, node.getClass().getName())) {
                StringBuilder identifier = new StringBuilder();
                identifier.append(node.toString(Verbosity.Name));
                identifier.append(SEPARATOR);
                if (node.getNodeSourcePosition() != null) {
                    identifier.append(textifyNodeSourcePosition(node.getNodeSourcePosition()));
                }
                DynamicCounterNode.addCounterBefore(node.getNodeClass().shortName(), identifier.toString(),
                                1, true, insertAfter ? ((FixedWithNextNode) node).next() : node);
            }
        }
    }

    private static String textifyNodeSourcePosition(NodeSourcePosition nodeSourcePosition) {
        StringBuilder sb = new StringBuilder(100);
        NodeSourcePosition pos = nodeSourcePosition;
        while (pos != null) {
            MetaUtil.appendLocation(sb.append("at "), pos.getMethod(), pos.getBCI());
            pos = pos.getCaller();
            if (pos != null) {
                sb.append(" ");
            }
        }
        return sb.toString();
    }

    private static MethodFilter[] parse(String commaSeparatedPatterns) {
        String[] filters = commaSeparatedPatterns.split(",");
        MethodFilter[] methodFilters = new MethodFilter[filters.length];
        for (int i = 0; i < filters.length; i++) {
            methodFilters[i] = new MethodFilter(filters[i].concat(".*"));
        }
        return methodFilters;
    }

}
