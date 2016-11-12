/*
 * Copyright (c) 2009, 2016, Oracle and/or its affiliates. All rights reserved.
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
package com.oracle.graal.nodes.java;

import com.oracle.graal.compiler.common.type.AbstractPointerStamp;
import com.oracle.graal.compiler.common.type.ObjectStamp;
import com.oracle.graal.compiler.common.type.StampFactory;
import com.oracle.graal.compiler.common.type.TypeReference;
import com.oracle.graal.graph.NodeClass;
import com.oracle.graal.graph.spi.CanonicalizerTool;
import com.oracle.graal.nodeinfo.NodeInfo;
import com.oracle.graal.nodes.LogicNode;
import com.oracle.graal.nodes.ValueNode;
import com.oracle.graal.nodes.spi.Lowerable;
import com.oracle.graal.nodes.spi.LoweringTool;

/**
 * The {@code LoweredInstanceOfNode} represents an instanceof test on a non-null object and without
 * profile.
 */
@NodeInfo
public final class LoweredInstanceOfNode extends AbstractInstanceOfNode implements Lowerable {
    public static final NodeClass<LoweredInstanceOfNode> TYPE = NodeClass.create(LoweredInstanceOfNode.class);

    @Input protected ValueNode hub;

    protected LoweredInstanceOfNode(ObjectStamp checkedStamp, ValueNode object, ValueNode hub) {
        super(TYPE, checkedStamp, object);
        this.hub = hub;
        assert checkedStamp != null;
    }

    public static LogicNode create(TypeReference type, ValueNode object, ValueNode hub) {
        assert ((ObjectStamp) object.stamp()).nonNull();
        assert ((AbstractPointerStamp) hub.stamp()).nonNull();
        ObjectStamp checkedStamp = StampFactory.objectNonNull(type);
        LogicNode synonym = findSynonym(checkedStamp, object);
        if (synonym != null) {
            return synonym;
        } else {
            return new LoweredInstanceOfNode(checkedStamp, object, hub);
        }
    }

    @Override
    public void lower(LoweringTool tool) {
        tool.getLowerer().lower(this, tool);
    }

    @Override
    public ValueNode canonical(CanonicalizerTool tool, ValueNode forValue) {
        LogicNode synonym = findSynonym(checkedStamp, forValue);
        if (synonym != null) {
            return synonym;
        } else {
            return this;
        }
    }

    public ValueNode getHub() {
        return hub;
    }
}
