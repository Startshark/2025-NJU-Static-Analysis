/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */
package pascal.taie.analysis.pta.core.cs.selector;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of 2-object sensitivity.
 */
public class _2ObjSelector implements ContextSelector {

    @Override
    public Context getEmptyContext() {
        return ListContext.make();
    }

    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        // TODO - finish me
        Context ctx = callSite.getContext();
        int size = ctx.getLength();
        if (size == 0) {
            return getEmptyContext();
        }
        if (size == 1) {
            return ListContext.make(ctx.getElementAt(0));
        }
        return ListContext.make(ctx.getElementAt(size - 2), ctx.getElementAt(size - 1));
    }

    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        // TODO - finish me
        Context recvCtx = recv.getContext();
        Obj recvObj = recv.getObject();
        if (recvCtx.getLength() > 0) {
            return ListContext.make(recvCtx.getElementAt(recvCtx.getLength() - 1), recvObj);
        }
        return ListContext.make(recvObj);
    }

    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        // TODO - finish me
        Context mCtx = method.getContext();
        if (mCtx.getLength() > 0) {
            return ListContext.make(mCtx.getElementAt(mCtx.getLength() - 1));
        }
        return getEmptyContext();
    }
}
