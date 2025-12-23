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
package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Stream;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        // 使用显式的可达方法集合，避免重复检查callGraph.contains
        Set<JMethod> reachableMethods = new HashSet<>();
        Deque<JMethod> worklist = new ArrayDeque<>();

        worklist.addLast(entry);
        reachableMethods.add(entry);

        // 工作列表驱动的可达性分析
        while (!worklist.isEmpty()) {
            JMethod currentMethod = worklist.pollFirst();
            callGraph.addReachableMethod(currentMethod);

            // 分析当前方法的所有调用点
            callGraph.callSitesIn(currentMethod).forEach(invoke -> {
                Set<JMethod> possibleTargets = resolve(invoke);
                for (JMethod target : possibleTargets) {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, target));
                    // 只有首次遇到的方法才加入工作列表
                    if (reachableMethods.add(target)) {
                        worklist.addLast(target);
                    }
                }
            });
        }
        return callGraph;
    }

    private void enqueue(JClass type, Queue<JClass> work, Set<JClass> visited) {
        for (JClass cls : hierarchy.getDirectSubclassesOf(type)) {
            if (visited.add(cls)) {
                work.add(cls);
            }
        }
        for (JClass iface : hierarchy.getDirectSubinterfacesOf(type)) {
            if (visited.add(iface)) {
                work.add(iface);
            }
        }
        for (JClass impl : hierarchy.getDirectImplementorsOf(type)) {
            if (visited.add(impl)) {
                work.add(impl);
            }
        }
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> targets = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        JClass declaringClass = methodRef.getDeclaringClass();
        Subsignature subsig = methodRef.getSubsignature();

        if (callSite.isStatic()) {
            JMethod staticMethod = declaringClass.getDeclaredMethod(subsig);
            if (staticMethod != null) {
                targets.add(staticMethod);
            }
            return targets;
        }

        // 处理特殊调用（构造器、私有方法、父类方法）
        if (callSite.isSpecial()) {
            JMethod specialMethod = dispatch(declaringClass, subsig);
            if (specialMethod != null) {
                targets.add(specialMethod);
            }
            return targets;
        }

        // 处理虚调用和接口调用：需遍历整个子类型层次结构
        Queue<JClass> typeQueue = new LinkedList<>();
        Set<JClass> processedTypes = new HashSet<>();

        typeQueue.offer(declaringClass);
        processedTypes.add(declaringClass);

        while (!typeQueue.isEmpty()) {
            JClass currentType = typeQueue.poll();
            JMethod resolvedMethod = dispatch(currentType, subsig);

            if (resolvedMethod != null) {
                targets.add(resolvedMethod);
            }

            if (currentType.isInterface()) {
                // 接口需要考虑实现类和子接口
                for (JClass implementor : hierarchy.getDirectImplementorsOf(currentType)) {
                    if (processedTypes.add(implementor)) {
                        typeQueue.offer(implementor);
                    }
                }
                for (JClass subInterface : hierarchy.getDirectSubinterfacesOf(currentType)) {
                    if (processedTypes.add(subInterface)) {
                        typeQueue.offer(subInterface);
                    }
                }
            } else {
                for (JClass subclass : hierarchy.getDirectSubclassesOf(currentType)) {
                    if (processedTypes.add(subclass)) {
                        typeQueue.offer(subclass);
                    }
                }
            }
        }

        return targets;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method can
     * be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if (jclass == null) {
            return null;
        }
        // JMethod method = jclass.lookupMethod(subsignature); Copilot Tab 立大功
        JMethod method = jclass.getDeclaredMethod(subsignature);

        if (method != null && !method.isAbstract()) {
            return method;
        }
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
