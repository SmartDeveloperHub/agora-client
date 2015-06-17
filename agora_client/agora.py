"""
#-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=#
  This file is part of the Smart Developer Hub Project:
    http://www.smartdeveloperhub.org

  Center for Open Middleware
        http://www.centeropenmiddleware.com/
#-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=#
  Copyright (C) 2015 Center for Open Middleware.
#-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=#
  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

            http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
#-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=#
"""

__author__ = 'Fernando Serena'

import StringIO
from urllib import urlencode
import requests
from rdflib import ConjunctiveGraph, Graph, RDF
from rdflib.namespace import Namespace

from blessings import Terminal

term = Terminal()

AGORA = Namespace('http://agora.org#')


def __extend_uri(prefixes, short):
    for prefix in prefixes:
        if short.startswith(prefix):
            return short.replace(prefix + ':', prefixes[prefix])
    return short


class Agora(object):
    def __init__(self, host):
        self.__host = host

    def get_fragment(self, gp):
        collector = FragmentCollector(self.__host, gp)
        return collector.get_fragment()

    def get_fragment_generator(self, gp, **kwargs):
        collector = FragmentCollector(self.__host, gp)
        return collector.get_fragment_generator(**kwargs)


class FragmentCollector(object):
    """ Class for interacting with the Agora planner and executing the plans for a certain graph pattern
    """

    def __init__(self, planner_uri, gp):
        self.__planner = planner_uri
        self.__cache_graph = ConjunctiveGraph()
        self.__uri_cache = []
        self.__graph_pattern = gp
        self.__plan_graph = self.__get_gp_plan(self.__graph_pattern)
        self.__node_spaces = {}
        self.__spaces = None
        self.__patterns = {}
        self.__subjects_to_clear = {}

        self.__extract_patterns_and_spaces()

    def __get_gp_plan(self, gp):
        """
        Request the planner a search plan for a given gp and returns the plan as a graph
        :param gp:
        :return:
        """
        query = urlencode({'gp': gp})
        response = requests.get('{}/plan?'.format(self.__planner) + query, headers={'Accept': 'text/turtle'})
        graph = Graph()
        graph.parse(source=StringIO.StringIO(response.text), format='turtle')
        return graph

    def __extract_patterns_and_spaces(self):
        def __decorate_nodes(nodes, space):
            """
            Performs a backward search from a list of pattern nodes and assigns a set of search spaces
            to all encountered nodes.
            :param nodes: List of pattern nodes that belongs to a search space
            :param space: List of  search space id
            :return:
            """
            for n in nodes:
                if n not in self.__node_spaces:
                    self.__node_spaces[n] = set([])
                self.__node_spaces[n].add(space)
                pred_nodes = self.__plan_graph.subjects(AGORA.next, n)
                __decorate_nodes(pred_nodes, space)

        self.__spaces = set(self.__plan_graph.subjects(RDF.type, AGORA.SearchSpace))
        for sp in self.__spaces:
            self.__subjects_to_clear[sp] = set([])

        patterns = list(self.__plan_graph.subjects(RDF.type, AGORA.TriplePattern))
        for tp in patterns:
            self.__patterns[tp] = {'spaces': set([])}
            space = list(self.__plan_graph.subjects(AGORA.definedBy, tp)).pop()
            self.__patterns[tp]['space'] = space
            tp_pred = list(self.__plan_graph.objects(tp, predicate=AGORA.predicate)).pop()
            if tp_pred == RDF.type:
                self.__patterns[tp]['type'] = list(self.__plan_graph.objects(tp, predicate=AGORA.object)).pop()
                try:
                    check_type = list(self.__plan_graph.objects(tp, predicate=AGORA.checkType)).pop().toPython()
                except IndexError:
                    check_type = False
                self.__patterns[tp]['check'] = check_type
            else:
                self.__patterns[tp]['property'] = tp_pred
                tp_obj = list(self.__plan_graph.objects(tp, predicate=AGORA.object)).pop()
                if (tp_obj, RDF.type, AGORA.Literal) in self.__plan_graph:
                    self.__patterns[tp]['filter'] = list(self.__plan_graph.objects(tp_obj, AGORA.value)).pop()

            nodes = self.__plan_graph.subjects(AGORA.byPattern, tp)
            __decorate_nodes(nodes, space)

    def get_fragment(self):
        """
        Return a complete fragment for a given gp
        :param gp:
        :return:
        """
        gen, namespaces, plan = self.get_fragment_generator()
        graph = ConjunctiveGraph()
        [graph.bind(prefix, u) for (prefix, u) in namespaces]
        [graph.add(tp) for tp in gen]

        return graph

    def get_fragment_generator(self, on_load=None, on_seeds=None, on_plink=None, on_link=None, on_type=None,
                               on_type_validation=None, on_tree=None):

        def __dereference_uri(tg, uri):
            """
            Load in a tree graph the set of triples contained in uri, trying to not deference the same uri more than once
            in the context of a search  plan execution
            :param graph: The graph to be loaded with all the triples obtained from uri
            :param uri: A resource uri to be dereferenced
            :return:
            """
            loaded = False
            if uri not in self.__uri_cache:
                try:
                    self.__cache_graph.get_context(uri).load(uri, format='turtle')
                    self.__uri_cache.append(uri)
                    loaded = True
                except Exception:
                    pass

            triples = list(self.__cache_graph.get_context(uri).triples((None, None, None)))
            [tg.get_context(uri).add(t) for t in triples]

            if loaded:
                if on_load is not None:
                    on_load(uri, triples)

        def __follow_tree(node, tree_graph, objs=None):
            def order_func(x):
                p_node = list(self.__plan_graph.objects(subject=x, predicate=AGORA.byPattern))
                return len(p_node) and 'filter' in self.__patterns[p_node.pop()]

            nxt = list(self.__plan_graph.objects(node, AGORA.next))
            nxt = sorted(nxt, key=lambda x: order_func(x),
                         reverse=True)

            for n in nxt:
                search_spaces = self.__node_spaces[n]
                pattern_nodes = list(self.__plan_graph.objects(subject=n, predicate=AGORA.byPattern))

                try:
                    link = list(self.__plan_graph.objects(subject=n, predicate=AGORA.onProperty)).pop()
                except IndexError:
                    link = None

                cp_objs = {}

                for pattern_node in pattern_nodes:
                    try:
                        obj_filter = self.__patterns[pattern_node].get('filter', None)
                        obj_type = self.__patterns[pattern_node].get('type', None)
                        pattern_space = self.__patterns[pattern_node].get('space', None)
                        check_type = self.__patterns[pattern_node].get('check', False)
                        pattern_link = self.__patterns[pattern_node].get('property', None)
                    except IndexError:
                        pattern_node = None
                        pattern_link = None
                        pattern_space = None
                        obj_filter = None
                        obj_type = None
                        check_type = False

                    if pattern_link is not None:
                        cp_objs[pattern_space] = set([])
                        cp_prev_objs = filter(lambda x: x not in self.__subjects_to_clear[pattern_space],
                                              objs[pattern_space])
                        if on_plink is not None:
                            on_plink(pattern_link, cp_prev_objs, pattern_space)

                        for obj_s in cp_prev_objs:
                            __dereference_uri(tree_graph, obj_s)
                            link_objs = list(tree_graph.objects(subject=obj_s, predicate=pattern_link))
                            for lo in link_objs:
                                if obj_filter is None or str(lo) == str(obj_filter):
                                    cp_objs[pattern_space].add(lo)
                                    yield (obj_s, pattern_link, lo)
                                else:
                                    self.__subjects_to_clear[pattern_space].add(obj_s)

                    if obj_type is not None:
                        cp_prev_objs = filter(lambda x: x not in self.__subjects_to_clear[pattern_space],
                                              objs[pattern_space])
                        if pattern_space not in cp_objs:
                            cp_objs[pattern_space] = set([])
                        if on_type is not None:
                            on_type(obj_type, cp_prev_objs, pattern_space)
                        for obj_s in cp_prev_objs:
                            __dereference_uri(tree_graph, obj_s)
                            link_objs = list(tree_graph.objects(subject=obj_s, predicate=link))
                            for obj in link_objs:
                                type_triple = (obj, RDF.type, obj_type)
                                if check_type:
                                    __dereference_uri(tree_graph, obj)
                                    types = list(tree_graph.objects(subject=obj, predicate=RDF.type))
                                    if obj_type in types:
                                        yield type_triple
                                else:
                                    yield (obj, RDF.type, obj_type)

                if link is not None:
                    for sp in search_spaces:
                        if sp not in cp_objs:
                            cp_objs[sp] = set([])
                        cp_prev_objs = filter(lambda x: x not in self.__subjects_to_clear[sp], objs[sp])
                        if on_link is not None:
                            on_link(link, cp_prev_objs, sp)
                        for obj_s in cp_prev_objs:
                            __dereference_uri(tree_graph, obj_s)
                            link_objs = list(tree_graph.objects(subject=obj_s, predicate=link))
                            for lo in link_objs:
                                cp_objs[sp].add(lo)

                if filter(lambda x: len(cp_objs[x]), cp_objs.keys()):
                    for yt in __follow_tree(n, tree_graph, cp_objs):
                        yield yt

        def filter_triples():
            def order_func(x):
                length = list(self.__plan_graph.objects(subject=x, predicate=AGORA.length)).pop()
                return length

            trees = self.__plan_graph.subjects(RDF.type, AGORA.SearchTree)
            trees = sorted(trees, key=lambda x: order_func(x))

            for tree in trees:
                if on_tree is not None:
                    on_tree(tree)
                type_triples = set([])
                tree_graph = ConjunctiveGraph()
                seeds = list(self.__plan_graph.objects(tree, AGORA.hasSeed))
                if on_seeds is not None:
                    on_seeds(seeds)

                root_pattern = list(self.__plan_graph.objects(tree, AGORA.byPattern))
                if len(root_pattern):
                    pattern_node = list(self.__plan_graph.objects(subject=tree, predicate=AGORA.byPattern)).pop()
                    seed_type = self.__patterns[pattern_node].get('type', None)
                    for s in seeds:
                        type_triples.add((s, RDF.type, seed_type))

                nxt = list(self.__plan_graph.objects(tree, AGORA.next))
                if len(nxt):
                    objs = {}
                    for sp in self.__spaces:
                        objs[sp] = set(seeds)

                    for (s, p, o) in __follow_tree(tree, tree_graph, objs.copy()):
                        if p == RDF.type:
                            type_triples.add((s, p, o))
                        else:
                            yield (s, p, o)

                for (s, p, o) in type_triples:
                    clear = False
                    for stc in self.__subjects_to_clear:
                        if s in self.__subjects_to_clear[stc]:
                            clear = True
                            break
                    if not clear:
                        if on_type_validation is not None:
                            on_type_validation((s, p, o))
                        yield (s, p, o)

        return filter_triples(), self.__plan_graph.namespaces(), self.__plan_graph
