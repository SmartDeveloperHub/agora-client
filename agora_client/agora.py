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
    def __init__(self, planner_uri):
        self.__planner = planner_uri

    def get_fragment(self, gp):
        gen, namespaces, plan = self.get_fragment_generator(gp)
        graph = ConjunctiveGraph()
        for (prefix, u) in namespaces:
            graph.bind(prefix, u)

        for tp in gen:
            graph.add(tp)

        return graph

    def __get_gp_plan(self, gp):
        query = urlencode({'gp': gp})
        response = requests.get('{}/plan?'.format(self.__planner) + query, headers={'Accept': 'text/turtle'})
        graph = Graph()
        graph.parse(source=StringIO.StringIO(response.text), format='turtle')
        return graph

    def get_fragment_generator(self, gp, on_load=None, on_seeds=None, on_plink=None, on_link=None, on_type=None,
                               on_type_validation=None, on_tree=None):
        cache_graph = ConjunctiveGraph()
        cache = []
        spaces_dict = {}

        def __decorate_nodes(nodes, space):
            for n in nodes:
                if n not in spaces_dict:
                    spaces_dict[n] = set([])
                spaces_dict[n].add(space)
                pred_nodes = graph.subjects(AGORA.next, n)
                __decorate_nodes(pred_nodes, space)

        def load_uri(graph, uri):
            loaded = False
            if uri not in cache:
                try:
                    cache_graph.get_context(uri).load(uri)
                    cache.append(uri)
                    loaded = True
                except Exception:
                    pass

            triples = list(cache_graph.get_context(uri).triples((None, None, None)))
            for t in triples:
                graph.get_context(uri).add(t)

            if loaded:
                if on_load is not None:
                    on_load(uri, triples)

        graph = self.__get_gp_plan(gp)
        sps = set(graph.subjects(RDF.type, AGORA.SearchSpace))
        subjects_to_clear = {}
        for sp in sps:
            subjects_to_clear[sp] = set([])

        patterns_dict = {}
        patterns = list(graph.subjects(RDF.type, AGORA.TriplePattern))
        for tp in patterns:
            patterns_dict[tp] = {}
            space = list(graph.subjects(AGORA.definedBy, tp)).pop()
            patterns_dict[tp]['space'] = space
            tp_pred = list(graph.objects(tp, predicate=AGORA.predicate)).pop()
            if tp_pred == RDF.type:
                patterns_dict[tp]['type'] = list(graph.objects(tp, predicate=AGORA.object)).pop()
            else:
                patterns_dict[tp]['property'] = tp_pred
                tp_obj = list(graph.objects(tp, predicate=AGORA.object)).pop()
                if (tp_obj, RDF.type, AGORA.Literal) in graph:
                    patterns_dict[tp]['filter'] = list(graph.objects(tp_obj, AGORA.value)).pop()

            nodes = graph.subjects(AGORA.byPattern, tp)
            __decorate_nodes(nodes, space)

        def follow_tree(node, tree_graph, objs=None):
            def order_func(x):
                p_node = list(graph.objects(subject=x, predicate=AGORA.byPattern))
                return len(p_node) and 'filter' in patterns_dict[p_node.pop()]

            nxt = list(graph.objects(node, AGORA.next))
            nxt = sorted(nxt, key=lambda x: order_func(x),
                         reverse=True)

            for n in nxt:
                pattern_node = None
                try:
                    pattern_node = list(graph.objects(subject=n, predicate=AGORA.byPattern)).pop()
                    pattern_link = patterns_dict[pattern_node]['property']
                except (IndexError, KeyError):
                    pattern_link = None

                try:
                    link = list(graph.objects(subject=n, predicate=AGORA.onProperty)).pop()
                    search_spaces = spaces_dict[n]
                except IndexError:
                    link = None
                    search_spaces = []

                obj_filter = None
                obj_type = None
                if pattern_node is not None:
                    obj_filter = patterns_dict[pattern_node].get('filter', None)
                    obj_type = patterns_dict[pattern_node].get('type', None)
                    pattern_space = patterns_dict[pattern_node]['space']

                cp_objs = {}

                if pattern_link is not None:
                    cp_objs[pattern_space] = set([])
                    cp_prev_objs = filter(lambda x: x not in subjects_to_clear[pattern_space],
                                          objs[pattern_space])
                    if on_plink is not None:
                        on_plink(pattern_link, cp_prev_objs, pattern_space)

                    for obj_s in cp_prev_objs:
                        load_uri(tree_graph, obj_s)
                        link_objs = list(tree_graph.objects(subject=obj_s, predicate=pattern_link))
                        for lo in link_objs:
                            if obj_filter is None or str(lo) == str(obj_filter):
                                cp_objs[pattern_space].add(lo)
                                yield (obj_s, pattern_link, lo)
                            else:
                                subjects_to_clear[pattern_space].add(obj_s)

                if link is not None:
                    for sp in search_spaces:
                        if sp not in cp_objs:
                            cp_objs[sp] = set([])
                        cp_prev_objs = filter(lambda x: x not in subjects_to_clear[sp] or pattern_link is None,
                                              objs[sp])
                        if on_link is not None:
                            on_link(link, cp_prev_objs, sp)
                        for obj_s in cp_prev_objs:
                            load_uri(tree_graph, obj_s)
                            link_objs = list(tree_graph.objects(subject=obj_s, predicate=link))
                            for lo in link_objs:
                                cp_objs[sp].add(lo)

                if obj_type is not None:
                    cp_prev_objs = filter(lambda x: x not in subjects_to_clear[pattern_space], objs[pattern_space])
                    if pattern_space not in cp_objs:
                        cp_objs[pattern_space] = set([])
                    if on_type is not None:
                            on_type(obj_type, cp_prev_objs, pattern_space)
                    for obj_s in cp_prev_objs:
                        load_uri(tree_graph, obj_s)
                        link_objs = list(tree_graph.objects(subject=obj_s, predicate=link))
                        for obj in link_objs:
                            yield (obj, RDF.type, obj_type)

                if len(filter(lambda x: len(cp_objs[x]), cp_objs.keys())):
                    for yt in follow_tree(n, tree_graph, cp_objs):
                        yield yt

        def filter_triples():
            def order_func(x):
                length = list(graph.objects(subject=x, predicate=AGORA.length)).pop()
                return length

            trees = graph.subjects(RDF.type, AGORA.SearchTree)
            trees = sorted(trees, key=lambda x: order_func(x))

            for tree in trees:
                if on_tree is not None:
                    on_tree(tree)
                type_triples = set([])
                tree_graph = ConjunctiveGraph()
                seeds = list(graph.objects(tree, AGORA.hasSeed))
                if on_seeds is not None:
                    on_seeds(seeds)

                root_pattern = list(graph.objects(tree, AGORA.byPattern))
                if len(root_pattern):
                    pattern_node = list(graph.objects(subject=tree, predicate=AGORA.byPattern)).pop()
                    seed_types = list(graph.objects(subject=pattern_node, predicate=AGORA.patternType))

                    for st in seed_types:
                        for s in seeds:
                            type_triples.add((s, RDF.type, st))

                nxt = list(graph.objects(tree, AGORA.next))
                if len(nxt):
                    objs = {}
                    for sp in sps:
                        objs[sp] = set(seeds)

                    for (s, p, o) in follow_tree(tree, tree_graph, objs.copy()):
                        if p == RDF.type:
                            type_triples.add((s, p, o))
                        else:
                            yield (s, p, o)

                for (s, p, o) in type_triples:
                    clear = False
                    for stc in subjects_to_clear:
                        if s in subjects_to_clear[stc]:
                            clear = True
                            break
                    if not clear:
                        if on_type_validation is not None:
                            on_type_validation((s, p, o))
                        yield (s, p, o)

        return filter_triples(), graph.namespaces(), graph

