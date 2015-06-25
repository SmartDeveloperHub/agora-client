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

from rdflib.plugins.parsers.notation3 import BadSyntax
from concurrent.futures.thread import ThreadPoolExecutor
import StringIO
from urllib import urlencode
import requests
from rdflib import ConjunctiveGraph, Graph, RDF
from rdflib.namespace import Namespace
from concurrent.futures import wait, ALL_COMPLETED
from blessings import Terminal

term = Terminal()

AGORA = Namespace('http://agora.org#')


def chunks(l, n):
    """Yield successive n-sized chunks from l."""
    for i in xrange(0, len(l), n):
        yield l[i:i + n]


def __extend_uri(prefixes, short):
    """
    Extend a prefixed uri with the help of a specific dictionary of prefixes
    :param prefixes: Dictionary of prefixes
    :param short: Prefixed uri to be extended
    :return:
    """
    for prefix in prefixes:
        if short.startswith(prefix):
            return short.replace(prefix + ':', prefixes[prefix])
    return short


class Agora(object):
    """
    Wrapper class for the FragmentCollector
    """

    def __init__(self, host):
        self.__host = host

    def get_fragment(self, gp):
        """
        Return a complete fragment for a given gp.
        :param gp: A graph pattern
        :return:
        """
        collector = FragmentCollector(self.__host, gp)
        return collector.get_fragment()

    def get_fragment_generator(self, gp, **kwargs):
        """
        Return a fragment generator for a given gp.
        :param gp:
        :param kwargs:
        :return:
        """
        collector = FragmentCollector(self.__host, gp)
        return collector.get_fragment_generator(**kwargs)


class PlanExecutor(object):
    def __init__(self, plan):
        self.__plan_graph = plan
        self.__cache_graph = ConjunctiveGraph()
        self.__uri_cache = []
        self.__node_spaces = {}
        self.__node_patterns = {}
        self.__spaces = None
        self.__patterns = {}
        self.__subjects_to_ignore = {}

        # Request a search plan on initialization and extract patterns and spaces
        self.__extract_patterns_and_spaces()

    def __extract_patterns_and_spaces(self):
        """
        Analyses the search plan graph in order to build the required data structures from patterns
        and spaces.
        :return:
        """

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

        # Extract all search spaces in the plan and build a dictionary of subjects-to-ignore per each of them.
        # Ignored subjects are those that won't be dereferenced due to a explicit graph pattern (object) filter,
        # e.g. ?s doap:name "jenkins" -> All ?s that don't match the filter will be ignored.
        self.__spaces = set(self.__plan_graph.subjects(RDF.type, AGORA.SearchSpace))
        self.__subjects_to_ignore = dict([(sp, set([])) for sp in self.__spaces])

        patterns = list(self.__plan_graph.subjects(RDF.type, AGORA.TriplePattern))
        for tp in patterns:
            # A triple pattern belongs to a UNIQUE search space
            space = list(self.__plan_graph.subjects(AGORA.definedBy, tp)).pop()
            self.__patterns[tp] = {'space': space}

            # Depending on the format of each triple pattern (either '?s a Concept' or '?s prop O'),
            # it is required to extract different properties.
            tp_pred = list(self.__plan_graph.objects(tp, predicate=AGORA.predicate)).pop()

            if tp_pred == RDF.type:  # ?s a Concept
                self.__patterns[tp]['type'] = list(self.__plan_graph.objects(tp, predicate=AGORA.object)).pop()
                try:
                    check_type = list(self.__plan_graph.objects(tp, predicate=AGORA.checkType)).pop().toPython()
                except IndexError:
                    check_type = True
                self.__patterns[tp]['check'] = check_type
            else:  # ?s prop O
                self.__patterns[tp]['property'] = tp_pred
                tp_obj = list(self.__plan_graph.objects(tp, predicate=AGORA.object)).pop()
                if (tp_obj, RDF.type, AGORA.Literal) in self.__plan_graph:  # In case O is a Literal
                    self.__patterns[tp]['filter'] = list(self.__plan_graph.objects(tp_obj, AGORA.value)).pop()

            # Get all pattern nodes (those that have a byPattern properties) of the search plan and search backwards
            # in order to set the scope of each search space.
            nodes = list(self.__plan_graph.subjects(AGORA.byPattern, tp))
            for n in nodes:
                if n not in self.__node_patterns:
                    self.__node_patterns[n] = set([])
                self.__node_patterns[n].add(tp)
            __decorate_nodes(nodes, space)

    def get_fragment(self):
        """
        Return a complete fragment.
        :param gp:
        :return:
        """
        gen, namespaces, plan = self.get_fragment_generator()
        graph = ConjunctiveGraph()
        [graph.bind(prefix, u) for (prefix, u) in namespaces]
        [graph.add((s, p, o)) for (_, s, p, o) in gen]

        return graph

    def get_fragment_generator(self, on_load=None, on_seeds=None, on_plink=None, on_link=None, on_type=None,
                               on_type_validation=None, on_tree=None):
        """
        Create a fragment generator that executes the search plan.
        :param on_load: Function to be called just after a new URI is dereferenced
        :param on_seeds: Function to be called just after a seed of a tree is identified
        :param on_plink: Function to be called when a pattern link is reached
        :param on_link: Function to be called when following a property that is not of a pattern
        :param on_type: Function to be called when search for a type triple
        :param on_type_validation: Function to be called just after a type is validated
        :param on_tree: Function to be called just before a tree is going to be explored
        :return:
        """

        def __dereference_uri(tg, uri):
            """
            Load in a tree graph the set of triples contained in uri, trying to not deference the same uri
            more than once in the context of a search plan execution
            :param tg: The graph to be loaded with all the triples obtained from uri
            :param uri: A resource uri to be dereferenced
            :return:
            """
            loaded = False
            if uri not in self.__uri_cache:
                self.__uri_cache.append(uri)
                try:
                    self.__cache_graph.get_context(uri).load(uri, format='turtle')
                    loaded = True
                except Exception:
                    pass

            # Copy the triples contained in the cache graph to the tree graph given as a parameter
            triples = list(self.__cache_graph.get_context(uri).triples((None, None, None)))
            [tg.get_context(uri).add(t) for t in triples]

            if loaded and on_load is not None:
                on_load(uri, triples)

        def __process_seeds(f, seeds, *args):
            futures = []
            with ThreadPoolExecutor(min(len(seeds), 20)) as th_pool:
                for seed in seeds:
                    futures.append(th_pool.submit(f, seed, *args))
                wait(futures, timeout=None, return_when=ALL_COMPLETED)
                th_pool.shutdown()
            return [f.result() for f in futures if f.done()]

        def __process_link_seed(seed, tree_graph, link, next_seeds, sp):
            __dereference_uri(tree_graph, seed)
            seed_pattern_objects = list(tree_graph.objects(subject=seed, predicate=link))
            for seed_object in seed_pattern_objects:
                next_seeds[sp].add(seed_object)

        def __process_pattern_link_seed(seed, tree_graph, pattern_link):
            __dereference_uri(tree_graph, seed)
            seed_pattern_objects = list(tree_graph.objects(subject=seed, predicate=pattern_link))
            return seed, seed_pattern_objects

        def __follow_node(node, tree_graph, node_seeds):
            """
            Recursively search for relevant triples following the current node and all its successors
            :param node: Tree node to be followed
            :param tree_graph:
            :param node_seeds: Set of collected seeds for the current node
            :return:
            """

            def node_has_filter(x):
                """
                Check if a node is a pattern node and has an object filter
                """
                p_node = list(self.__plan_graph.objects(subject=x, predicate=AGORA.byPattern))
                return len(p_node) and 'filter' in self.__patterns[p_node.pop()]

            # Get the sorted list of current node's successors
            nxt = sorted(list(self.__plan_graph.objects(node, AGORA.next)),
                         key=lambda x: node_has_filter(x), reverse=True)

            # Per each successor...
            for n in nxt:
                # Get all its search spaces and pattern nodes (if any)
                search_spaces = self.__node_spaces[n]
                node_patterns = self.__node_patterns.get(n, [])

                # In case the node is not a leaf, 'onProperty' tells which is the next link to follow
                try:
                    link = list(self.__plan_graph.objects(subject=n, predicate=AGORA.onProperty)).pop()
                except IndexError:
                    link = None

                next_seeds = dict([(sp, set([])) for sp in search_spaces])

                # If the current node is a pattern node, it must search for triples to yield
                for pattern in node_patterns:
                    pattern_space = self.__patterns[pattern].get('space', None)
                    pattern_link = self.__patterns[pattern].get('property', None)
                    filtered_seeds = filter(lambda x: x not in self.__subjects_to_ignore[pattern_space],
                                            node_seeds[pattern_space])

                    # If pattern is of type '?s prop O'...
                    if pattern_link is not None:
                        obj_filter = self.__patterns[pattern].get('filter', None)
                        if on_plink is not None:
                            on_plink(pattern_link, filtered_seeds, pattern_space)

                        for chunk in chunks(filtered_seeds, min(20, len(filtered_seeds))):
                            result = __process_seeds(__process_pattern_link_seed, chunk,
                                                     tree_graph, pattern_link)

                            for seed, seed_pattern_objects in result:
                                for seed_object in seed_pattern_objects:
                                    if obj_filter is None or str(seed_object) == str(obj_filter):
                                        yield (pattern, seed, pattern_link, seed_object)
                                    else:
                                        self.__subjects_to_ignore[pattern_space].add(seed)

                    # If pattern is of type '?s a Concept'...
                    obj_type = self.__patterns[pattern].get('type', None)
                    if obj_type is not None:
                        check_type = self.__patterns[pattern].get('check', False)
                        if on_type is not None:
                            on_type(obj_type, filtered_seeds, pattern_space)

                        for seed in filtered_seeds:
                            __dereference_uri(tree_graph, seed)
                            # 'link' should be None!
                            seed_pattern_objects = list(tree_graph.objects(subject=seed, predicate=link))
                            for seed_object in seed_pattern_objects:
                                type_triple = (pattern, seed_object, RDF.type, obj_type)
                                # In some cases, it is necessary to verify the type of the seed
                                if check_type:
                                    __dereference_uri(tree_graph, seed_object)
                                    types = list(tree_graph.objects(subject=seed_object, predicate=RDF.type))
                                    if obj_type in types:
                                        yield type_triple
                                else:
                                    yield type_triple

                # If the current node is not a leaf... go on finding seeds for the successors
                if link is not None:
                    for sp in search_spaces:
                        filtered_seeds = filter(lambda x: x not in self.__subjects_to_ignore[sp], node_seeds[sp])
                        if on_link is not None:
                            on_link(link, filtered_seeds, sp)
                        __process_seeds(__process_link_seed, filtered_seeds, tree_graph, link, next_seeds, sp)

                if filter(lambda x: len(next_seeds[x]), next_seeds.keys()):
                    for yt in __follow_node(n, tree_graph, next_seeds):
                        yield yt

        def get_fragment_triples():
            """
            Iterate over all search trees and yield relevant triples
            :return:
            """

            def get_tree_length(x):
                """
                Return the value of the Agora length property in the given tree node
                :param x:
                :return:
                """
                length = list(self.__plan_graph.objects(subject=x, predicate=AGORA.length)).pop()
                return length

            # Get all search trees contained in the search plan and sort them by length. A shorter tree is going
            # to be explored first.
            trees = self.__plan_graph.subjects(RDF.type, AGORA.SearchTree)
            trees = sorted(trees, key=lambda x: get_tree_length(x))

            for tree in trees:
                if on_tree is not None:
                    on_tree(tree)

                # Prepare an dedicated graph for the current tree and a set of type triples (?s a Concept)
                # to be evaluated retrospectively
                tree_graph = ConjunctiveGraph()
                type_triples = set([])

                # Get all seeds of the current tree
                seeds = list(self.__plan_graph.objects(tree, AGORA.hasSeed))
                if on_seeds is not None:
                    on_seeds(seeds)

                # Check if the tree root is a pattern node and in that case, adds a type triple to the
                # respective set
                root_pattern = list(self.__plan_graph.objects(tree, AGORA.byPattern))
                if len(root_pattern):
                    pattern_node = list(self.__plan_graph.objects(subject=tree, predicate=AGORA.byPattern)).pop()
                    seed_type = self.__patterns[pattern_node].get('type', None)
                    [type_triples.add((s, seed_type)) for s in seeds]

                # Get the children of the root node and follow them recursively
                nxt = list(self.__plan_graph.objects(tree, AGORA.next))
                if len(nxt):
                    # Prepare the list of seeds to start the exploration with, taking into account all search spaces
                    # that were defined
                    s_seeds = set(seeds)
                    root_seeds = dict([(sp, s_seeds) for sp in self.__spaces])

                    # Directly yield all found triples except for type ones, which will be evaluated retrospectively
                    for (t, s, p, o) in __follow_node(tree, tree_graph, root_seeds):
                        if p == RDF.type:
                            type_triples.add((t, s, o))
                        else:
                            yield (t, s, p, o)

                # All type triples that are of subjects to ignore won't be returned (this has to be done this way
                # because of generators nature)
                all_ignores = set.intersection(*self.__subjects_to_ignore.values())
                valid_type_triples = [(t, s, o) for (t, s, o) in type_triples if s not in all_ignores]
                for (t, s, o) in valid_type_triples:
                    if on_type_validation is not None:
                        on_type_validation((t, s, RDF.type, o))
                    yield (t, s, RDF.type, o)

        return get_fragment_triples(), self.__plan_graph.namespaces(), self.__plan_graph


class FragmentCollector(object):
    """ Class for interacting with the Agora planner and executing the plans for a certain graph pattern.
    """

    def __init__(self, planner_uri, gp):
        self.__planner = planner_uri
        self.__graph_pattern = gp

        # Request a search plan on initialization and extract patterns and spaces
        plan_graph = self.__get_gp_plan(self.__graph_pattern)
        self.__plan_executor = PlanExecutor(plan_graph)

    def __get_gp_plan(self, gp):
        """
        Request the planner a search plan for a given gp and returns the plan as a graph.
        :param gp:
        :return:
        """
        query = urlencode({'gp': gp})
        response = requests.get('{}/plan?'.format(self.__planner) + query, headers={'Accept': 'text/turtle'})
        graph = Graph()
        try:
            graph.parse(source=StringIO.StringIO(response.text), format='turtle')
        except BadSyntax:
            pass
        return graph

    def get_fragment(self):
        return self.__plan_executor.get_fragment()

    def get_fragment_generator(self, **kwargs):
        return self.__plan_executor.get_fragment_generator(**kwargs)
