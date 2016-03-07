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

import Queue
import StringIO
import logging
import multiprocessing
import traceback
from threading import RLock, Thread, Event
from xml.sax import SAXParseException

import gc
from _bsddb import DBNotFoundError
from datetime import datetime as dt

import requests
from agora.client.namespaces import AGORA
from concurrent.futures import ThreadPoolExecutor
from concurrent.futures import wait
from rdflib import ConjunctiveGraph, RDF, URIRef

pool = ThreadPoolExecutor(max_workers=20)

__author__ = 'Fernando Serena'

log = logging.getLogger('agora.client')

_accept_mimes = {'turtle': 'text/turtle', 'xml': 'application/rdf+xml'}


class StopException(Exception):
    pass


def chunks(l, n):
    """
    Yield successive n-sized chunks from l.
    :param l:
    :param n:
    :return:
    """
    if n:
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


class PlanExecutor(object):
    def __init__(self, plan):
        self.__plan_graph = plan
        self.__fragment = set([])
        self.__uri_cache = {}
        self.__node_spaces = {}
        self.__node_patterns = {}
        self.__spaces = None
        self.__patterns = {}
        self.__subjects_to_ignore = {}
        self.__resource_queue = {}
        self.__resource_lock = RLock()
        self.__completed = False
        self.__last_success_format = None
        self.__last_iteration_ts = dt.now()

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
                    self.__patterns[tp]['filter_object'] = list(self.__plan_graph.objects(tp_obj, AGORA.value)).pop()
                elif isinstance(tp_obj, URIRef):
                    self.__patterns[tp]['filter_object'] = tp_obj

                tp_sub = list(self.__plan_graph.objects(tp, predicate=AGORA.subject)).pop()
                if isinstance(tp_sub, URIRef):
                    self.__patterns[tp]['filter_subject'] = tp_sub

            # Get all pattern nodes (those that have a byPattern properties) of the search plan and search backwards
            # in order to set the scope of each search space.
            nodes = list(self.__plan_graph.subjects(AGORA.byPattern, tp))
            for n in nodes:
                if n not in self.__node_patterns:
                    self.__node_patterns[n] = set([])
                self.__node_patterns[n].add(tp)
            __decorate_nodes(nodes, space)

    def get_fragment(self, **kwargs):
        """
        Return a complete fragment.
        :param gp:
        :return:
        """
        gen, namespaces, plan = self.get_fragment_generator(**kwargs)
        graph = ConjunctiveGraph()
        [graph.bind(prefix, u) for (prefix, u) in namespaces]
        [graph.add((s, p, o)) for (_, s, p, o) in gen]

        return graph

    def get_fragment_generator(self, on_load=None, on_seeds=None, on_plink=None, on_link=None, on_type=None,
                               on_type_validation=None, on_tree=None, workers=None, stop_event=None, queue_wait=None,
                               queue_size=100, provider=None, lazy=True):
        """
        Create a fragment generator that executes the search plan.
        :param on_load: Function to be called just after a new URI is dereferenced
        :param on_seeds: Function to be called just after a seed of a tree is identified
        :param on_plink: Function to be called when a pattern link is reached
        :param on_link: Function to be called when following a property that is not of a pattern
        :param on_type: Function to be called when search for a type triple
        :param on_type_validation: Function to be called just after a type is validated
        :param on_tree: Function to be called just before a tree is going to be explored
        :param provider:
        :param queue_size:
        :param workers:
        :param stop_event:
        :param queue_wait:
        :param lazy:
        :return:
        """

        if workers is None:
            workers = multiprocessing.cpu_count()

        fragment_queue = Queue.Queue(maxsize=queue_size)
        workers_queue = Queue.Queue(maxsize=workers)

        if stop_event is None:
            stop_event = Event()

        def __create_graph(conjunctive=False):
            if provider is None:
                return ConjunctiveGraph()
            else:
                return provider.create(conjunctive)

        def __destroy_graph(g):
            if provider is not None:
                provider.destroy(g)
            else:
                g.remove((None, None, None))
                g.close()

        def __dereference_uri(tg, uri):

            uri = uri.encode('utf-8')

            def treat_resource_content(parse_format):
                lock_acquired = False
                try:
                    log.debug('[Dereference][START] {}'.format(uri))
                    response = requests.get(uri, headers={'Accept': _accept_mimes[parse_format]}, timeout=30)
                except requests.Timeout:
                    log.debug('[Dereference][TIMEOUT][GET] {}'.format(uri))
                    return True
                except UnicodeEncodeError:
                    log.debug('[Dereference][ERROR][ENCODE] {}'.format(uri))
                    return True
                except Exception:
                    log.debug('[Dereference][ERROR][GET] {}'.format(uri))
                    return True

                g = None
                if response.status_code == 200:
                    try:
                        log.debug('Parsing {}-RDF from {}...'.format(parse_format, uri))
                        g = __create_graph()
                        g.parse(source=StringIO.StringIO(response.content), format=parse_format)
                        log.debug('RDF parse of {} done!'.format(uri))
                        log.debug('Trying to acquire lock for {}'.format(uri))
                        self.__resource_lock.acquire()
                        lock_acquired = True
                        tg.get_context(uri).__iadd__(g)
                        log.debug('Trying to release lock for {}'.format(uri))
                        self.__resource_lock.release()
                        log.debug('[Dereference][OK] {}'.format(uri))
                        return True
                    except SyntaxError:
                        log.error('[Dereference][ERROR][PARSE] {}'.format(uri))
                        return False
                    except ValueError:
                        log.debug('[Dereference][ERROR][VAL] {}'.format(uri))
                        return False
                    except (KeyboardInterrupt, SystemError, SystemExit):
                        if lock_acquired:
                            self.__resource_lock.release()
                        raise
                    except DBNotFoundError:
                        log.error('[Dereference][ERROR][DB] {}'.format(uri))
                        return False
                    except SAXParseException:
                        log.error('[Dereference][ERROR][SAX] {}'.format(uri))
                        return False
                    except Exception:
                        log.error('[Dereference][ERROR] {}'.format(uri))
                        return True
                    finally:
                        if g is not None:
                            __destroy_graph(g)

                return True

            """
            Load in a tree graph the set of triples contained in uri, trying to not deference the same uri
            more than once in the context of a search plan execution
            :param tg: The graph to be loaded with all the triples obtained from uri
            :param uri: A resource uri to be dereferenced
            :return:
            """
            loaded = False
            self.__resource_lock.acquire()
            if tg in self.__resource_queue and uri not in self.__resource_queue[tg]:
                self.__resource_queue[tg].append(uri)
                if len(self.__resource_queue[tg]) > workers * 2:  # TODO: Adjust this capacity properly
                    tg.remove_context(tg.get_context(self.__resource_queue[tg].pop(0)))
                self.__resource_lock.release()
                for fmt in sorted(_accept_mimes.keys(), key=lambda x: x != self.__last_success_format):
                    loaded = treat_resource_content(fmt)
                    if loaded:
                        self.__last_success_format = fmt
                        break
            else:
                try:
                    self.__resource_lock.release()
                except RuntimeError:  # Raises when trying to release the lock but was not acquired
                    pass

            if loaded and on_load is not None:
                triples = list(tg.get_context(uri).triples((None, None, None)))
                on_load(uri, triples)

        def __process_link_seed(seed, tree_graph, link, next_seeds):
            __check_stop()
            try:
                __dereference_uri(tree_graph, seed)
            except:
                pass
            seed_pattern_objects = tree_graph.objects(subject=seed, predicate=link)
            next_seeds.update(seed_pattern_objects)

        def __process_pattern_link_seed(seed, tree_graph, pattern_link):
            __check_stop()
            try:
                __dereference_uri(tree_graph, seed)
            except:
                pass
            seed_pattern_objects = tree_graph.objects(subject=seed, predicate=pattern_link)
            return seed_pattern_objects

        def __check_stop():
            if stop_event.isSet():
                with self.__resource_lock:
                    self.__fragment.clear()
                    for tg in self.__resource_queue.keys():
                        try:
                            tg.remove((None, None, None))
                            tg.store.close()
                        except KeyError:
                            pass
                        tg.close()
                        __destroy_graph(tg)
                    self.__plan_graph = None
                    self.__uri_cache = None
                    self.__node_spaces = None
                    self.__node_patterns = None
                    self.__spaces = None
                    self.__patterns = None
                    self.__subjects_to_ignore.clear()
                    self.__resource_queue.clear()
                gc.collect()
                raise StopException()

        def __put_triple_in_queue(quad):
            if (dt.now() - self.__last_iteration_ts).total_seconds() > 100:
                log.info('Aborted fragment collection!')
                stop_event.set()
            fragment_queue.put(quad, timeout=queue_wait)

        def __follow_node(node, tree_graph, seed_space, seed):
            """
            Recursively search for relevant triples following the current node and all its successors
            :param node: Tree node to be followed
            :param tree_graph:
            :param seed_space:
            :param seed: Collected seed for the current node
            :return:
            """

            def node_has_filter(x):
                """
                Check if a node is a pattern node and has an object filter
                """
                p_node = list(self.__plan_graph.objects(subject=x, predicate=AGORA.byPattern))
                return len(p_node) and 'filter_object' in self.__patterns[p_node.pop()]

            try:
                # Get the sorted list of current node's successors
                nxt = sorted(list(self.__plan_graph.objects(node, AGORA.next)),
                             key=lambda x: node_has_filter(x), reverse=True)

                # Per each successor...
                for n in nxt:
                    if seed_space in self.__node_spaces[n]:
                        node_patterns = self.__node_patterns.get(n, [])

                        # In case the node is not a leaf, 'onProperty' tells which is the next link to follow
                        try:
                            link = list(self.__plan_graph.objects(subject=n, predicate=AGORA.onProperty)).pop()
                        except IndexError:
                            link = None

                        next_seeds = set([])
                        # If the current node is a pattern node, it must search for triples to yield
                        for pattern in node_patterns:
                            pattern_space = self.__patterns[pattern].get('space', None)
                            if pattern_space != seed_space or seed in self.__subjects_to_ignore[pattern_space]:
                                continue

                            subject_filter = self.__patterns[pattern].get('filter_subject', None)
                            if subject_filter is not None and seed != subject_filter:
                                continue

                            pattern_link = self.__patterns[pattern].get('property', None)

                            # If pattern is of type '?s prop O'...
                            if pattern_link is not None:
                                if (seed, pattern_link) not in self.__fragment:
                                    obj_filter = self.__patterns[pattern].get('filter_object', None)
                                    if on_plink is not None:
                                        on_plink(pattern_link, [seed], pattern_space)

                                    apply_filter = True
                                    try:
                                        for seed_object in list(
                                                __process_pattern_link_seed(seed, tree_graph, pattern_link)):
                                            __check_stop()
                                            quad = (pattern, seed, pattern_link, seed_object)
                                            if obj_filter is None or u''.join(seed_object).encode(
                                                    'utf-8') == u''.join(obj_filter.toPython()).encode('utf-8'):
                                                self.__fragment.add((seed, pattern_link))
                                                __put_triple_in_queue(quad)
                                                apply_filter = False
                                        if obj_filter is not None and apply_filter:
                                            self.__subjects_to_ignore[pattern_space].add(seed)
                                    except AttributeError, e:
                                        log.warning('Trying to find {} objects of {}: {}'.format(link, seed, e.message))

                            # If pattern is of type '?s a Concept'...
                            obj_type = self.__patterns[pattern].get('type', None)
                            if obj_type is not None:
                                check_type = self.__patterns[pattern].get('check', False)
                                if on_type is not None:
                                    on_type(obj_type, [seed], pattern_space)

                                __dereference_uri(tree_graph, seed)
                                try:
                                    seed_objects = list(tree_graph.objects(subject=seed, predicate=link))
                                    for seed_object in seed_objects:
                                        type_triple = (pattern, seed_object, RDF.type, obj_type)
                                        # In some cases, it is necessary to verify the type of the seed
                                        if (seed_object, obj_type) not in self.__fragment:
                                            if check_type:
                                                __dereference_uri(tree_graph, seed_object)
                                                types = list(
                                                    tree_graph.objects(subject=seed_object, predicate=RDF.type))
                                                if obj_type in types:
                                                    self.__fragment.add((seed_object, obj_type))
                                                    __put_triple_in_queue(type_triple)
                                                else:
                                                    self.__subjects_to_ignore[pattern_space].add(seed_object)
                                            else:
                                                self.__fragment.add((seed_object, obj_type))
                                                __put_triple_in_queue(type_triple)
                                except AttributeError, e:
                                    log.warning('Trying to find {} objects of {}: {}'.format(link, seed, e.message))

                        # If the current node is not a leaf... go on finding seeds for the successors
                        if link is not None and seed not in self.__subjects_to_ignore[seed_space]:
                            if on_link is not None:
                                on_link(link, [seed], seed_space)
                            __process_link_seed(seed, tree_graph, link, next_seeds)

                        chs = list(chunks(list(next_seeds), min(len(next_seeds), max(1, workers / 2))))
                        next_seeds.clear()
                        try:
                            while True:
                                __check_stop()
                                chunk = chs.pop()
                                threads = []
                                for s in chunk:
                                    try:
                                        workers_queue.put_nowait(s)
                                        future = pool.submit(__follow_node, n, tree_graph, seed_space, s)
                                        threads.append(future)
                                    except Queue.Full:
                                        # If all threads are busy...I'll do it myself
                                        __follow_node(n, tree_graph, seed_space, s)
                                    except Queue.Empty:
                                        pass

                                wait(threads)
                                [(workers_queue.get_nowait(), workers_queue.task_done()) for _ in threads]
                        except (IndexError, KeyError):
                            pass
            except Queue.Full:
                stop_event.set()
            except Exception, e:
                traceback.print_exc()
                log.error(e.message)
                return

        def get_fragment_triples():
            """
            Iterate over all search trees and yield relevant triples
            :return:
            """

            def execute_plan():
                for tree in trees:
                    if on_tree is not None:
                        on_tree(tree)

                    # Prepare an dedicated graph for the current tree and a set of type triples (?s a Concept)
                    # to be evaluated retrospectively
                    tree_graph = __create_graph(conjunctive=True)

                    try:
                        self.__resource_queue[tree_graph] = []

                        # Get all seeds of the current tree
                        seeds = list(self.__plan_graph.objects(tree, AGORA.hasSeed))
                        if on_seeds is not None:
                            on_seeds(seeds)

                        # Check if the tree root is a pattern node and in that case, adds a type triple to the
                        # respective set
                        root_pattern = list(self.__plan_graph.objects(tree, AGORA.byPattern))
                        if len(root_pattern):
                            pattern_node = list(
                                self.__plan_graph.objects(subject=tree, predicate=AGORA.byPattern)).pop()
                            seed_type = self.__patterns[pattern_node].get('type', None)
                            [type_triples.add((pattern_node, sd, seed_type)) for sd in seeds]

                        # Get the children of the root node and follow them recursively
                        nxt = list(self.__plan_graph.objects(tree, AGORA.next))
                        if len(nxt):
                            # Prepare the list of seeds to start the exploration with, taking into account all
                            # search spaces that were defined
                            s_seeds = set(seeds)
                            for sp in self.__spaces:
                                for seed in s_seeds:
                                    __follow_node(tree, tree_graph, sp, seed)
                    finally:
                        __destroy_graph(tree_graph)

                    if lazy and found_data:
                        break

                self.__completed = True

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

            type_triples = set([])

            thread = Thread(target=execute_plan)
            thread.daemon = True
            thread.start()

            found_data = False
            while not self.__completed or fragment_queue.not_empty:
                try:
                    (t, s, p, o) = fragment_queue.get(timeout=1)
                    found_data = True
                    fragment_queue.task_done()
                    if p == RDF.type:
                        type_triples.add((t, s, o))
                    else:
                        yield (t, s, p, o)
                except Queue.Empty:
                    if self.__completed:
                        break
                self.__last_iteration_ts = dt.now()
            thread.join()

            # All type triples that are of subjects to ignore won't be returned (this has to be done this way
            # because of generators nature)
            all_ignores = {}
            if self.__subjects_to_ignore.values():
                all_ignores = set.intersection(*self.__subjects_to_ignore.values())
            valid_type_triples = [(t, s, o) for (t, s, o) in type_triples if s not in all_ignores]
            for (t, s, o) in valid_type_triples:
                if on_type_validation is not None:
                    on_type_validation((t, s, RDF.type, o))
                yield (t, s, RDF.type, o)

        return get_fragment_triples(), self.__plan_graph.namespaces(), self.__plan_graph
