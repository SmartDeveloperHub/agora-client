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

from agora_client.agora import Agora
from blessings import Terminal
import sys
from rdflib import Graph
from time import time

total_derefs = 0
total_triples = 0


def stringify_uri_list(objs):
    if not len(objs):
        return '[]'
    return ', '.join(map(lambda x: x.n3(graph.namespace_manager), objs))


def out_load(uri, triples):
    global total_derefs
    global total_triples
    total_derefs += 1
    total_triples += len(triples)
    mto = ''
    if len(triples) > 1:
        mto = 's'
    print term.cyan + 'Deref' + '(<{}>) => {} triple{}'.format(uri, len(triples), mto) + term.normal


def out_seeds(seeds):
    pass
    # print seeds


def out_plink(uri, objs, sp):
    print term.green + '({}) Looking for triples with property {} at {}'.\
        format(sp, uri.n3(graph.namespace_manager), stringify_uri_list(objs)) + term.normal


def out_link(uri, objs, sp):
    print term.green + '({}) Following {} from {}'.\
        format(sp, uri.n3(graph.namespace_manager), stringify_uri_list(objs)) + term.normal


def out_type(uri, objs, sp):
    print term.green + "({}) Searching {}'s at {}".\
        format(sp, uri.n3(graph.namespace_manager), stringify_uri_list(objs)) + term.normal


def out_type_validation((s, _, o)):
    print term.green + 'Extracted {} as subject of type {}'.format(s.n3(graph.namespace_manager),
                                                                     o.n3(graph.namespace_manager)) + term.white


def out_tree(node):
    print term.bold_blue("Starting tree navigation {}".format(node.n3(graph.namespace_manager)))

term = Terminal()
PLANNER = 'http://localhost:5000'
agora = Agora(PLANNER)

# pattern = """{?s a sdh:Contribution.
#               ?s foaf:name "jenkins".
#               ?s sdh:hasCommits ?cc.
#               ?cc sdh:size ?t.
#               ?cc sdh:commits ?c.
#               ?r dc:created ?y.}"""

# pattern = """{?s a sdh:Commit}"""
pattern = """{?m a scm:Merge}"""

if len(sys.argv) > 1:
    pattern = sys.argv[1]
if len(sys.argv) > 2:
    unnattended = True
else:
    unnattended = False

print term.bold + term.underline + 'Agora Console Client v0.1' + term.normal
print 'Connected to an Agora-Planner at %s.' % PLANNER

print 'Trying to retrieve a fragment for:',
print term.bold + pattern + term.normal
raw_input(term.bold_blue('(send)'))
print 'Requesting a plan...',
start_time = time()

fragment, namespaces, plan = agora.get_fragment_generator(pattern, on_load=out_load, on_seeds=out_seeds,
                                                          on_plink=out_plink, on_link=out_link,
                                                          on_type=out_type, on_type_validation=out_type_validation,
                                                          on_tree=out_tree)
print 'Done! (in ~{}ms)'.format(int(1000 * (time() - start_time)))
raw_input(term.bold_blue('(take a look)'))
print term.bold_yellow('Search plan:')
print term.yellow + plan.serialize(format='turtle') + term.normal

graph = Graph()
for (prefix, u) in namespaces:
    graph.bind(prefix, u)


raw_input(term.blink(term.bold_blue('(run)')))

final_triples = 0
for tp in fragment:
    graph.add(tp)
    final_triples += 1
    print term.bold_green_on_bright_green('{} {} {} .'.format(tp[0].n3(graph.namespace_manager),
                                                              tp[1].n3(graph.namespace_manager),
                                                              tp[2].n3(graph.namespace_manager)))
    if not unnattended:
        raw_input(term.bold_blue('(more)'))

print term.bold_yellow('\nFragment:')
print term.yellow(graph.serialize(format='turtle'))

print term.bold_white('Summary:')
print 'Resources dereferenced = {}'.format(term.bold(str(total_derefs)))
print 'Triples collected = {}'.format(term.bold(str(total_triples)))
print 'Fragment triples = {}'.format(term.bold(str(final_triples)))
