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

import StringIO
from urllib import urlencode

import pkg_resources
import requests
from agora.client.execution import PlanExecutor
from rdflib import Graph
from rdflib.plugins.parsers.notation3 import BadSyntax

__author__ = 'Fernando Serena'

try:
    pkg_resources.declare_namespace(__name__)
except ImportError:
    import pkgutil
    __path__ = pkgutil.extend_path(__path__, __name__)


class FountainException(Exception):
    pass


class FragmentCollector(object):
    """ Class for interacting with the Agora planner and executing the plan for a certain graph pattern.
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

    def get_fragment(self, **kwargs):
        return self.__plan_executor.get_fragment(**kwargs)

    def get_fragment_generator(self, **kwargs):
        return self.__plan_executor.get_fragment_generator(**kwargs)


class Agora(object):
    """
    Wrapper class for the FragmentCollector
    """

    def __init__(self, host='localhost', port=9001):
        self.__host = 'http://{}:{}'.format(host, port)

    def get_fragment(self, gp, **kwargs):
        """
        Return a complete fragment for a given gp.
        :param gp: A graph pattern
        :return:
        """
        collector = FragmentCollector(self.__host, gp)
        return collector.get_fragment(**kwargs)

    def get_fragment_generator(self, gp, **kwargs):
        """
        Return a fragment generator for a given gp.
        :param gp:
        :param kwargs:
        :return:
        """
        collector = FragmentCollector(self.__host, gp)
        return collector.get_fragment_generator(**kwargs)

    @property
    def prefixes(self):
        response = requests.get(self.__host + '/prefixes')
        if response.status_code == 200:
            return response.json()

        raise FountainException(response.text)
