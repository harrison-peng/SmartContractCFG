import functools
from graphviz import Digraph
from Node import Node
from Edge import Edge

class Cfg:

    def __init__(self, nodes: [Node], edges: [Edge]):
        self.nodes = nodes
        self.edges = edges
        self.graph = Digraph(format='svg', node_attr={'shape': 'box'})

    def build_cfg(self, file):
        for node in self.nodes:
            self.graph.node(str(node.tag), label=self.__node_obj_to_graph_content(node))
        for edge in self.edges:
            self.graph.edge(str(edge.from_), str(edge.to_))
        self.graph.render(file)

    def __node_obj_to_graph_content(self, node: Node) -> str:
        content = '[ADDRESS: %s]\n\n' % str(node.tag)
        opcdoes = node.opcodes
        for opcode in opcdoes:
            content += '%s: %s %s\n' % (opcode.pc, opcode.name, opcode.value if opcode.value else '')
        return content
