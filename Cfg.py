import functools
from global_constants import logging
from graphviz import Digraph
from cfg_builder import ins_sim
from Node import Node
from Edge import Edge
from Opcode import Opcode

class Cfg:

    def __init__(self):
        self.nodes = list()
        self.edges = list()
        self.graph = Digraph(format='svg', node_attr={'shape': 'box'})

    def build_cfg(self, opcode_data):
        logging.info('[INFO] Constructing CFG...')
        
        self.__addr_index_dict = dict()
        opcode_list = opcode_data.split('\n')
        for i in range(len(opcode_list)):
            opcode_list[i] = (i, opcode_list[i])
        
        for index, line in opcode_list:
            code_set = line.rstrip().split(' ')
            pc = int(code_set[0].replace(':', ''))
            s = code_set[1:]
            if s[0] == 'JUMPDEST':
                self.__addr_index_dict.update({pc: index})
        
        self.__building_cfg(opcode_list, 0, 0, list(), list(), True)

        for addr in self.__addr_index_dict:
            if addr not in [node.tag for node in self.nodes]:
                self.__building_cfg(opcode_list, self.__addr_index_dict[addr], addr, [0], list(), False)

    def __building_cfg(self, opcode_list, start_idx, curr_addr, stack, path, exec_mode):
        segment_ins = ['JUMPDEST', 'JUMP', 'JUMPI', 'STOP', 'REVERT', 'INVALID', 'RETURN', 'SELFDESTRUCT']
        opcode_obj_list = list()

        opcode_sublist = opcode_list[start_idx:]
        for index, line in opcode_sublist:
            code_set = line.rstrip().split(' ')
            pc = int(code_set[0].replace(':', ''))
            s = code_set[1:]

            jump_addr = None
            if exec_mode:
                stack, jump_addr = ins_sim(stack, s, pc)

            if s[0] == '':
                continue
            elif s[0] in segment_ins:
                if s[0] == 'JUMPDEST':
                    path.append(pc)
                    
                    if opcode_obj_list:
                        node_obj = Node(int(curr_addr), opcode_obj_list)
                        edge_obj = Edge(int(curr_addr), int(pc))
                        if node_obj not in self.nodes:
                            self.nodes.append(node_obj)
                        if edge_obj not in self.edges:
                            self.edges.append(edge_obj)
                        opcode_obj_list = list()

                    curr_addr = pc
                    opcode_obj_list.append(Opcode(int(pc), s[0], None))
                elif s[0] == 'JUMP':
                    opcode_obj_list.append(Opcode(int(pc), s[0], None))
                    node_obj = Node(int(curr_addr), opcode_obj_list)
                    if node_obj not in self.nodes:
                        self.nodes.append(node_obj)
                    edge_obj = Edge(int(curr_addr), int(jump_addr))
                    if edge_obj not in self.edges:
                        self.edges.append(edge_obj)

                    if exec_mode:
                        self.__building_cfg(opcode_list, self.__addr_index_dict[jump_addr], jump_addr, list(stack), path, exec_mode)
                    return
                elif s[0] == 'JUMPI':
                    opcode_obj_list.append(Opcode(int(pc), s[0], None))
                    node_obj = Node(int(curr_addr), opcode_obj_list)
                    if node_obj not in self.nodes:
                        self.nodes.append(node_obj)

                    if exec_mode:
                        jump_addr_true = jump_addr
                        jump_idx_true = self.__addr_index_dict[jump_addr_true]
                        jump_addr_false = pc + 1
                        jump_idx_false = index + 1
                        stack_true = list(stack)
                        stack_false = list(stack)
                        path_true = list(path)
                        path_false = list(path)

                        edge_obj = Edge(int(curr_addr), int(jump_addr_true))
                        if edge_obj not in self.edges:
                            self.edges.append(edge_obj)
                        if jump_addr_true not in path:
                            self.__building_cfg(opcode_list, jump_idx_true, jump_addr_true, stack_true, path_true, exec_mode)

                        edge_obj = Edge(int(curr_addr), int(jump_addr_false))
                        if edge_obj not in self.edges:
                            self.edges.append(edge_obj)
                        if jump_addr_false not in path:
                            self.__building_cfg(opcode_list, jump_idx_false, jump_addr_false, stack_false, path_false, exec_mode)
                    return
                else:
                    opcode_obj_list.append(Opcode(int(pc), s[0], None))
                    node_obj = Node(int(curr_addr), opcode_obj_list)
                    if node_obj not in self.nodes:
                        self.nodes.append(node_obj)
                    return
            else:
                if not opcode_obj_list:
                    # NOTE: node content is empty -> from JUMPI
                    curr_addr = pc
                    path.append(pc)
                if len(s) == 1:
                    opcode_obj_list.append(Opcode(int(pc), s[0], None))
                else:
                    opcode_obj_list.append(Opcode(int(pc), s[0], s[1]))

    def render(self, file):
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

    def node_num(self) -> int:
        return len(self.nodes)

    def edge_num(self) -> int:
        return len(self.edges)

    def ins_num(self) -> int:
        return sum([len(node.opcodes) for node in self.nodes])