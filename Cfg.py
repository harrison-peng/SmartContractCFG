import functools
from global_constants import logging
from graphviz import Digraph
from Node import Node
from Edge import Edge
from Opcode import Opcode

class Cfg:

    def __init__(self):
        self.nodes = list()
        self.edges = list()
        self.graph = Digraph(format='svg', node_attr={'shape': 'box'})

    def build_cfg(self, opcode_data):
        logging.info('Constructing CFG...')
        
        self.__tag_index_dict = dict()
        opcode_list = opcode_data.split('\n')
        for i in range(len(opcode_list)):
            opcode_list[i] = (i, opcode_list[i])
        self.opcode_list = opcode_list
        
        for index, line in self.opcode_list:
            code_set = line.rstrip().split(' ')
            pc = int(code_set[0].replace(':', ''))
            s = code_set[1:]
            if s[0] == 'JUMPDEST':
                self.__tag_index_dict.update({pc: index})
        
        self.__building_cfg(0, list(), list(), True)

        for tag in self.__tag_index_dict:
            if tag not in [node.tag for node in self.nodes]:
                self.__building_cfg(tag, [0], list(), False)

    def __building_cfg(self, tag, stack, path, exec_mode):
        # logging.debug('TAG: %s %s\n' % (tag, path))
        segment_ins = ['JUMPDEST', 'JUMP', 'JUMPI', 'STOP', 'REVERT', 'INVALID', 'RETURN', 'SELFDESTRUCT']
        content = list()

        opcode_sublist = self.opcode_list[self.__tag_index_dict[tag]:] if tag != 0 else self.opcode_list
        for index, line in opcode_sublist:
            code_set = line.rstrip().split(' ')
            pc = int(code_set[0].replace(':', ''))
            s = code_set[1:]
            opcode = Opcode(pc, s[0], None) if len(s) == 1 else Opcode(pc, s[0], s[1])

            if exec_mode:
                stack, jump_tag = self.__simulate_stack(stack, opcode)

            if s[0] == '':
                continue
            elif s[0] in segment_ins:
                if s[0] == 'JUMPDEST':
                    path.append(opcode.pc)
                    
                    if content:
                        node = Node(int(tag), content)
                        edge = Edge(int(tag), int(opcode.pc))
                        if node not in self.nodes:
                            self.nodes.append(node)
                        if edge not in self.edges:
                            self.edges.append(edge)
                        content = list()

                    tag = opcode.pc
                    content.append(opcode)
                elif s[0] == 'JUMP':
                    content.append(opcode)
                    node = Node(int(tag), content)
                    if node not in self.nodes:
                        self.nodes.append(node)

                    if exec_mode:
                        edge = Edge(int(tag), int(jump_tag))
                        if edge not in self.edges:
                            self.edges.append(edge)
                        self.__building_cfg(jump_tag, list(stack), path, exec_mode)
                    return
                elif s[0] == 'JUMPI':
                    self.__tag_index_dict[opcode.get_next_pc()] = index + 1
                    content.append(opcode)
                    node = Node(int(tag), content)
                    if node not in self.nodes:
                        self.nodes.append(node)

                    if exec_mode:
                        edge = Edge(int(tag), int(jump_tag))
                        if edge not in self.edges:
                            self.edges.append(edge)
                        if jump_tag not in path:
                            self.__building_cfg(jump_tag, list(stack), list(path), exec_mode)

                        edge = Edge(int(tag), int(opcode.get_next_pc()))
                        if edge not in self.edges:
                            self.edges.append(edge)
                        if opcode.get_next_pc() not in path:
                            self.__building_cfg(opcode.get_next_pc(), list(stack), list(path), exec_mode)
                    return
                else:
                    content.append(opcode)
                    node = Node(int(tag), content)
                    if node not in self.nodes:
                        self.nodes.append(node)
                    return
            else:
                if not content:
                    # NOTE: node content is empty -> from JUMPI
                    tag = opcode.pc
                    path.append(opcode.pc)
                content.append(opcode)

    def render(self, file):
        for node in self.nodes:
            self.graph.node(str(node.tag), label=self.__node_to_graph_content(node))
        for edge in self.edges:
            self.graph.edge(str(edge.from_), str(edge.to_))
        self.graph.render(file)

    def __node_to_graph_content(self, node: Node) -> str:
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

    def get_node(self, tag: int) -> Node:
        return [node for node in self.nodes if tag == node.tag][0]

    def add_edge(self, edge: Edge):
        self.edges.append(edge)

    def get_edge(self, from_: int, to_: int) -> Edge:
        return [edge for edge in self.edges if edge.from_ == from_ and edge.to_ == to_][0]

    def __simulate_stack(self, stack: list(), opcode: Opcode):
        jump_tag = None

        if opcode.name in ['INVALID', 'STOP', 'REVERT', 'JUMPDEST']:
            pass
        elif opcode.name == 'TIMESTAMP':
            stack.append('TIMESTAMP')
        elif opcode.name == 'ADD':
            first = stack.pop()
            second = stack.pop()
            stack.append('ADD')
        elif opcode.name == 'MUL':
            first = stack.pop()
            second = stack.pop()
            stack.append('MUL')
        elif opcode.name == 'SUB':
            first = stack.pop()
            second = stack.pop()
            stack.append('SUB')
        elif opcode.name == 'DIV':
            first = stack.pop()
            second = stack.pop()
            stack.append('DIV')
        elif opcode.name == 'SDIV':
            first = stack.pop()
            second = stack.pop()
            stack.append('SDIV')
        elif opcode.name == 'MOD':
            first = stack.pop()
            second = stack.pop()
            stack.append('MOD')
        elif opcode.name == 'SMOD':
            first = stack.pop()
            second = stack.pop()
            stack.append('SMOD')
        elif opcode.name == 'ADDMOD':
            first = stack.pop()
            second = stack.pop()
            third = stack.pop()
            stack.append('ADDMOD')
        elif opcode.name == 'MULMOD':
            first = stack.pop()
            second = stack.pop()
            third = stack.pop()
            stack.append('MULMOD')
        elif opcode.name == 'EXP':
            first = stack.pop()
            second = stack.pop()
            stack.append('EXP')
        elif opcode.name == 'SIGNEXTEND':
            first = stack.pop()
            second = stack.pop()
            stack.append('SIGNEXTEBD')
        elif opcode.name == 'LT':
            first = stack.pop()
            second = stack.pop()
            stack.append('LT')
        elif opcode.name == 'GT':
            first = stack.pop()
            second = stack.pop()
            stack.append('GT')
        elif opcode.name == 'SLT':
            first = stack.pop()
            second = stack.pop()
            stack.append('SLT')
        elif opcode.name == 'SGT':
            first = stack.pop()
            second = stack.pop()
            stack.append('SGT')
        elif opcode.name == 'EQ':
            first = stack.pop()
            second = stack.pop()
            stack.append('EQ')
        elif opcode.name == 'ISZERO':
            first = stack.pop()
            stack.append('ISZERO')
        elif opcode.name == 'AND':
            first = stack.pop()
            second = stack.pop()
            if isinstance(first, int) and isinstance(second, int):
                stack.append(first & second)
            else:
                stack.append('AND')
        elif opcode.name == 'OR':
            first = stack.pop()
            second = stack.pop()
            if isinstance(first, int) and isinstance(second, int):
                stack.append(first | second)
            else:
                stack.append('AND')
        elif opcode.name == 'XOR':
            first = stack.pop()
            second = stack.pop()
            stack.append('XOR')
        elif opcode.name == 'NOT':
            first = stack.pop()
            if isinstance(first, int):
                stack.append(~first)
            else:
                stack.append('NOT')
        elif opcode.name == 'BYTE':
            first = stack.pop()
            second = stack.pop()
            stack.append('BYTE')
        elif opcode.name in ['SHA3', 'KECCAK256']:
            first = stack.pop()
            second = stack.pop()
            stack.append('SHA3')
        elif opcode.name == 'ADDRESS':
            stack.append('ADDRESS')
        elif opcode.name == 'BALANCE':
            first = stack.pop()
            stack.append('BALANCE')
        elif opcode.name == 'CALLER':
            stack.append('CALLER')
        elif opcode.name == "ORIGIN":
            stack.append('ORIGIN')
        elif opcode.name == 'CALLVALUE':
            stack.append('CALLVALUE')
        elif opcode.name == 'CALLDATALOAD':
            first = stack.pop()
            stack.append('CALLDATALOAD')
        elif opcode.name == 'CALLDATASIZE':
            stack.append('CALLDATASIZE')
        elif opcode.name == "CALLDATACOPY":
            first = stack.pop()
            second = stack.pop()
            third = stack.pop()
        elif opcode.name == 'CODESIZE':
            stack.append('CODESIZE')
        elif opcode.name == 'CODECOPY':
            first = stack.pop()
            second = stack.pop()
            third = stack.pop()
        elif opcode.name == 'GASPRICE':
            stack.append('GASPRICE')
        elif opcode.name == 'RETURNDATACOPY':
            first = stack.pop()
            second = stack.pop()
            third = stack.pop()
        elif opcode.name == 'RETURNDATASIZE':
            stack.append('RETURNDATASIZE')
        elif opcode.name == 'NUMBER':
            stack.append('NUMBER')
        elif opcode.name == 'POP':
            stack.pop()
        elif opcode.name == 'MLOAD':
            first = stack.pop()
            stack.append('MLOAD')
        elif opcode.name == 'MSTORE':
            first = stack.pop()
            second = stack.pop()
        elif opcode.name == 'SLOAD':
            first = stack.pop()
            stack.append('SLOAD')
        elif opcode.name == 'SSTORE':
            first = stack.pop()
            second = stack.pop()
        elif opcode.name == 'JUMP':
            jump_tag = stack.pop()
        elif opcode.name == 'JUMPI':
            jump_tag = stack.pop()
            second = stack.pop()
        elif opcode.name == 'GAS':
            stack.append('GAS')
        elif opcode.name.startswith('PUSH', 0):
            stack.append(int(opcode.value, 16))
        elif opcode.name.startswith('DUP', 0):
            idx = len(stack) - int(opcode.name[3:], 10)
            stack.append(stack[idx])
        elif opcode.name.startswith('SWAP', 0):
            idx_1 = len(stack) - 1
            idx_2 = len(stack) - 1 - int(opcode.name[4:], 10)
            stack[idx_1], stack[idx_2] = stack[idx_2], stack[idx_1]
        elif opcode.name in ('LOG0', 'LOG1', 'LOG2', 'LOG3', 'LOG4'):
            first = stack.pop()
            second = stack.pop()
            for _ in range(int(opcode.name[3:])):
                stack.pop()
        elif opcode.name == 'CALL':
            first = stack.pop()
            second = stack.pop()
            third = stack.pop()
            fourth = stack.pop()
            fifth = stack.pop()
            sixth = stack.pop()
            seventh = stack.pop()
            stack.append('CALL')
        elif opcode.name == 'CALLCODE':
            first = stack.pop()
            second = stack.pop()
            third = stack.pop()
            fourth = stack.pop()
            fifth = stack.pop()
            sixth = stack.pop()
            seventh = stack.pop()
            stack.append('CALLCODE')
        elif opcode.name in ['DELEGATECALL', 'STATICCALL']:
            first = stack.pop()
            second = stack.pop()
            third = stack.pop()
            fourth = stack.pop()
            fifth = stack.pop()
            sixth = stack.pop()
            stack.append('DELEGATECALL')
        elif opcode.name == 'RETURN':
            first = stack.pop()
            second = stack.pop()
        elif opcode.name == 'CREATE':
            first = stack.pop()
            second = stack.pop()
            third = stack.pop()
            stack.append('CREATE')
        elif opcode.name == 'EXTCODESIZE':
            first = stack.pop()
            stack.append('EXTCODESIZE')
        elif opcode.name == 'BLOCKHASH':
            first = stack.pop()
            stack.append('BLOCKHASH')
        elif opcode.name == 'SELFDESTRUCT':
            first = stack.pop()
        else:
            raise Exception('UNKNOWN INSTRUCTION:', opcode.name, opcode.pc)
        if jump_tag and not isinstance(jump_tag, int):
            raise ValueError('ERROR TAG:', opcode.pc, jump_tag, stack)
        return stack, jump_tag
