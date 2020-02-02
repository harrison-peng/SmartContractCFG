import src.settings as settings
from typing import Any
import networkx as nx
from subprocess import call
from src.settings import logging, CFG_STATE
from src.Node import Node
from src.Edge import Edge
from src.Opcode import Opcode
from src.Path import Path

class Cfg:

    segment_ins = ['JUMPDEST', 'JUMP', 'JUMPI', 'STOP', 'REVERT', 'INVALID', 'RETURN', 'SELFDESTRUCT']

    def __init__(self):
        self.nodes = list()
        self.edges = list()
        self.graph = None
        self.count = 0

    def build_cfg(self, opcode_data: str) -> None:
        logging.info('Constructing CFG...')
        
        self.__tag_index_dict = dict()
        opcode_list = opcode_data.split('\n')
        for i in range(len(opcode_list)):
            opcode_list[i] = (i, opcode_list[i])
        self.opcode_list = opcode_list
        self.check_list = list(range(len(opcode_list)))
        
        for index, line in self.opcode_list:
            code_set = line.rstrip().split(' ')
            pc = int(code_set[0].replace(':', ''))
            s = code_set[1:]
            self.__tag_index_dict.update({pc: index})
        
        self.__test()
        # self.__building_cfg(0, list(), list())
        
        # while self.check_list:
        #     try:
        #         self.__building_cfg(list(self.__tag_index_dict.keys())[list(self.__tag_index_dict.values()).index(self.check_list.pop(0))], [0], list())
        #     except:
        #         continue

        # self.__building_cfg(0, list(), list())

    def __test(self):
        opcodes = list()
        push_value = ''
        pre_opcode = None
        start_idx = 0
        start_pc = 0
        for index, line in self.opcode_list:
            code_set = line.rstrip().split(' ')
            pc = int(code_set[0].replace(':', ''))
            s = code_set[1:]
            opcode = Opcode(pc, s[0], None) if len(s) == 1 else Opcode(pc, s[0], s[1])
            opcodes.append(opcode)

        for index, opcode in enumerate(opcodes):
            # print(start_idx, index, opcode)
            if opcode.name == 'JUMPDEST' and start_idx != index:
                content = opcodes[start_idx:index]
                # print(start_idx, index, content)
                node = Node(start_pc, content)
                self.nodes.append(node)
                start_idx = index
                start_pc = opcode.pc
            elif opcode.name.startswith('PUSH'):
                push_value = opcode.value
            elif opcode.name == 'JUMP' and pre_opcode.name.startswith('PUSH'):
                content = opcodes[start_idx:index+1]
                node = Node(start_pc, content)
                self.nodes.append(node)
                edge = Edge(start_pc, int(pre_opcode.value, 16))
                self.edges.append(edge)
                start_idx = index + 1
                start_pc = opcode.pc + 1
            elif opcode.name == 'JUMPI':
                content = opcodes[start_idx:index+1]
                node = Node(start_pc, content)
                self.nodes.append(node)
                edge = Edge(start_pc, int(pre_opcode.value, 16))
                self.edges.append(edge)
                edge = Edge(start_pc, opcode.pc + 1)
                self.edges.append(edge)
                start_idx = index + 1
                start_pc = opcode.pc + 1
            elif opcode.name in ['STOP', 'RETURN', 'REVERT', 'INVALID', 'SELFDESTRUCT']:
                content = opcodes[start_idx:index+1]
                node = Node(start_pc, content)
                self.nodes.append(node)
                start_idx = index + 1
                start_pc = opcode.pc + 1
            pre_opcode = opcode
            

    def __building_cfg(self, tag: int, stack: list, path: list) -> None:
        self.count += 1
        if self.count % 1000 == 0:
            logging.debug('CFG node visit: %s' % self.count)
        if self.count >= 60000:
            logging.debug('CFG node EXCEED: %s' % self.count)
            return

        # logging.debug('TAG: %s %s\n' % (tag, path))
        content = list()
        
        opcode_sublist = self.opcode_list[self.__tag_index_dict[tag]:] if tag != 0 else self.opcode_list
        for index, line in opcode_sublist:
            if index in self.check_list:
                self.check_list.remove(index)
            code_set = line.rstrip().split(' ')
            pc = int(code_set[0].replace(':', ''))
            s = code_set[1:]
            opcode = Opcode(pc, s[0], None) if len(s) == 1 else Opcode(pc, s[0], s[1])

            stack, jump_tag = self.__simulate_stack(stack, opcode)

            if stack == 'Error':
                content.append(opcode)
                if s[0] in self.segment_ins:
                    node = Node(int(tag), content)
                    if node not in self.nodes:
                        self.nodes.append(node)
                    if s[0] == 'JUMPI':
                        edge = Edge(int(tag), int(opcode.get_next_pc()))
                        if edge not in self.edges:
                            self.edges.append(edge)
                            self.__building_cfg(int(opcode.get_next_pc()), list(), path)
                        edge = Edge(int(tag), jump_tag)
                        if edge not in self.edges:
                            self.edges.append(edge)
                            self.__building_cfg(jump_tag, list(), path)
                    return
                stack = list()
                continue

            if s[0] == '':
                continue
            elif s[0] in self.segment_ins:
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

                    if int(jump_tag) != 0:
                        edge = Edge(int(tag), int(jump_tag))
                        if edge not in self.edges:
                            self.edges.append(edge)
                        self.__building_cfg(jump_tag, list(stack), path)
                    return
                elif s[0] == 'JUMPI':
                    self.__tag_index_dict[opcode.get_next_pc()] = index + 1
                    content.append(opcode)
                    node = Node(int(tag), content)
                    if node not in self.nodes:
                        self.nodes.append(node)

                    edge = Edge(int(tag), int(jump_tag))
                    if edge not in self.edges:
                        self.edges.append(edge)
                    if jump_tag not in path:
                        self.__building_cfg(jump_tag, list(stack), list(path))

                    edge = Edge(int(tag), int(opcode.get_next_pc()))
                    if edge not in self.edges:
                        self.edges.append(edge)
                    if opcode.get_next_pc() not in path:
                        self.__building_cfg(opcode.get_next_pc(), list(stack), list(path))
                    return
                else:
                    content.append(opcode)
                    node = Node(int(tag), content)
                    if s[0] == 'RETURN':
                        node.set_color('green')
                    elif s[0] == 'STOP':
                        node.set_color('blue')
                    else:
                        node.set_color('red')
                    if node not in self.nodes:
                        self.nodes.append(node)
                    return
            else:
                if not content:
                    # NOTE: node content is empty -> from JUMPI
                    tag = opcode.pc
                    path.append(opcode.pc)
                content.append(opcode)

    def render(self, file: str, paths: list = None) -> None:
        G = nx.DiGraph()
        nodes_dict = None
        if paths and CFG_STATE:
            nodes_dict = self.__get_all_node_of_paths(paths)
        if settings.CFG_FORMAT == 'html':
            for node in self.nodes:
                if nodes_dict:
                    G.add_node(node.tag, id=node.tag, color=node.color, tooltip=self.__node_to_graph_content(node, nodes_dict.get(node.tag, None)))
                else:
                    G.add_node(node.tag, id=node.tag, color=node.color, tooltip=self.__node_to_graph_content(node))
            for edge in self.edges:
                label = '[Path Constraint]\n\n%s' % edge.path_constraint
                G.add_edge(edge.from_, edge.to_, tooltip=label, color=edge.color)

            with open('%s.html' % file, 'w') as f:
                f.write(self.svg_to_html(nx.nx_pydot.to_pydot(G).create_svg().decode("utf-8")))
        elif settings.CFG_FORMAT == 'svg':
            for node in self.nodes:
                G.add_node(node.tag, id=node.tag, color=node.color, shape='box', label=self.__node_to_graph_content(node))
            for edge in self.edges:
                G.add_edge(edge.from_, edge.to_, label=edge.path_constraint if edge.path_constraint else '', color=edge.color)

            with open('%s.svg' % file, 'wb') as f:
                f.write(nx.nx_pydot.to_pydot(G).create_svg())
        else:
            logging.error('CFG format error')


    def __node_to_graph_content(self, node: Node, node_list: list = None) -> str:
        seg = '-+-+' * 10
        sub_seg = '-' * 50
        content = '[ADDRESS: %s]\n\n' % str(node.tag)
        opcdoes = node.opcodes
        for opcode in opcdoes:
            content += '%s: %s %s\n' % (opcode.pc, opcode.name, opcode.value if opcode.value else '')
        if not (isinstance(node.gas, int) and node.gas == 0):
            content += '\n[GAS]: %s' % self.to_string(node.gas)
        if node_list and CFG_STATE:
            content += '\n%s\n\n' % seg
            for path_id, state in node_list:
                logging.debug('Add node to result: %s' % path_id)
                content += '[Path: %s]\n\n' % path_id
                content += 'Stack: %s\n\n' % self.to_string(state.stack)
                content += 'Memory: %s\n\n' % self.to_string(state.memory)
                content += 'Storage: %s\n' % self.to_string(state.storage)
                content += '%s\n\n' % sub_seg
        return content

    def to_string(self, input: Any) -> str:
        return str(input).replace('\n', '').replace(' ', '').replace(",'", ",\n'").replace('{', '{\n').replace('}', '\n}')

    def __get_all_node_of_paths(self, paths: [Path]) -> dict:
        result = dict()
        for path in paths:
            for node in path.path:
                logging.debug('NodeTag: %s' % node)
                n = result.get(node.tag, None)
                if n:
                    n.append((path.id, node.state))
                else:
                    result[node.tag] = [(path.id, node.state)]
        return result

    def node_num(self) -> int:
        return len(self.nodes)

    def edge_num(self) -> int:
        return len(self.edges)

    def ins_num(self) -> int:
        return sum([len(node.opcodes) for node in self.nodes])

    def __node_exist(self, tag: int) -> bool:
        for node in self.nodes:
            if node.tag == tag:
                return True
        return False

    def get_node(self, tag: int) -> Node:
        from src.Result import Result
        try:
            return [node for node in self.nodes if tag == node.tag][0]
        except Exception as e:
            result = Result()
            result.log_error(settings.ADDRESS, 'Cannot find the node [%s]: %s' % (tag, e))
            raise ValueError('Cannot find the node [%s]: %s' % (tag, e))

    def add_edge(self, edge: Edge) -> None:
        self.edges.append(edge)

    def get_edge(self, from_: int, to_: int) -> Edge:
        return [edge for edge in self.edges if edge.from_ == from_ and edge.to_ == to_][0]

    def remove_unreach_nodes(self) -> None:
        reached_list = [edge.from_ for edge in self.edges] + [edge.to_ for edge in self.edges]
        for node in list(self.nodes):
            if node.tag not in reached_list:
                self.nodes.remove(node)

    def __simulate_stack(self, stack: list(), opcode: Opcode) -> (list, int):
        from src.Result import Result
        jump_tag = None

        try:
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
                pass
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
                result = Result()
                result.log_error(settings.ADDRESS, 'UNKNOWN INSTRUCTION: %s' % opcode)
                raise Exception('UNKNOWN INSTRUCTION:', opcode.name, opcode.pc)
            if jump_tag and not isinstance(jump_tag, int):
                raise ValueError('ERROR TAG:', opcode.pc, jump_tag, stack)
            return stack, jump_tag
        except Exception as e:
            return 'Error', jump_tag

    def svg_to_html(self, svg: str, function_extractor = None) -> str:
        """
        Produces an interactive html page from an svg image of a CFG.

        Args:
            svg: the string of the SVG to process
            function_extractor: a FunctionExtractor object containing functions
                                to annotate the graph with.

        Returns:
            HTML string of interactive web page source for the given CFG.
        """

        lines = svg.split("\n")
        page = []

        page.append("""
<html>
<body>
<style>
.node
{
    transition: all 0.05s ease-out;
}
.node:hover
{
    stroke-width: 1.5;
    cursor:pointer
}
.node:hover
ellipse
{
    fill: #EEE;
}
textarea#infobox {
    position: fixed;
    display: block;
    top: 0;
    right: 0;
}

.edge
{
    transition: all 0.05s ease-out;
}
.edge:hover
{
    stroke-width: 2;
    cursor:pointer
}

.dropbutton {
    padding: 10px;
    border: none;
}
.dropbutton:hover, .dropbutton:focus {
    background-color: #777777;
}
.dropdown {
    margin-right: 5px;
    position: fixed;
    top: 5px;
    right: 0px;
}
.dropdown-content {
    background-color: white;
    display: none;
    position: absolute;
    width: 70px;
    box-shadow: 0px 5px 10px 0px rgba(0,0,0,0.2);
    z-index: 1;
}
.dropdown-content a {
    color: black;
    padding: 8px 10px;
    text-decoration: none;
    font-size: 10px;
    display: block;
}

.dropdown-content a:hover { background-color: #f1f1f1; }

.show { display:block; }
</style>
                """)

        for line in lines[3:]:
            page.append(line)

        page.append("""<textarea id="infobox" disabled=true rows=40 cols=50></textarea>""")

        # Create a dropdown list of functions if there are any.
        if function_extractor is not None:
            page.append("""<div class="dropdown">
                <button onclick="showDropdown()" class="dropbutton">Functions</button>
                <div id="func-list" class="dropdown-content">""")

            for i, f in enumerate(function_extractor.functions):
                if f.is_private:
                    page.append('<a id=f_{0} href="javascript:highlightFunction({0})">private #{0}</a>'.format(i))
                else:
                    if f.signature:
                        page.append(
                            '<a id=f_{0} href="javascript:highlightFunction({0})">public {1}</a>'.format(i, f.signature))
                    else:
                        page.append('<a id=f_{0} href="javascript:highlightFunction({0})">fallback</a>'.format(i))
            page.append("</div></div>")

        page.append("""<script>""")

        if function_extractor is not None:
            func_map = {i: [b.ident() for b in f.body]
                        for i, f in enumerate(function_extractor.functions)}
            page.append("var func_map = {};".format(func_map))
            page.append("var highlight = new Array({}).fill(0);".format(len(func_map)))

        page.append("""
// Set info textbox contents to the title of the given element, with line endings replaced suitably.
function setInfoContents(element){
    document.getElementById('infobox').value = element.getAttribute('xlink:title').replace(/\\\\n/g, '\\n');
}

// Make all node anchor tags in the svg clickable.
for (var el of Array.from(document.querySelectorAll(".node a"))) {
    el.setAttribute("onclick", "setInfoContents(this);");
}

// Make all edge anchor tags in the svg clickable.
for (var el of Array.from(document.querySelectorAll(".edge a"))) {
    console.log(el)
    el.setAttribute("onclick", "setInfoContents(this);");
}

const svg = document.querySelector('svg')
const NS = "http://www.w3.org/2000/svg";
const defs = document.createElementNS( NS, "defs" );

// IIFE add filter to svg to allow shadows to be added to nodes within it
(function(){
    defs.innerHTML = makeShadowFilter()
    svg.insertBefore(defs,svg.children[0])
})()

function colorToID(color){
    return color.replace(/[^a-zA-Z0-9]/g,'_')
}

function makeShadowFilter({color = 'black',x = 0,y = 0, blur = 3} = {}){
    return `
    <filter id="filter_${colorToID(color)}" x="-40%" y="-40%" width="250%" height="250%">
    <feGaussianBlur in="SourceAlpha" stdDeviation="${blur}"/>
    <feOffset dx="${x}" dy="${y}" result="offsetblur"/>
    <feFlood flood-color="${color}"/>
    <feComposite in2="offsetblur" operator="in"/>
    <feMerge>
        <feMergeNode/>
        <feMergeNode in="SourceGraphic"/>
    </feMerge>
    </filter>
    `
}

// Shadow toggle functions, with filter caching
function addShadow(el, {color = 'black', x = 0, y = 0, blur = 3}){
    const id = colorToID(color);
    if(!defs.querySelector(`#filter_${id}`)){
    const d = document.createElementNS(NS, 'div');
    d.innerHTML = makeShadowFilter({color, x, y, blur});
    defs.appendChild(d.children[0]);
    }
    el.style.filter = `url(#filter_${id})`
}

function removeShadow(el){
    el.style.filter = ''
}

function hash(n) {
    var str = n + "rainbows" + n + "please" + n;
    var hash = 0;
    for (var i = 0; i < str.length; i++) {
    hash = (((hash << 5) - hash) + str.charCodeAt(i)) | 0;
    }
    return hash > 0 ? hash : -hash;
};

function getColor(n, sat="80%", light="50%") {
    const hue = hash(n) % 360;
    return `hsl(${hue}, ${sat}, ${light})`;
}

// Add shadows to function body nodes, and highlight functions in the dropdown list
function highlightFunction(i) {
    for (var n of Array.from(document.querySelectorAll(".node ellipse"))) {
    removeShadow(n);
    }

    highlight[i] = !highlight[i];
    const entry = document.querySelector(`.dropdown-content a[id='f_${i}']`)
    if (entry.style.backgroundColor) {
    entry.style.backgroundColor = null;
    } else {
    entry.style.backgroundColor = getColor(i, "60%", "90%");
    }

    for (var j = 0; j < highlight.length; j++) {
    if (highlight[j]) {
        const col = getColor(j);
        for (var id of func_map[j]) {
        var n = document.querySelector(`.node[id='${id}'] ellipse`);
        addShadow(n, {color:`${col}`});
        }
    }
    }
}

// Show the dropdown elements when it's clicked.
function showDropdown() {
    document.getElementById("func-list").classList.toggle("show");
}
window.onclick = function(event) {
    if (!event.target.matches('.dropbutton')) {
    var items = Array.from(document.getElementsByClassName("dropdown-content"));
    for (var item of items) {
        item.classList.remove('show');
    }
    }
}
</script>
</html>
</body>
                """)
        return "\n".join(page)