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

    def __init__(self):
        self.nodes = list()
        self.edges = list()
        self.opcodes = list()
        self.graph = None
        self.count = 0

    def build_cfg(self, opcode_data: str) -> None:
        logging.info('Constructing CFG...')

        opcode_list = opcode_data.split('\n')
        for i in range(len(opcode_list)):
            code_set = opcode_list[i].rstrip().split(' ')
            pc = int(code_set[0].replace(':', ''))
            s = code_set[1:]
            opcode = Opcode(pc, s[0], None) if len(s) == 1 else Opcode(pc, s[0], s[1])
            self.opcodes.append(opcode)

        push_value = ''
        pre_opcode = None
        start_idx = 0
        start_pc = 0
        for index, opcode in enumerate(self.opcodes):
            if opcode.name == 'JUMPDEST' and start_idx != index:
                content = self.opcodes[start_idx:index]
                node = Node(start_pc, content)
                self.nodes.append(node)
                start_idx = index
                start_pc = opcode.pc
            elif opcode.name.startswith('PUSH'):
                push_value = opcode.value
            elif opcode.name == 'JUMP' and pre_opcode.name.startswith('PUSH'):
                content = self.opcodes[start_idx:index+1]
                node = Node(start_pc, content)
                self.nodes.append(node)
                edge = Edge(start_pc, int(pre_opcode.value, 16))
                self.edges.append(edge)
                start_idx = index + 1
                start_pc = opcode.pc + 1
            elif opcode.name == 'JUMPI':
                content = self.opcodes[start_idx:index+1]
                node = Node(start_pc, content)
                self.nodes.append(node)
                edge = Edge(start_pc, int(pre_opcode.value, 16))
                self.edges.append(edge)
                edge = Edge(start_pc, opcode.pc + 1)
                self.edges.append(edge)
                start_idx = index + 1
                start_pc = opcode.pc + 1
            elif opcode.name in ['STOP', 'RETURN', 'REVERT', 'INVALID', 'SELFDESTRUCT']:
                content = self.opcodes[start_idx:index+1]
                node = Node(start_pc, content)
                if opcode.name == 'RETURN':
                    node.set_color('green')
                elif opcode.name == 'STOP':
                    node.set_color('blue')
                else:
                    node.set_color('red')
                self.nodes.append(node)
                start_idx = index + 1
                start_pc = opcode.pc + 1
            pre_opcode = opcode

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