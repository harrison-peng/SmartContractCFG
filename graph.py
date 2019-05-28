import graphviz as gv
import functools
import global_vars


def graph_detail(nodes, edges):
    count = 0
    for n in nodes:
        count += len(n['ins'])
    return len(nodes), len(edges), count


def create_graph(n, e, dir_name, row_id):
    digraph = functools.partial(gv.Digraph, format='svg')
    g = add_edges(add_nodes(digraph(), n), e)
    filename = 'img/%s/%s' % (dir_name, row_id)
    g.render(filename=filename)
    return g


def create_graph_new(nodes, edges, dir_name, row_id):
    cfg_nodes = list()
    cfg_edges = list()
    for node in nodes:
        content = '[ADDRESS: %s]\n\n' % node['addr']

        for ins in node['ins']:
            content += '%s\n' % ins

        if node['gas'] is not None:
            content += '\nGAS:\n%s\n' % str(node['gas'])
        if node['state']:
            content += '\nSTATE:\n%s' % node['state']
        content = content\
            .replace("'Stack", "\n'Stack")\
            .replace("'Memory", "\n'Memory")\
            .replace("'Storage", "\n'Storage")\
            .replace('}},', '}},\n')

        if node['ins'][-1].split(' ')[1] in ['STOP', 'REVERT', 'INVALID', 'RETURN']:
            cfg_nodes.append((str(node['addr']), {'label': content, 'shape': 'box', 'color': 'red'}))
        else:
            cfg_nodes.append((str(node['addr']), {'label': content, 'shape': 'box'}))

    for edge in edges:
        if edge[1]['label']:
            content = 'Path Constraint:\n['

            for constraint in edge[1]['label']:
                content += '%s,\n' % constraint
            content = content[:-2] + ']'
        else:
            content = ''
        cfg_edges.append((edge[0], {'label': content, 'color': edge[1]['color']}))

    digraph = functools.partial(gv.Digraph, format='svg')
    g = add_edges(add_nodes(digraph(), cfg_nodes), cfg_edges)
    filename = 'cfg/%s/%s' % (dir_name, row_id)
    g.render(filename=filename)
    return g


def add_nodes(graph, nodes):
    for n in nodes:
        if isinstance(n, tuple):
            graph.node(n[0], **n[1])
        else:
            graph.node(n)
    return graph


def add_edges(graph, edges):
    for e in edges:
        if isinstance(e[0], tuple):
            graph.edge(*e[0], **e[1])
        else:
            graph.edge(*e)
    return graph


def node_add_gas_sum(nodes):
    for key, val in global_vars.get_final_gas().items():
        for n in nodes:
            if n[0] == str(key):
                n[1]['label'] += '\n\nGas Sum: %s' % val
    return nodes
