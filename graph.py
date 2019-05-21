import graphviz as gv
import functools
import global_vars


def graph_detail(nodes, edges):
    count = 0

    for n in nodes:
        label = n[1].get('label')
        label_content = label.split('\n')
        for l in label_content:
            if 'Stack' in l or 'Gas' in l or 'PC' in l:
                break
            elif l == '' or (l.startswith('[TAG:') and l.endswith(']')):
                continue
            else:
                count += 1
    return len(nodes), len(edges), count


def create_graph(n, e, dir_name, row_id):
    digraph = functools.partial(gv.Digraph, format='svg')
    g = add_edges(add_nodes(digraph(), n), e)
    filename = 'img/{}/{}'.format(dir_name, row_id)
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
