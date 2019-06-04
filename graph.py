import graphviz as gv
import functools
import global_vars


def graph_detail(nodes, edges):
    count = 0
    for n in nodes:
        count += len(n['ins'])
    return len(nodes), len(edges), count


def create_graph_old(n, e, dir_name, row_id):
    digraph = functools.partial(gv.Digraph, format='svg')
    g = add_edges(add_nodes(digraph(), n), e)
    filename = 'img/%s/%s' % (dir_name, row_id)
    g.render(filename=filename)
    return g


def create_graph(nodes, edges, dir_name, row_id):
    cfg_nodes = list()
    cfg_edges = list()
    for node in nodes:
        content = '[ADDRESS: %s]\n\n' % node['addr']

        for ins in node['ins']:
            content += '%s\n' % ins

        if node['gas'] is not None:
            if len(str(node['gas'])) < 100:
                content += '\nGAS: %s\n' % str(node['gas'])
            else:
                content += '\nGAS:\n%s\n' % str(node['gas'])
        if node['state']:
            state_content = ''
            for idx, s in enumerate(node['state']):
                if idx <= 3:
                    state_content += '[Path Label: %s,\n' % str(s['Path Label'])
                    state_content += 'stack: {'
                    for st in s['Stack']:
                        if len(str(s['Stack'][st])) < 100:
                            state_content += '%s: %s,\n' % (str(st), str(s['Stack'][st]).replace('\n', '').replace(' ', ''))
                        else:
                            state_content += '%s: %s...,\n' % (str(st), str(s['Stack'][st])[:50].replace('\n', '').replace(' ', ''))
                    if state_content[-2:] == ',\n':
                        state_content = state_content[:-2]
                    state_content += '},\nMemory: {'
                    for mem in s['Memory']:
                        if len(str(s['Memory'][mem])) < 100 and len(str(mem)) < 100:
                            state_content += '%s: %s,\n' % (str(mem), str(s['Memory'][mem]).replace('\n', '').replace(' ', ''))
                        else:
                            if len(str(mem)) > 100:
                                s1 = str(mem)[:50].replace('\n', '').replace(' ', '')
                            else:
                                s1 = str(mem).replace('\n', '').replace(' ', '')
                            if len(str(s['Memory'][mem])) > 100:
                                s2 = str(s['Memory'][mem])[:50].replace('\n', '').replace(' ', '')
                            else:
                                s2 = str(s['Memory'][mem]).replace('\n', '').replace(' ', '')
                            state_content += '%s: %s...,\n' % (s1, s2)
                    if state_content[-2:] == ',\n':
                        state_content = state_content[:-2]
                    state_content += '},\nStorage: {'
                    for sto in s['Storage']:
                        if len(str(s['Storage'][sto])) < 100 and len(str(sto)) < 100:
                            state_content += '%s: %s,\n' % (str(sto), str(s['Storage'][sto]).replace('\n', '').replace(' ', ''))
                        else:
                            if len(str(sto)) > 100:
                                s1 = str(sto)[:50].replace('\n', '').replace(' ', '')
                            else:
                                s1 = str(sto).replace('\n', '').replace(' ', '')
                            if len(str(s['Storage'][sto])) > 100:
                                s2 = str(s['Storage'][sto])[:50].replace('\n', '').replace(' ', '')
                            else:
                                s2 = str(s['Storage'][sto]).replace('\n', '').replace(' ', '')
                            state_content += '%s: %s...,\n' % (s1, s2)
                    if state_content[-2:] == ',\n':
                        state_content = state_content[:-2]
                    state_content += '},\n\n'

            state_content = state_content[:-3] + ']'
            state_content = '\nSTATE:\n%s' % state_content
            content += state_content

            # if node['addr'] == 5890:
            #     print(content)

        if node['ins'][-1].split(' ')[1] in ['STOP', 'REVERT', 'INVALID', 'RETURN']:
            cfg_nodes.append((str(node['addr']), {'label': content, 'shape': 'box', 'color': 'red'}))
        else:
            cfg_nodes.append((str(node['addr']), {'label': content, 'shape': 'box'}))

    for edge in edges:
        if edge[1]['label']:
            content = 'Path Constraint:\n['
            for idx, constraint in enumerate(edge[1]['label']):
                cons_str = str(constraint).replace('\n', '').replace(' ', '')
                if idx == len(edge[1]['label']) - 1:
                    content += '%s]' % cons_str
                else:
                    content += '%s,\n' % cons_str
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
