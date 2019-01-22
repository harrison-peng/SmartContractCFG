import re
import sys
from opcode_table import *

nodes = []
edges = []

def cfg_construction(opcode_data, contract_name):
    global nodes
    global edges

    nodes = []
    edges = []

    print('''[INFO] Constructing CFG for contract '{}'. '''.format(contract_name))

    opcode_list = opcode_data.split('\n')
    for i in range(len(opcode_list)):
        opcode_list[i] = (i, opcode_list[i])

    tag_num = 0
    stack_sum = 0
    tag_line_dict = dict()
    stacks = list()

    for _ in range(10):
        cfg_implement(opcode_list, 0, stacks, tag_num, stack_sum, tag_line_dict)

    return nodes, edges

def cfg_implement(opcode_list, line, stacks, tag_num, stack_sum, tag_line_dict):
    global nodes
    global edges

    segment_ins = ['tag', 'JUMP', 'JUMPI', 'STOP', 'REVERT', 'INVALID', 'RETURN']

    node_content = ''
    prev_ins = ''
    prev_tag = 0
    from_jumpi = False
    push_tag = list()
    left_push_tag = list()

    opcode_sublist = opcode_list[line:]
    for index, line in opcode_sublist:
        s = line.rstrip().split(' ')

        if s[0] == '':
            continue
        elif s[0] in segment_ins:
            if s[0] == 'tag':
                tag_line_dict.update({int(s[1]): index})
                if node_content == '':
                    tag_num = int(s[1])
                    node_content += str(index) + ': ' + line.rstrip() + '\n'

                    if len(left_push_tag) > 0 and left_push_tag[-1][1] == prev_tag:
                        left_push_tag.pop()
                        left_push_tag.append((index, tag_num))
                else:
                    node_content += 'Stack Sum: ' + str(stack_sum)
                    node_exist = is_nodes_exist(tag_num)
                    if not node_exist:
                        node_content = '[TAG: %d]\n\n' % tag_num + node_content
                        nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))

                    if from_jumpi:
                        edge_exist = is_edge_exist(prev_tag, tag_num)
                        if not edge_exist:
                            edges.append(((str(prev_tag), str(tag_num)),
                                          {'label': '',
                                           'color': 'blue'}))
                        from_jumpi = False

                    edge_exist = is_edge_exist(tag_num, int(s[1]))
                    if not edge_exist and prev_ins[0] != 'JUMPDEST':
                        edges.append(((str(tag_num), s[1]),
                                      {'label': '',
                                       'color': 'blue'}))

                    for push_stack in stacks:
                        if push_stack[-1][1] == tag_num:
                            push_stack.pop()
                            push_stack.append((index, int(s[1])))

                    stack_sum = 0
                    node_content = ''
                    node_content += str(index) + ': ' + line.rstrip() + '\n'
                    prev_tag = tag_num
                    tag_num = int(s[1])

                    if push_tag:
                        all_exist = True
                        for tag in push_tag:
                            if tag[1] not in tag_line_dict:
                                all_exist = False
                        if all_exist:
                            for tag in push_tag:
                                left_push_tag.append((tag_line_dict[tag[1]], tag[1]))
                            left_push_tag.append((index, tag_num))
                    push_tag = list()
            else:
                if from_jumpi:
                    edge_exist = is_edge_exist(prev_tag, tag_num)
                    if not edge_exist:
                        edges.append(((str(prev_tag), str(tag_num)),
                                      {'label': '',
                                       'color': 'blue'}))
                    from_jumpi = False

                if s[0] == 'JUMP' and len(s) == 1 and len(prev_ins) > 1:
                    push_stack = list()
                    for tag in push_tag:
                        push_stack.append(tag)
                    stacks.append(push_stack)

                    stack_sum -= 1
                    node_content += str(index) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum)
                    node_exist = is_nodes_exist(tag_num)
                    if not node_exist:
                        node_content = '[TAG: %d]\n\n' % tag_num + node_content
                        nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))

                    jump_tag = int(prev_ins[2])
                    edge_exist = is_edge_exist(tag_num, jump_tag)
                    if not edge_exist:
                        edges.append(((str(tag_num), str(jump_tag)),
                                      {'label': '',
                                       'color': 'blue'}))
                    push_tag = list()
                    node_content = ''
                elif s[0] == 'JUMPI':
                    stack_sum -= 2
                    node_content += str(index) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum)
                    node_exist = is_nodes_exist(tag_num)
                    if not node_exist:
                        node_content = '[TAG: %d]\n\n' % tag_num + node_content
                        nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))

                    jump_tag = int(prev_ins[2])
                    edge_exist = is_edge_exist(tag_num, jump_tag)
                    if not edge_exist:
                        edges.append(((str(tag_num), str(jump_tag)),
                                      {'label': '',
                                       'color': 'blue'}))

                    for push_stack in stacks:
                        if tag_num == push_stack[-1][1]:
                            push_stack.pop()
                            for tag in push_tag:
                                push_stack.append(tag)

                    node_content = ''
                    push_tag = list()
                    prev_tag = tag_num
                    from_jumpi = True
                elif len(s) > 1 and s[0] == 'JUMP' and s[1] == '[in]':
                    for push_stack in stacks:
                        if push_stack[-1][1] == tag_num:
                            push_stack.pop()
                            for tag in push_tag:
                                push_stack.append(tag)

                    stack_sum -= 1
                    node_content += str(index) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum)
                    node_exist = is_nodes_exist(tag_num)
                    if not node_exist:
                        node_content = '[TAG: %d]\n\n' % tag_num + node_content
                        nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))
                    edge_exist = is_edge_exist(tag_num, push_tag[-1][1])
                    if not edge_exist:
                        edges.append(((str(tag_num), str(push_tag[-1][1])),
                                      {'label': '',
                                       'color': 'blue'}))

                    node_content = ''
                    push_tag = list()
                    prev_tag = tag_num

                elif len(s) > 1 and s[0] == 'JUMP' and s[1] == '[out]':
                    find_out = False
                    jump_to_line = sys.maxsize
                    jump_to_tag = -1
                    for push_stack in stacks:
                        if len(push_stack) > 1 and push_stack[-1][1] == tag_num:
                            jump_from = push_stack.pop()[1]
                            jump_to = push_stack[-1][1]
                            edge_exist = is_edge_exist(jump_from, jump_to)
                            if not edge_exist:
                                find_out = True
                                if tag_line_dict[push_stack[-1][1]] < jump_to_line:
                                    jump_to_line = tag_line_dict[push_stack[-1][1]]
                                    jump_to_tag = push_stack[-1][1]
                                edges.append(((str(jump_from), str(jump_to)),
                                              {'label': '',
                                               'color': 'blue'}))
                    if find_out:
                        return cfg_implement(opcode_list, jump_to_line,
                                                 stacks, jump_to_tag,
                                                 stack_sum, tag_line_dict)

                    stack_sum -= 1
                    node_content += str(index) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum)
                    node_exist = is_nodes_exist(tag_num)
                    if not node_exist:
                        node_content = '[TAG: %d]\n\n' % tag_num + node_content
                        nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))

                    node_content = ''
                    push_tag = list()
                    prev_tag = tag_num
                else:
                    if len(s) == 1 and s[0] == 'JUMP':
                        if len(left_push_tag) > 0 and left_push_tag[-1][1] == tag_num:
                            left_push_tag.pop()
                            jump_to = left_push_tag.pop()
                            edge_exist = is_edge_exist(tag_num, jump_to[1])

                            for push_stack in stacks:
                                if len(push_stack) > 0 and push_stack[-1][1] == tag_num:
                                    push_stack.pop()
                                    push_stack.append(jump_to)

                            if not edge_exist:
                                edges.append(((str(tag_num), str(jump_to[1])),
                                              {'label': '',
                                               'color': 'blue'}))
                                return cfg_implement(opcode_list, jump_to[0],
                                                     stacks, jump_to[1],
                                                     stack_sum, tag_line_dict)

                    if s[0] in ['REVERT', 'RETURN']:
                        stack_sum -= 2
                    node_content += str(index) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum)
                    node_exist = is_nodes_exist(tag_num)
                    if not node_exist:
                        node_content = '[TAG: %d]\n\n' % tag_num + node_content
                        if s[0] in ['REVERT', 'RETURN', 'STOP', 'INVALID']:
                            nodes.append((str(tag_num), {'label': node_content, 'shape': 'box', 'color': 'red'}))
                        else:
                            nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))
                    node_content = ''
                    push_tag = list()
                tag_num = int(tag_num) + 10000
                stack_sum = 0
        else:
            if 'LOG' in s[0]:
                log_number = s[0].split('LOG')[1]
                stack_sum -= int(log_number) + 2
            elif 'PUSH' in s and '[tag]' in s:
                push_tag.append((index, int(s[2])))
                stack_sum += 1
            else:
                instruction = re.sub(r'\d+', '', str(s[0]))
                if instruction == 'PUSHLIB':
                    instruction = 'PUSH'
                tmp = opcode[instruction]
                stack_sum += tmp[1] - tmp[0]

            node_content += str(index) + ': ' + line.rstrip() + '\n'
        prev_ins = s


def is_edge_exist(from_tag, to_tag):
    global edges

    for edge in edges:
        jump_pair = list(map(int, edge[0]))
        if from_tag == jump_pair[0] and to_tag == jump_pair[1]:
            return True
    return False


def is_nodes_exist(tag):
    global nodes

    for node in nodes:
        tag_in_node = int(node[0])
        if tag_in_node == tag:
            return True
    return False