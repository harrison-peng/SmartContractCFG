import psycopg2
import sys
import pyperclip


def connect_to_db():
    try:
        conn = psycopg2.connect(database="smartcontract", user="postgres", password="soslab5566", host="140.119.19.77", port="5432")
        return conn
    except Exception as ex:
        print(" --- Unable to connect to the database. ---")
        print('Error: ', ex)
        sys.exit(0)


def load_source_code_from_db():
    conn = connect_to_db()
    cur = conn.cursor()

    try:
        cur.execute('''SELECT id, source_code FROM contract
        WHERE source_code <> '' AND status = 'PENDING' ORDER BY id;''')
        result = cur.fetchall()
    except Exception as ex:
        print('--- Failed to select source code from database. ---')
        print('Error: ', ex)
        conn.close()
        sys.exit(0)

    return result


def load_assembly_from_db(mode, contract_id):
    conn = connect_to_db()
    cur = conn.cursor()

    if mode == 0:
        try:
            print('--- Querying contract assembly code from DB ---')
            cur.execute('''
            SELECT opcode_data, contract_name, id
            FROM preprocessing
            ORDER BY id;
            ''')
            result = cur.fetchall()
        except Exception as ex:
            print('--- Failed to query assembly from database. ---')
            print('Error: ', ex)
            sys.exit(0)
    else:
        try:
            print('--- Querying contract assembly code from DB ---')
            cur.execute('''
            SELECT opcode_data, contract_name, id
            FROM preprocessing
            WHERE contract_id = '{}'
            ORDER BY id;
            '''.format(contract_id))
            result = cur.fetchall()
        except Exception as ex:
            print('--- Failed to query assembly from database. ---')
            print('Error: ', ex)
            sys.exit(0)

    return result


def update_source_code_to_db(code, test_mode):
    if not test_mode:
        conn = connect_to_db()
        cur = conn.cursor()
        src = code.replace("'", "''")

        try:
            cur.execute('''
                        SELECT id FROM contract
                        WHERE source_code = '{}';
                        '''.format(src))

            id_list = cur.fetchall()
            if len(id_list) == 0:
                print('[INFO] Insert source code to DB')
                cur.execute('''
                            INSERT INTO contract (source_code, status)
                            VALUES ('{}', 'PENDING');
                            '''.format(src))
                conn.commit()
            else:
                print('[INFO] Source code is already in DB')

            # delete rebundant source code in DB
            if len(id_list) > 1:
                print('[INFO] Delete rebundant source code in DB')
                for id in enumerate(id_list):
                    if id[0] > 0:
                        cur.execute('''
                                        DELETE FROM contract
                                        WHERE id='{}';
                                    '''.format(id[1][0]))
                conn.commit()

            cur.execute('''
                        SELECT id FROM contract
                        WHERE source_code = '{}';
                        '''.format(src))

            result = cur.fetchall()
        except Exception as ex:
            print('[FAIL] Failed to insert source code to database. ---')
            print('Error: ', ex)
            sys.exit(0)

        return result


def update_status_to_db(status, table_name, contract_id, test_mode):
    if not test_mode:
        conn = connect_to_db()
        cur = conn.cursor()

        try:
            print('[INFO] Update contract analysis status.')
            cur.execute('''
                            UPDATE {}
                            SET status = '{}'
                            WHERE id='{}';
                            '''.format(table_name, status, contract_id))
            conn.commit()
        except Exception as ex:
            print('[FAIL] Failed to update analysis status to database.')
            print('Error: ', ex)
            sys.exit(0)


def update_analysis_result_to_db(db_status, result, row_id, test_mode):
    if not test_mode:
        conn = connect_to_db()
        cur = conn.cursor()

        try:
            print('\t--- Updating contract analysis result to DB, id: {} ---'.format(row_id))
            cur.execute('''
                UPDATE contract
                SET status = '{}', analysis_result = '{}'
                WHERE id='{}';
                '''.format(db_status, result, row_id))
            conn.commit()
            if result:
                print('\t--- Updating cycle information to DB, id: {} ---'.format(row_id))
                cur.execute('''
                            INSERT INTO cycle_contract (contract_id)
                            VALUES ('{}');
                            '''.format(row_id))
                conn.commit()
        except Exception as ex:
            print('\t--- Failed to update result to database. ---')
            print('Error: ', ex)
            sys.exit(0)


def update_crawling_to_db(conn, row_id, input_code):
    code_origin = pyperclip.paste()
    assembly_code = code_origin.replace("'", "''")

    cur = conn.cursor()

    if code_origin == input_code:
        try:
            cur.execute('''UPDATE contract SET status='{}' WHERE id='{}';'''.format('COMPILE_ERROR',
                                                                                    row_id))
            conn.commit()
            print('''\t--- Update id {} status '{}' to database. ---'''.format(row_id, 'COMPILE_ERROR'))
        except Exception as ex:
            print('\t--- Failed to update to database. ---')
            print('Error: ', ex)
            sys.exit(0)
    else:
        try:
            cur.execute('''
            UPDATE contract
            SET assembly='{}', status='{}'
            WHERE id='{}';
            '''.format(assembly_code,
                       'GOT_ASSEMBLY',
                       row_id))
            conn.commit()
            print('\t--- Update id {} assembly to database. ---'.format(row_id))
        except Exception as ex:
            print('\t--- Failed to update assembly code to database. ---')
            print('Error: ', ex)
            sys.exit(0)


def update_assembly_to_db(op, op_pre, row_id, json_name, test_mode):
    if not test_mode:
        conn = connect_to_db()
        cur = conn.cursor()

        try:
            print(json_name)
            cur.execute('''
                        SELECT id FROM preprocessing
                        WHERE contract_name='{}';
                        '''.format(json_name))
            id_list = cur.fetchall()

            if len(id_list) == 0:
                cur.execute('''
                                INSERT INTO preprocessing (contract_id, contract_name, opcode_pre, opcode_data)
                                VALUES ('{}', '{}', '{}', '{}');
                                '''.format(row_id, json_name, op_pre, op))
                conn.commit()
            else:
                print('[INFO] Assembly is already in DB')
                cur.execute('''
                            UPDATE preprocessing
                            SET opcode_pre = '{}', opcode_data = '{}'
                            WHERE contract_name='{}'
                            '''.format(op_pre, op, json_name))

            # delete rebundant source code in DB
            if len(id_list) > 1:
                print('[INFO] Delete rebundant source code in DB')
                for id in enumerate(id_list):
                    if id[0] > 0:
                        cur.execute('''
                                    DELETE FROM preprocessing
                                    WHERE id='{}';
                                    '''.format(id[1][0]))
                conn.commit()

            print('\t[INFO] Update assembly of contract id {}  to database.'.format(row_id))
        except Exception as ex:
            print('\t[FAIL] Failed to update assembly to database.')
            print('Error: ', ex)
            sys.exit(0)


def update_opcode_to_db(column_name, input_code, row_id, test_mode):
    if not test_mode:
        conn = connect_to_db()
        cur = conn.cursor()

        try:
            cur.execute('''UPDATE preprocessing SET '{}'='{}' WHERE contract_id='{}';'''.format(column_name, input_code, row_id))
            conn.commit()
            print('\t--- Update runtime opcode to database. ---')
        except Exception as ex:
            print('\t--- Failed to update runtime opcode to database. ---')
            print('Error: ', ex)
            sys.exit(0)


def update_cfg_info_to_db(row_id, graph, test_mode):
    if not test_mode:
        conn = connect_to_db()
        cur = conn.cursor()
        # node = node.replace("'", "''")

        try:
            print('\t[INFO] Updating cfg info to DB, id: {}'.format(row_id))
            cur.execute('''
            INSERT INTO cfg (preproc_id, cfg, cycle)
            VALUES ('{}', '{}', 'N');
            '''.format(row_id, graph))
            conn.commit()
        except Exception as ex:
            print('\t--- Failed to update result to database. ---')
            print('Error: ', ex)
            sys.exit(0)


def update_cycle_info_to_db(row_id, test_mode, cfg, code, opcode, graph, node, edge, count, op_with_src):
    if not test_mode:
        conn = connect_to_db()
        cur = conn.cursor()

        try:
            print('\t--- Updating cycle info to DB, id: {} ---'.format(row_id))
            cur.execute('''
                UPDATE cycle_contract
                SET cycle_cfg = '{}', cycle_code = '{}', cycle_opcode = '{}',
                 graph_count = {}, cycle_node_count = {}, cycle_edge_count = {}, cycle_count = {}, contract_assembly = '{}'
                WHERE contract_id = '{}';
                '''.format(cfg, code, opcode, graph, node, edge, count, op_with_src, row_id))
            conn.commit()
        except Exception as ex:
            print('\t--- Failed to update result to database. ---')
            print('Error: ', ex)
            sys.exit(0)


def update_condition_info_to_db(row_id, test_mode, gas_total, num, var):
    if not test_mode:
        conn = connect_to_db()
        cur = conn.cursor()

        try:
            print('\t--- Updating condition info to DB, id: {} ---'.format(row_id))
            cur.execute('''INSERT INTO loop_gas_consume(contract_id, gas, node)
                VALUES('{}', '{}', {});'''.format(row_id, gas_total, (num, var)))
            conn.commit()
        except Exception as ex:
            print('\t--- Failed to update result to database. ---')
            print('Error: ', ex)
            sys.exit(0)
