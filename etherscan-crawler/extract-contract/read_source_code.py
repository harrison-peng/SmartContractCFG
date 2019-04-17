import json

with open('source_code.json') as f:
    data_li = json.load(f)

for data in data_li:
    code = data['result'][0]['SourceCode']
    name = data['result'][0]['ContractName']
    valid = data['result'][0]['ABI']

    if valid != 'Contract source code not verified':
        print('[Contract]:', name)
        with open('contracts/%s.sol' % name, 'w') as f:
            f.write(code)