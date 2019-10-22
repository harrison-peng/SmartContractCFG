# SmartContractCFG

SmartContractCFG consists of a series of analysis to detect the gas vulnerability. First, it converts the source code or byte code into opcodes. Based on the opcodes, we constrcut the control flow graph. Then, we do the symbolic execution to walk through all the path and find the maximum gas consumption. It will find if the maximum consumption is excceed the gas limit of the user.

## Usage

Install with docker as follows:

```
$ docker build -t smart_contract_cfg .
```

Analyze the example contract:

```
$ python main.py -s -code Example/SIXcontracts/Bank.sol -gas 5000
```

Output control flow graph is in `cfg` directory, result is in `result` directory.

Further invocation options are detailed when the `--help` flag is supplied:

```
python main.py --help
```