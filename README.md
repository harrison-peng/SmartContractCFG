# SmartContractCFG

SmartContractCFG consists of a series of analysis to detect the gas vulnerability. First, it converts the source code or byte code into opcodes. Based on the opcodes, we constrcut the control flow graph. Then, we do the symbolic execution to walk through all the path and find the maximum gas consumption. It will find if the maximum consumption is excceed the gas limit of the user.

## Usage

Install with docker as follows:

```bash
docker build -t smart_contract_cfg .
```

Analyze the example contract:

```bash
python main.py -s -code Example/SIXcontracts/Bank.sol
```

Output control flow graph and result are in `result` directory if the output directory is not specified. The ourput directory can be specified with `-o` command.

Further invocation options are detailed when the `--help` flag is supplied:

```bash
python main.py --help
```
