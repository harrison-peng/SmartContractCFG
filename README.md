# SmartContractCFG

SmartContractCFG consists of a series of analysis to detect the gas vulnerability. First, it converts the source code or byte code into opcodes. Based on the opcodes, we constrcut the control flow graph. Then, we do the symbolic execution to walk through all the path and find the maximum gas consumption. It will find if the maximum consumption is excceed the gas limit of the user.

## Requirements

- [Python 3.6+](https://www.python.org/downloads/)
- [go-ethereum](https://github.com/ethereum/go-ethereum)
- [solidity](https://github.com/ethereum/solidity)
- [graphviz](https://www.graphviz.org/)

## Quickstart

Install with docker as follows:

```bash
docker build -t smart_contract_cfg .
```

Run the docker contianer:

```bash
docker run -it --rm smart_contract_cfg
```

Analyze the example contract:

```bash
python3 main.py -s -code Example/SIXcontracts/Bank.sol
```

Output control flow graph and result are in `result` directory if the result directory is not specified. The result directory can be specified with `-o` command.

Further invocation options are detailed when the `--help` flag is supplied:

```bash
python3 main.py --help
```

NOTE: Docker only supports solidity^0.4.25. For other versions of solidity, you can modify in Dockerfile.
