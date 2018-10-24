pragma solidity ^0.4.23;

import "./Owned.sol";

contract Account is Owned {
    /** events */
    event Forwarded (address indexed destination, uint value, bytes data);
    event Received (address indexed sender, uint value);

    function () public payable {
        emit Received(msg.sender, msg.value);
    }

    /** methods */
    function forward (address destination, uint value, bytes data) public onlyOwner {
        // require(destination.call.value(value)(data));
        require(executeCall(destination, value, data));
        emit Forwarded(destination, value, data);
    }

    function deployCode (bytes bytecode) public onlyOwner returns (address deployedAddress) {
        assembly {
            deployedAddress := create(0, add(bytecode, 0x20), mload(bytecode))
            // jumpi(invalidJumpLabel, iszero(extcodesize(deployedAddress))) // jumps if no code at addresses
        }
        emit Forwarded(address(0), 0, bytecode);
    }

    function executeCall(address to, uint256 value, bytes data) internal returns (bool success) {
        // copied from GnosisSafe
        // https://github.com/gnosis/gnosis-safe-contracts/blob/master/contracts/GnosisSafe.sol
        assembly {
            success := call(gas, to, value, add(data, 0x20), mload(data), 0, 0)
        }
    }
}
