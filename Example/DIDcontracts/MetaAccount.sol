pragma solidity ^0.4.25;

import "./Owned.sol";
import "./Account.sol";

contract MetaAccount is Owned {
    function createAccount (bytes bytecode) public onlyOwner returns (address account) {
        // todo: event
        assembly {
            account := create(0, add(bytecode, 0x20), mload(bytecode))
            // jumpi(invalidJumpLabel, iszero(extcodesize(deployedAddress))) // jumps if no code at addresses
        }
    }

    /** 轉發交易 */
    function forward (address from, address destination, uint value, bytes data) public onlyOwner {
        Account(from).forward(destination, value, data);
    }

    function deployCode (address from, bytes bytecode) public onlyOwner returns (address deployedAddress) {
        return Account(from).deployCode(bytecode);
    }
}
