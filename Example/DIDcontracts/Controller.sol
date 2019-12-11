pragma solidity ^0.4.25;

import "./Owned.sol";
import "./MetaAccount.sol";

contract Controller is Owned {
    address public metaAccount;
    mapping(address => address[]) public keysOf;

    /** events */
    event AccountCreated (address account);
    event SetKeys (address account, address[] keys);
    event DeployCode(address sender, address deployedAddress);

    /** methods */
    function setMetaAccount (address newMetaAccount) public {
        require(metaAccount != newMetaAccount);
        metaAccount = newMetaAccount;
    }

    // todo: 升級 Controller 時，替換 metaAccount 的 owner

    function accountExisted (address account) public view returns (bool) {
        return keysOf[account].length > 0;
    }

    /** create account */
    function signup (address key, bytes accountByteCode) public returns (address accountAddress) {
        require(metaAccount != address(0));
        address account = MetaAccount(metaAccount).createAccount(accountByteCode);
        // keysOf[account] = [key];
        address[] memory keys = new address[](1);
        keys[0] = key;
        setKeys(account, keys);
        emit AccountCreated(account);
        return account;
    }

    function setKeys (address account, address[] keys) public {
        require(keys.length > 0);
        require(isOwner(msg.sender) || hasKey(account, msg.sender));
        keysOf[account] = keys;
        emit SetKeys(account, keys);
    }

    function getKeys (address account) public view returns (address[]) {
        return keysOf[account];
    }

    function hasKey (address account, address key) public view returns (bool) {
        address[] memory keys = getKeys(account);
        for (uint i = 0; i < keys.length; i++) {
            if (keys[i] == key) {
                return true;
            }
        }
        return false;
    }

    /** 轉發交易 */
    function forward (address from, address key, address destination, uint value, bytes data) public {
        require(hasKey(from, key));
        MetaAccount(metaAccount).forward(from, destination, value, data);
    }

    function deployCode (address from, address key, bytes bytecode) public returns (address) {
        require(hasKey(from, key));
        address deployedAddress = MetaAccount(metaAccount).deployCode(from, bytecode);
        emit DeployCode(msg.sender, deployedAddress);
        return deployedAddress;
    }
}
