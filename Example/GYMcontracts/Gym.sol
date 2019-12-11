pragma solidity ^0.4.25;

import "./token/StandardToken.sol";
import "./ownership/Ownable.sol";

contract Gym is StandardToken, Ownable {
    string public name;
    string public symbol;

    event Redeem(address indexed from, address indexed to, uint256 value, string info);
    event Transfer(address indexed from, address indexed to, uint256 value);
    event AddSupply(uint256 amount);
    event Burn(uint256 amount);

    constructor(string _name,string _symbol, uint256 _amount) public {
        totalSupply = _amount;
        balances[owner] = totalSupply;
        name = _name;
        symbol = _symbol;
    }

    function transfer(address _to, uint256 _value) public returns (bool) {
        return super.transfer(_to, _value);
    }

    // @dev 核銷
    // @pragma _value token數量
    // @pragma _info 核銷資訊：商品名稱、數量
    function redeem(uint256 _value, address _store, string _info) public returns (bool) {
        emit Redeem(msg.sender, _store, _value, _info);
        return super.transfer(_store, _value);
    }

    // @dev 補發行
    // @pragma _amount 補發行數量
    function addSupply(uint256 _amount) onlyOwner public returns (bool){
        totalSupply = totalSupply.add(_amount);
        balances[owner] = balances[owner].add(_amount);
        emit AddSupply(_amount);
    }

    // @dev burn
    // @pragma _amount 從owner手上燒掉
    function burn(uint256 _amount) onlyOwner public returns (bool){
        balances[owner] = balances[owner].sub(_amount);
        totalSupply = totalSupply.sub(_amount);
        emit Burn(_amount);
    }
}