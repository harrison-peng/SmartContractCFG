pragma solidity ^0.4.25;

contract Exchange {
    mapping (address => mapping (address => uint256)) public exchangeRate;

    function setExchangeRate(address _partnerA, address _partnerB, uint256 _rate) public returns (bool){
        exchangeRate[_partnerA][_partnerB] = _rate;
    }

    function exchange(address _partnerAddrB, uint256 _amount, address _userAddr) public{
        uint256 tokenAmount = _amount * exchangeRate[msg.sender][_partnerAddrB];
        require(_partnerAddrB.call(bytes4(sha3("transfer(address,uint256)")), _userAddr, tokenAmount));
    }
}