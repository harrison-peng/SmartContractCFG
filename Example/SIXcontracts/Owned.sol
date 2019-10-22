pragma solidity ^0.4.25;


contract Owned {
    address public owner;
    address public newOwner;

    event OwnershipTransferred(address indexed _from, address indexed _to);

    function Owned() public {
        owner = msg.sender;
    }

    modifier onlyOwner {
        require(msg.sender == owner);
        _;
    }

    function transferOwnership(address _newOwner) public onlyOwner {
        newOwner = _newOwner;
    }

    function acceptOwnership() public {
        require(msg.sender == newOwner);
        emit OwnershipTransferred(owner, newOwner);
        owner = newOwner;
        newOwner = address(0);
    }
}


contract PointEX is Owned {
    mapping(address => bool) private distributor;

    modifier onlyDistributor {
        require(distributor[msg.sender] == true);
        _;
    }

    event GetTransactionData(string _fromCompany, string _fromID, uint256 _fromAmounts, string _toCompany, string _toID, uint256 _toAmounts, address indexed _recorder);

    function PointEX() public {
        distributor[owner] = true;
    }

    function transfer(string _fromCompany, string _fromID, uint256 _fromAmounts, string _toCompany, string _toID, uint256 _toAmounts) public onlyDistributor returns (bool) {
        emit GetTransactionData(_fromCompany, _fromID, _fromAmounts, _toCompany, _toID, _toAmounts, msg.sender);
        
        return true;
    }

    function setDistributor(address _dis, bool _status) public onlyOwner returns (bool) {
        require(_dis != address(0));

        distributor[_dis] = _status;

        return true;
    }
}