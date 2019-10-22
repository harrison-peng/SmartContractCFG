pragma solidity 0.4.25;

 contract Ownable {

     address public owner;

     event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

     constructor() public {
         owner = msg.sender;
     }

     modifier onlyOwner() {
         require(
             msg.sender == owner,
             "you have no right to execute this method.");
         _;
     }

     function transferOwnership(address newOwner) public  {         
         require(
             newOwner != owner,
             "wrong address"
         );                                                         
         emit OwnershipTransferred(owner, newOwner);
         owner = newOwner;
     }
 }