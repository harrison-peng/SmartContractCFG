pragma solidity 0.4.25;

 contract Bank{

     mapping(address=>uint) userBalances;

     event Name(address send);

     function getUserBalance(address user) public view returns(uint) {
         return userBalances[user];
     }

     function addToBalance() public payable{
         userBalances[msg.sender] = userBalances[msg.sender] + msg.value;
     }

     function withdrawBalance() public {
         uint amountToWithdraw = userBalances[msg.sender];
         emit Name(msg.sender);
         if (msg.sender.call.value(amountToWithdraw)() == false) {
             revert();
         }
         userBalances[msg.sender] = 0;
     }

     function contractHoldEth() public view returns (uint256){
         return address(this).balance;
     }
 }