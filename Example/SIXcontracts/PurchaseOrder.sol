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

contract purchaseOrder is Ownable {  
                  
     address public bank ;  
     address public customer;     
     address public sme;          
     address public ec;           
     address public logistic;     
     string public productNumber; 
     uint public pOfSme;
     uint public pOfEc;
     uint public pOfLogistic;

     mapping(uint => bool) public status;

     event StatusChanged(address indexed _from, bool indexed _newStatus);
     event Payment(address _sender, uint value);

     function () external payable{ 
         pay();
     }

     constructor(address _customer, address _sme, address _ec, address _logistic, string _productNumber, uint _pOfSme, 
     uint _pOfEc, uint _pOfLogistic)  public {
         customer = _customer;
         sme = _sme;
         ec = _ec;
         logistic = _logistic;
         productNumber = _productNumber;
         pOfSme = _pOfSme;
         pOfEc = _pOfEc;
         pOfLogistic = _pOfLogistic;
         require(
             _pOfSme + _pOfEc + _pOfLogistic == 100,
             "_pOfSme + _pOfEc + _pOfLogistic need = 100"
         );
         status[0] = true;
         for(uint8 i = 1; i < 7; i++){
             status[i] = false;
         }
     }

     function changeStatus(uint stepNumber, bool newStatus) public {
         emit StatusChanged(msg.sender, newStatus);
         require(
             stepNumber != 0 && stepNumber != 6,
             "wrong step !"
         );                                                                         
         status[stepNumber] = newStatus;
         if(stepNumber == 5){                                                                         
             finalized();
         }
     }

     function finalized() public {                                                         
         uint contractBalance = address(this).balance;
         ec.transfer(contractBalance*pOfEc/100);
         sme.transfer(contractBalance*pOfSme/100);
         logistic.transfer(contractBalance*pOfLogistic/100);
         emit Payment(msg.sender, contractBalance);
         status[6] = true; 
     }

     function disable() public  {
         for(uint8 i = 0; i < 7; i++){
             status[i] = false;
         }
     }

     function pay() internal   {
         emit Payment(msg.sender, msg.value);
     } 
 }