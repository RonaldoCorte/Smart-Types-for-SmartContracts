module Gamma = Map.Make (String)
module CT = Map.Make (String)


(* TYPES *)
type typ =
| TBool
| TNat
| TUnit
| TAddress
| TContract of string 
| TMapping of typ * typ 
| TFun of typ list * typ
| TString  (*added*)
| TState 

type values =
| VTrue                   (* true *)
| VFalse                  (* false *)
| VCons of int            (* n *)
| VAddress of string      (* address *)
| VContract of string     (* contract c *)
| VUnit                   (* u *)
| VMapping of (values * values) list 
| VString of string (*added*)
| VState of string

 
type exp = 
  | TmValue of values         
  | TmVar of string         
  | TmGetParam of string   
  | TmGetState of string
  | TmBalance of exp          
  | TmMappSel of exp * exp   
  | TmStateSel of exp * string 
  | TmPlus of exp * exp                     
  | TmMinus of exp * exp    
  | TmMult of term * term
  | TmDiv of term * term              
  | Equals of exp * exp       
  | Less of exp * exp          
  | Greater of exp * exp      
  | Not of exp               
  | And of exp * exp        
  | Or of exp * exp           
  | LessOrEquals of exp * exp 
  | GreaterOrEquals of exp * exp 
  | TmAddress of exp                      


type comm =
  | TmStateAss of exp * string * exp      
  | TmTransfer of exp * exp               
  | TmNew of string * exp * exp list     
  | TmDecl of typ * string * exp * exp  
  | TmAssign of string * exp               
  | TmMappAss of exp * exp * exp        
  | TmFun of exp * string                   
  | TmIf of exp * comm * comm              
  | TmRevert                                           
  | TmCall of exp * string * exp * exp list      
  | TmCallTop of exp * string * exp * exp * exp list 
  | TmSeq of comm * comm                                             
  | TmReturn of exp    
  
type params = typ * string
type construtor_ =  params list * term
type func = {
    requires : term;
    return_type: typ;
    func_name: string;
    params: params list;
    body: term; 
  }

type contract_tc = {
name : string;
init : (params list) * term;
invariant : (params list) * term;
behavioral_types: term list;
vars: (term * typ) list;
cons : construtor_;
funcs: func list;
}
  
type params = typ * string
type func = typ * string * params list * comm
type construtor =  params list * comm
type contract = params list * func list 

(* Bank *)
let sender : exp = TmVar("sender") 
let msg_value : exp = TmVar("msg_value")
let balances = TmVar("Balances")

let param_balances : params = (TMapping(TAddress, TNat), "balances_param")
let bank_constructor : construtor = ([param_balances],TmReturnUnit(TmAssign("balances", TmVar("balances_param")) )) 

let deposit : func = (TUnit, "deposit", [], TmReturnUnit( TmMappAss(balances, sender, TmPlus( TmMappSel(balances, sender) , msg_value) ) ) )

let get_balance : func = (TNat, "get_balance", [], TmReturn( TmMappSel(TmVar("balances"), sender) ) )

let param_to : params = (TAddress, "to")
let param_amount :params = (TNat, "amount")
let transfer : func = (TUnit, "transfer", [param_to; param_amount] , TmReturnUnit( TmIf( GreaterOrEquals(TmMappSel(TmVar("balances"), sender), TmVar("param_amount")), 
                                                                      TmSeq( TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender),TmVar("param_amount"))),
                                                                             (balances, TmVar("param_to"), TmPlus( TmMappSel(balances, TmVar("param_to")),TmVar("param_amount")))), 
                                                                      TmReturn(TmValue(VUnit))) ) )

let param_withdraw_amount : params = (TNat, "W_amount") 
let withdraw : func = (TUnit, "withdraw", [param_withdraw_amount], TmReturnUnit( TmIf( GreaterOrEquals(TmMappSel(TmVar("balances"), sender), TmVar("param_amount")), 
                                                                  TmSeq(TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender),TmVar("param_amount"))), 
                                                                        TmTransfer( sender, TmVar("param_withdraw_amount") ) ), 
                                                                        TmReturn(TmValue(VUnit))) ) )
let ctBank = (CT.add "Bank" ( (
             [(TAddress,"Sender"); (TNat,"MsgValue");(TNat,"Balances")], 
             bank_constructor,
             [ deposit; get_balance; transfer; withdraw]) ) );

(* Marketplace-azure *)

let instanceOwner : exp = TmVar("InstanceOwner")
let description : exp = TmVar("Description")
let askingPrice : exp = TmVar("AskingPrice")
let instanceBuyer : exp = TmVar("InstanceBuyer")
let offerPrice : exp = TmVar("OfferPrice")

let param_description : params = (TString, "param_description")
let param_price : params = (TNat,"param_price")
let marketplace_constructor : construtor = ([param_description;param_price], 
                                     TmReturnUnit(TmSeq( TmAssign("InstanceOwner",TmVar("param_description")) , TmSeq(TmAssign("AskingPrice",TmVar("param_price") ), TmAssign("Description", TmVar("param_description") ) )) ) )
let param_offer : params = (TNat, "param_offer")
let make_offer : func = (TUnit, "make_offer", [param_offer], 
                      TmReturnUnit( TmSeq( TmIf(Equals(TmVar("param_offer"), TmValue(VCons(0))), TmRevert, TmReturn(TmValue(VUnit))),TmSeq( TmIf(Equals(TmVar("sender"), TmVar("InstanceOwner")), TmRevert, TmReturn(TmValue(VUnit))),
                      TmSeq( TmAssign("InstanceBuyer", TmVar("Sender")), TmAssign("OfferPrice", TmVar("param_offer")) ) ))))
                
 
let reject : func = (TUnit, "reject", [], TmReturnUnit(TmSeq( TmIf(Not(Equals(TmVar("param_offer"), TmValue(VCons(0)))), 
                                                              TmRevert, 
                                                              TmReturn(TmValue(VUnit))), 
                                                       TmAssign("InstanceBuyer", TmValue(VString("0x000000000"))) ) ) )

let accept : func = (TUnit, "accept", [], TmReturnUnit(TmIf(Not(Equals(TmVar("param_offer"), TmValue(VCons(0)))), 
                                                        TmRevert, 
                                                        TmReturn(TmValue(VUnit)))))
                                                        
          
let ctMarketplace =  (CT.add "Marketplace" ( (
  [(TAddress,"Sender"); (TNat,"MsgValue");(TAddress,"InstanceOwner"); (TString, "Description"); (TNat, "AskingPrice"); (TAddress,"InstanceBuyer"); (TNat, "OfferPrice") ], 
  marketplace_constructor,
  [ make_offer; reject; accept]) ) );
                                                    
(* Telemetry-azure *)
let sender : exp = TmVar("Sender")
let owner : exp = TmVar("Owner")
let initialCounterParty : exp = TmVar("InitialCounterParty")
let counterParty : exp = TmVar("CounterParty")
let previousParty : exp = TmVar("PreviousParty")
let device : exp = TmVar("Device")
let supplyChainOwner : exp = TmVar("SupplyChainOwner")
let supplyChainObserver : exp = TmVar("SupplyChainObserver")
let complianceStatus : exp = TmVar("ComplianceStatus")
let max_temp : exp = TmVar("Max_Temperature")
let min_temp : exp = TmVar("Min_Temperature")
(*GetParam__*)
let param_device : params = (TAddress,"param_device")
let param_supplyChainOwner : params = (TAddress,"param_supplyChainOwner")
let param_supplyChainObserver : params = (TAddress,"param_supplyChainObserver")
let param_max_temp : params = (TAddress,"param_max_temp")
let param_min_temp : params = (TAddress,"param_min_temp")
let telemetry_constructor = ([param_device; param_supplyChainOwner; param_supplyChainObserver; param_max_temp; param_min_temp],
                            TmReturnUnit(TmSeq( TmAssign("ComplianceStatus",TmValue(VTrue)) , TmSeq( TmAssign("InitialCounterParty", sender), 
                            TmSeq(TmAssign("Owner", TmVar("InitialCounterParty")) , TmSeq(TmAssign(" Device", TmVar("param_device") ) , 
                            TmSeq(TmAssign(" SupplyChainOwner", TmVar("param_supplyChainOwner")), 
                            TmSeq(TmAssign("SupplyChainObserver", TmVar("param_supplyChainObserver") ), 
                            TmSeq(TmAssign("Max_Temperature", TmVar("param_max_temp") ) , TmAssign("Min_Temperature", TmVar("param_min_temp") )))) ) ) ) ) ) ) 
 
let param_temp : params = (TNat, "param_temp")                            
let ingest_telemetry : func = (TUnit, "ingest_telemetry", [param_temp], TmReturnUnit( TmSeq(TmIf( Not(Equals(sender, device)), TmRevert, TmReturn(TmValue(VUnit))), 
                              TmSeq(TmIf( Or( Greater(TmVar("param_temp"), max_temp), Less(TmVar("param_temp"), min_temp)),TmAssign("ComplianceStatus",TmValue(VFalse)),TmReturn(TmValue(VUnit))) ,TmReturn(TmValue(VUnit))))) ) 

let param_new_counter_party : params = (TAddress, "param_new_counter_party")                             
let transfer_responsability : func = (TUnit, "transfer_responsability", [param_new_counter_party], TmReturnUnit( TmSeq( TmIf( And(Not(Equals(sender,initialCounterParty )),Not(Equals(sender,counterParty))), TmRevert ,TmReturn(TmValue(VUnit))),
                                     TmSeq(TmIf(Equals(TmVar("param_new_counter_party"),device), TmRevert, TmReturn(TmValue(VUnit))), TmSeq( TmAssign("PreviousCounterParty", counterParty), TmAssign("counterParty", TmVar("param_new_counter_party")) ) ) ) ) )

let complete : func = (TUnit, "complete", [], TmReturnUnit( TmSeq( TmIf( And(Not(Equals(sender,owner )),Not(Equals(sender,supplyChainObserver))), TmRevert ,TmReturn(TmValue(VUnit))), 
                      TmSeq(TmAssign("PreviousCounterParty", counterParty), TmAssign("CounterParty", TmValue(VString("0x000000000"))) ) ) ) )  
                      
          
let ctTelemetry =  (CT.add "Telemetry" ( (
  [(TAddress,"Sender"); (TNat,"MsgValue");(TAddress,"Owner");(TAddress,"InitialCounterParty"); (TAddress,"CounterParty"); (TAddress,"PreviousParty"); (TAddress,"Device");
  (TAddress,"SupplyChainObserver");(TAddress,"SupplyChainOwner");(TNat,"Max_Temperature");(TNat,"Min_Temperature");], 
  telemetry_constructor,
  [ ingest_telemetry; transfer_responsability; complete]) ) );                       