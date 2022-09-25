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

type values =
  | VTrue                   (* true *)
  | VFalse                  (* false *)
  | VCons of int            (* n *)
  | VAddress of string      (* address *)
  | VContract of string     (* contract c *)
  | VUnit                   (* u *)
  | VMapping of (values * values) list 
  | VString of string (*added*)

 
type exp = 
  | TmValue of values                       (* v *)
  | TmVar of string                         (* x *)
  | TmBalance of exp                       (* balance(e) *)
  | TmMappSel of exp * exp                (* e[e] *)
  | TmStateSel of exp * string             (* e.s *)
  | TmPlus of exp * exp
  | TmMinus of exp * exp
  | Equals of exp * exp         (* x == 3 *)
  | Less of exp * exp          (* x < 3*)
  | Greater of exp * exp       (* x > 3*)
  | Not of exp                  (* !x *)
  | And of exp * exp          (* x AND y *)
  | Or of exp * exp            (* x OR y *)
  | LessOrEquals of exp * exp  (* x <= 3*)
  | GreaterOrEquals of exp * exp (* x >= 3*)

type comm =
  | TmAddress of exp                       (* address(e) *)
  | TmStateAss of exp * string * exp      (* e.s = e *)
  | TmTransfer of exp * exp               (* e.transfer(e) *)
  | TmNew of string * exp * exp list      (* new C.value(e)(e~) *)
  | TmDecl of typ * string * exp * exp    (* T x = e ; e *)
  | TmAssign of string * exp               (* x = e *)
  | TmMappAss of exp * exp * exp         (* e[e -> e] *)
  | TmFun of exp * string                    (* c.f *)
  | TmIf of exp * exp * exp              (* if e then e else e *)
  | TmRevert                                (* revert *)
  | TmCall of exp * string * exp * exp list (* e1.f.value(e2)(e) *)     
  | TmCallTop of exp * string * exp * exp * exp list (* e1.f.value(e2).sender(e3)(e) *)
  | TmSeq of comm * comm 
  | TmReturn of exp                        (* return e *)
  | TmReturnUnit of comm

  (*dividir expressoes arit_Exp, bool_exp, command e mudar construtor *)
  
type params = typ * string
type func = typ * string * params list * comm
type construtor =  params list * comm list
type contract = params list * func list 

(* Bank *)
let sender : exp = TmVar("sender") 
let msg_value : exp = TmVar("msg_value")
let balances = TmVar("Balances")

let param_balances : params = (TMapping(TAddress, TNat), "balances_param")
let bank_constructor : func = (TUnit, "Bank", [param_balances],TmReturnUnit(TmAssign("balances", TmVar("balances_param")) )) 

let deposit : func = (TUnit, "deposit", [], TmReturnUnit( TmMappAss(balances, sender, TmPlus( TmMappSel(balances, sender) , msg_value) ) ) )

let get_balance : func = (TNat, "get_balance", [], TmReturn( TmMappSel(TmVar("balances"), sender) ) )

let param_to : params = (TAddress, "to")
let param_amount :params = (TNat, "amount")
let transfer : func = (TUnit, "transfer", [param_to; param_amount] , TmReturnUnit( TmIf( GreaterOrEquals(TmMappSel(TmVar("balances"), sender), TmVar("param_amount")), 
                                                                      TmSeq( TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender),TmVar("param_amount"))),
                                                                             TmMappAss(balances, TmVar("param_to"), TmPlus( TmMappSel(balances, TmVar("param_to")),TmVar("param_amount")))), 
                                                                      TmValue(VUnit)) ) )

let param_withdraw_amount : params = (TNat, "W_amount") 
let withdraw : func = (TUnit, "withdraw", [param_withdraw_amount], TmReturn( TmIf( GreaterOrEquals(TmMappSel(TmVar("balances"), sender), TmVar("param_amount")), 
                                                                  TmSeq(TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender),TmVar("param_amount"))), 
                                                                        TmTransfer( sender, TmVar("param_withdraw_amount") ) ), 
                                                                  TmValue(VUnit)) ) )
let ctBank = (CT.add "Bank" ( (
             [(TAddress,"Sender"); (TNat,"MsgValue");(TNat,"Balances")], 
             [bank_constructor, deposit, get_balance, transfer, withdraw]) ) );

(* Marketplace-azure *)

let instanceOwner : term = TmVar("InstanceOwner")
let description : term = TmVar("Description")
let askingPrice : term = TmVar("AskingPrice")
let instanceBuyer : term = TmVar("InstanceBuyer")
let offerPrice : term = TmVar("OfferPrice")

let param_description : params = (TString, "param_description")
let param_price : params = (TNat,"param_price")
let marketplace_constructor : func = (TUnit,"Marketplace", [param_description;param_price], 
                                     TmReturn(TmSeq( TmAssign("InstanceOwner",TmVar("param_description")) , TmSeq(TmAssign("AskingPrice",TmVar("param_price") ), TmAssign("Description", TmVar("param_description") ) )) ) )
let param_offer : params = (TNat, "param_offer")
let make_offer : func = (TUnit, "make_offer", [param_offer], 
                      TmReturn( TmSeq( TmIf(Equals(TmVar("param_offer"), TmValue(VCons(0)), TmRevert,TmValue(""))),TmSeq( TmIf(Equals(TmVar("sender"), TmVar("InstanceOwner")), TmRevert, TmValue(VUnit)), TmSeq(TmRevert, TmValue(VUnit)),
                      TmSeq( TmAssign("InstanceBuyer", TmVar("Sender")), TmAssign("OfferPrice", TmVar("param_offer")) ) ))))
                
 
(*let reject : func = (TUnit, "reject", [], TmReturn())*)
