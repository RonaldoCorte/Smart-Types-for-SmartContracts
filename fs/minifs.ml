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

(* TERMS *)
type term =
  | TmValue of values                       (* v *)
  | TmVar of string                         (* x *)
  | TmBalance of term                       (* balance(e) *)
  | TmAddress of term                       (* address(e) *)
  | TmStateSel of term * string             (* e.s *)
  | TmStateAss of term * string * term      (* e.s = e *)
  | TmTransfer of term * term               (* e.transfer(e) *)
  | TmNew of string * term * term list      (* new C.value(e)(e~) *)
  | TmDecl of typ * string * term * term    (* T x = e ; e *)
  | TmAssign of string * term               (* x = e *)
  | TmMappAss of term * term * term         (* e[e -> e] *)
  | TmMappSel of term * term                (* e[e] *)
  | TmFun of term * string                    (* c.f *)
  | TmIf of term * term * term              (* if e then e else e *)
  | TmReturn of term                        (* return e *)
  | TmRevert                                (* revert *)
  | TmCall of term * string * term * term list (* e1.f.value(e2)(e) *)     
  | TmCallTop of term * string * term * term * term list (* e1.f.value(e2).sender(e3)(e) *)
  | TmSeq of term * term 
  | TmPlus of term * term
  | TmMinus of term * term
  | Equals of term * term         (* x == 3 *)
  | Less of term * term          (* x < 3*)
  | Greater of term * term       (* x > 3*)
  | Not of term                  (* !x *)
  | And of term * term          (* x AND y *)
  | Or of term * term            (* x OR y *)
  | LessOrEquals of term * term  (* x <= 3*)
  | GreaterOrEquals of term * term (* x >= 3*)

  (*dividir expressoes arit_Exp, bool_exp, command e mudar construtor *)
  
type command = 
  | Eval of term
  | CSeq of command * command

type params = typ * string
type func = typ * string * params list * term
type contract = params list * func list 

(* Bank *)
let sender : term = TmVar("sender") 
let msg_value : term = TmVar("msg_value")
let balances = TmVar("Balances")

let param_balances : params = (TMapping(TAddress, TNat), "balances_param")
let bank_constructor : func = (TUnit, "Bank", [param_balances], TmAssign("balances", TmVar("balances_param") )) 

let deposit : func = (TUnit, "deposit", [], TmReturn( TmMappAss(balances, sender, TmPlus( TmMappSel(balances, sender) , msg_value) ) ) )

let get_balance : func = (TNat, "get_balance", [], TmReturn( TmMappSel(TmVar("balances"), sender) ) )

let param_to : params = (TAddress, "to")
let param_amount :params = (TNat, "amount")
let transfer : func = (TUnit, "transfer", [param_to; param_amount] , TmReturn( TmIf( GreaterOrEquals(TmMappSel(TmVar("balances"), sender), TmVar("param_amount")), 
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
