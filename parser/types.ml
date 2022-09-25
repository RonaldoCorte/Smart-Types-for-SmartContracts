module Gamma = Map.Make (String)

    (*-------------------------------FS-------------------*)
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
  
   
  type term = 
    | TmValue of values          (* v *)     (*hasInCubicle*)
    | TmVar of string            (* x *)     (*hasInCubicle*)
    | TmGetParam of string
    | TmGetState of string
    | TmBalance of term           (* balance(e) *)
    | TmAddress of term                       (* address(e) *)
    | TmMappSel of term * term     (* e[e] *)  (*hasInCubicle*)
    | TmStateSel of term * string (* e.s *)
    | TmPlus of term * term                     (*hasInCubicle*)
    | TmMinus of term * term                    (*hasInCubicle*)
    | TmMult of term * term
    | TmDiv of term * term
    | Equals of term * term        (* x == 3 *) (*hasInCubicle*)
    | Less of term * term          (* x < 3*)   (*hasInCubicle*)
    | Greater of term * term       (* x > 3*)   (*hasInCubicle*)
    | Not of term                 (* !x *)     (*hasInCubicle*)
    | And of term * term           (* x AND y *)(*hasInCubicle*)
    | Or of term * term            (* x OR y *) (*hasInCubicle*)
    | LessOrEquals of term * term  (* x <= 3*)  (*hasInCubicle*)
    | GreaterOrEquals of term * term (* x >= 3*)(*hasInCubicle*)
    | TmStateAss of term * string * term      (* e.s = e *)
    | TmTransfer of term * term               (* e.transfer(e) *)
    | TmNew of string * term * term list      (* new C.value(e)(e~) *)
    | TmDecl of typ * string * term * term    (* T x = e ; e *)
    | TmAssign of string * term                (* x = e *)               (*hasInCubicle*)
    | TmMappAss of term * term * term        (* e[e -> e] *)             (*hasInCubicle*)
    | TmFun of term * string                    (* c.f *)    
    | TmIf of term * term * term              (* if e then e else e *)  (*hasInCubicle*)
    | TmRevert                                (* revert *)             
    | TmCall of term * string * term * term list (* e1.f.value(e2)(e) *)      
    | TmCallTop of term * string * term * term * term list (* e1.f.value(e2).sender(e3)(e) *)
    | TmSeq of term * term                                             (*hasInCubicle*)
    | TmReturn of term                        (* return e *)

    
    type params = typ * string
    type func_ = typ * string * params list * term
    type construtor_ =  params list * term
    type func = {
        requires : term;
        return_type: typ;
        func_name: string;
        params: params list;
        body: term; (*adicionar bool requires*)
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
    (*------------------------Cub--------------------------*)
    (* TYPES *)
    type cub_typ =
    | Int 
    | Bool 
    | Proc
    | CArr of cub_typ * cub_typ
    | State
    | Unit

    type cub_values =
    | CBool of bool
    | CCons of int            (* n *)
    | CProc of string      
    | CUnit                   (* u *)
    | CMapping of (values * values) list 
    | CState of string

    type exp =
    | C_Address of exp
    | C_Value of cub_values
    | C_Plus of exp * exp (*  3 + 4 *)
    | C_Minus of exp * exp (* CHANGED*)
    | C_Div of exp * exp (* CHANGED*)
    | C_Mult of exp * exp (*  CHANGED*)
    | C_Equals of exp * exp         (* x == 3 *)
    | C_Not of exp     (* x != 3 *)                   (*CHANGED*)
    | C_Less of exp * exp          (* x < 3*)
    | C_Greater of exp * exp       (* x > 3*)
    | C_And of exp * exp          (* x AND y *)
    | C_Or of exp * exp            (* x OR y *)
    | C_LessOrEquals of exp * exp  (* x <= 3*)
    | C_GreaterOrEquals of exp * exp (* x >= 3*)
    | C_GetI of exp * exp         (* arr[i] *)    (*CHANGED*)
    | C_Get_Param of string
    | C_GetState of string
    | C_GetVar of string
    | C_TS of string (*typestate*)
    | C_Assign of string * exp       (* x = 3 *)       
    | C_AssignArr of exp * exp * exp (*  arr[i] = 4*)  (*CHANGED*)
    | C_Seq of exp * exp          (* exp;exp *)
    | C_Case of string * (exp * exp) list  (*  CurrentState := case | CurrentState = Created : InTransit;*) 
    

    type behavioral_types = exp list  
   (* type cub_func = string * exp list * exp * exp*)
    type cub_vars =  (exp * cub_typ) list
    type cubfunc_ = {
        requires_ : exp;
        name_ : string;
        params_ : exp list;
        body_ : exp
      } 
    type contract_cub = { (*meter init e unsafe*)
        name : string;
        init : (exp list) * exp;
        unsafe : (exp list) * exp;
        behavioral_types: behavioral_types;
        vars: cub_vars;
        funcs: cubfunc_ list
    }                                            

 