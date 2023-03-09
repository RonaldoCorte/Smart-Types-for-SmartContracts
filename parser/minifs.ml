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
type func_ = typ * string * params list * term * term
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

type contract = params list * func list 

(*type params = typ * string
type func = typ * string * params list
type contract = params list * func list*)

exception InvalidTerm of term * term
let invTerm termected received =
  raise (InvalidTerm (termected, received))  
  
type command = 
  | Eval of term
  | CSeq of command * command

let comma fmt () = Format.fprintf fmt ", "

exception TypMismatch of typ * typ
let compType expected received = 
  if not (received = expected) then raise (TypMismatch (expected, received)) else received

(* ------------------ PRINTING ------------------ *)
let rec pp_listparams f c fmt = function
[] -> ()
| [t] -> f fmt t 
| t :: l -> f fmt t; c fmt () ; pp_listparams f c fmt l

(* PRINT TYPES *)
let rec pp_typ fmt = function
  | TBool -> Format.fprintf fmt "bool"
  | TNat -> Format.fprintf fmt "uint"
  | TState -> Format.fprintf fmt "state"
  | TUnit -> Format.fprintf fmt "unit"
  | TAddress -> Format.fprintf fmt "address"
  | TString -> Format.fprintf fmt "string"
  | TContract(c) -> Format.fprintf fmt "%s" c
  | TMapping(t1, t2) -> Format.fprintf fmt "mapping(%a => %a)" pp_typ t1 pp_typ t2
  | TFun(l, t) -> Format.fprintf fmt "%a -> %a" (pp_listparams pp_typ comma) l pp_typ t

let rec pp_mappings f c fmt = function
  [] -> ()
  | [(v1, v2)] -> Format.fprintf fmt "(%a , %a)" f v1 f v2
  | (v1, v2) :: l -> Format.fprintf fmt "(%a , %a)" f v1 f v2 ; c fmt () ; pp_mappings f c fmt l

(* PRINT VALUES *)
let rec pp_val fmt = function
  | VTrue -> Format.fprintf fmt "true"
  | VFalse -> Format.fprintf fmt "false"
  | VState(s) -> Format.fprintf fmt "%s" s
  | VString(s) -> Format.fprintf fmt "%s" s
  | VCons(v) -> Format.fprintf fmt "%d" v
  | VAddress(v) -> Format.fprintf fmt "%s" v
  | VContract(v) -> Format.fprintf fmt "%s" v
  | VUnit -> Format.fprintf fmt "u" 
  | VMapping(l) -> Format.fprintf fmt "[%a]" (pp_mappings pp_val comma) l

  let rec pp_listparams f c fmt = function
  [] -> ()
  | [t] -> f fmt t 
  | t :: l -> f fmt t; c fmt () ; pp_listparams f c fmt l

(* PRINT TERMS *)
let rec pp_term fmt = function
  | TmValue(t) -> Format.fprintf fmt "%a" pp_val t
  | TmVar(t) -> Format.fprintf fmt "%s" t
  | TmBalance(t) -> Format.fprintf fmt "balance(%a)" pp_term t 
  | TmAddress(t) -> Format.fprintf fmt "address(%a)" pp_term t
  | TmStateSel(e, s) -> Format.fprintf fmt "%a.%s" pp_term e s
  | TmStateAss(e1, s, e2) -> Format.fprintf fmt "%a.%s = %a" pp_term e1 s pp_term e2
  | TmTransfer(e1, e2) -> Format.fprintf fmt "%a.transfer(%a)" pp_term e1 pp_term e2
  | TmNew(c, e1, e2) -> Format.fprintf fmt "new %s.value(%a)(%a)" c pp_term e1 (pp_listparams pp_term comma) e2
  | TmDecl(t, x, e1, e2) -> Format.fprintf fmt "%a %s = %a ; %a" pp_typ t x pp_term e1 pp_term e2
  | TmAssign(x, e) -> Format.fprintf fmt "%s = %a" x pp_term e 
  | TmMappAss(e1, e2, e3) -> Format.fprintf fmt "%a[%a -> %a]" pp_term e1 pp_term e2 pp_term e3
  | TmMappSel(e1, e2) -> Format.fprintf fmt "%a[%a]" pp_term e1 pp_term e2
  | TmIf(t1, t2, t3) -> Format.fprintf fmt "if %a then %a else %a" pp_term t1 pp_term t2 pp_term t3
  | TmFun(c, f) -> Format.fprintf fmt "%a.%s" pp_term c f
  | TmReturn(e) -> Format.fprintf fmt "return %a" pp_term e 
  | TmRevert -> Format.fprintf fmt "revert"
  | TmCall(e1, f, e2, e) -> Format.fprintf fmt "%a.%s.value(%a)(%a)" pp_term e1 f pp_term e2 (pp_listparams pp_term comma) e
  | TmCallTop(e1, f, e2, e3, e) -> Format.fprintf fmt "%a.%s.value(%a).sender(%a)(%a)" pp_term e1 f pp_term e2 pp_term e3
   (pp_listparams pp_term comma) e
  | TmSeq(e1, e2) -> Format.fprintf fmt "%a ; %a" pp_term e1 pp_term e2
  | TmPlus(e1, e2) -> Format.fprintf fmt "%a + %a" pp_term e1 pp_term e2
  | TmMinus(e1, e2) -> Format.fprintf fmt "%a - %a" pp_term e1 pp_term e2
  | TmMult(e1, e2) -> Format.fprintf fmt "%a * %a" pp_term e1 pp_term e2
  | TmDiv(e1, e2) -> Format.fprintf fmt "%a / %a" pp_term e1 pp_term e2
  | Equals(e1, e2) -> Format.fprintf fmt "%a == %a" pp_term e1 pp_term e2
  | Less(e1, e2) -> Format.fprintf fmt "%a < %a" pp_term e1 pp_term e2
  | Greater(e1, e2) -> Format.fprintf fmt "%a > %a" pp_term e1 pp_term e2
  | Not(e1) -> Format.fprintf fmt "!%a" pp_term e1
  | And(e1, e2) -> Format.fprintf fmt "%a && %a" pp_term e1 pp_term e2
  | Or(e1, e2) -> Format.fprintf fmt "%a || %a" pp_term e1 pp_term e2
  | LessOrEquals(e1, e2) -> Format.fprintf fmt "%a <= %a" pp_term e1 pp_term e2
  | GreaterOrEquals(e1, e2) -> Format.fprintf fmt "%a >= %a" pp_term e1 pp_term e2
  | TmGetParam(p) -> Format.fprintf fmt "param %s" p
  | TmGetState(p) -> Format.fprintf fmt "state  %s" p




(* PRINT GAMMA *)
let pp_gamma fmt g = 
  Gamma.iter (fun k v -> Format.fprintf fmt "(%s : %a); " k pp_typ v) g

(* PRINT PARAMETERS *)
let rec pp_params fmt = function
  [] -> ()
  | (t,x) :: l -> Format.fprintf fmt "(%a : %s)" pp_typ t x; pp_params fmt l

let rec pp_func fmt = function
  [] -> ()
  | [(t, n, l)] -> Format.fprintf fmt "%a %s (%a)" pp_typ t n pp_params l
  | (t, n, l) :: ll -> Format.fprintf fmt "%a %s (%a) ; " pp_typ t n pp_params l ; pp_func fmt ll

(* PRINT CONTRACT *)
let pp_contract fmt ct = 
  CT.iter (fun x (p, f)  -> Format.fprintf fmt "contract %s {%a} %a @." x pp_params p pp_func f) ct

(* PRINT COMMAND *)
let rec pp_cmd fmt = function
  | Eval t -> Format.fprintf fmt "%a" pp_term t 
  | CSeq(s1, s2) -> Format.fprintf fmt "%a ; %a" pp_cmd s1 pp_cmd s2


(* ------------ AUX FUNCTIONS ----------- *)
let get_type gamma x =
  Gamma.find x gamma

let binding gamma x t =
  Gamma.add x t gamma

let getContractName c =
  match c with 
  | TContract(x) -> x
  | _ -> "oops" (* //TODO error *)

let getTypeFunc ct c f =
  let (paramslist, funclist) = CT.find c ct in 
  let (typefunc, funcname, params) = List.find (fun (tf, fname, tp) -> fname = f) funclist in
  TFun((List.map (fun (typparam, nameparam) -> typparam) params), typefunc)

(* type params = typ * string
type func = typ * string * params list
type contract = params list * func list *)


let rec typecheck whites gamma ct ty t =
  match ty with 
  | None -> for i = 0 to whites - 1 do Format.eprintf " " done ;
   Format.eprintf "%a , %a |- %a : " pp_contract ct pp_gamma gamma pp_term t; 
    begin match t with
      | TmValue(VTrue) -> Format.eprintf "(TRUE) @."; Format.eprintf "%a @." pp_typ TBool ; TBool 
      | TmValue(VFalse) -> Format.eprintf "(FALSE) @."; Format.eprintf "%a @." pp_typ TBool ; TBool
      | TmValue(VCons(v)) -> Format.eprintf "(NAT) @."; Format.eprintf "%a @." pp_typ TNat ; TNat
      | TmValue(VState(v)) -> Format.eprintf "(STATE) @."; Format.eprintf "%a @." pp_typ TState ; TState
      | TmValue(VAddress(x)) -> Format.eprintf "(ADDRESS) @."; Format.eprintf "%a @." pp_typ TAddress ; compType TAddress (get_type gamma x) 
      | TmValue(VContract(x)) -> Format.eprintf "(REF) @.";
      let ctype = get_type gamma x in Format.eprintf "%a @." pp_typ ctype ;
      compType (TContract(getContractName(ctype))) ctype 
      | TmValue(VString(s)) -> Format.eprintf "(STRING) @."; Format.eprintf "%a @." pp_typ TString ; TString
      | TmValue(VUnit) -> Format.eprintf "(UNIT) @."; Format.eprintf "%a @." pp_typ TUnit ; TUnit  
      | TmVar(x) -> Format.eprintf "(Var) @."; let t = get_type gamma x in Format.eprintf "%a @." pp_typ t ; t
      | TmGetParam(x) -> Format.eprintf "(Param) @."; let t = get_type gamma x in Format.eprintf "%a @." pp_typ t ; t
      | TmGetState(x) -> Format.eprintf "(State) @."; let t = get_type gamma x in Format.eprintf "%a @." pp_typ t ; t
      | TmRevert -> Format.eprintf "(REVERT) @."; Format.eprintf "%a @." pp_typ TUnit; TUnit
      | And(t1, t2) | Or(t1,t2) -> Format.eprintf "(Bool cond) @."; 
      let te1 = typecheck (whites + 2) gamma ct (Some TBool) t1 in 
      let te2 = typecheck (whites + 2) gamma ct (Some TBool) t2 in 
      if te1 != TBool then compType TBool te1
      else if te2 != TBool then compType TBool te2 
      else if te1 == te2 then typecheck (whites + 2) gamma ct (Some TBool) (TmValue(VTrue)) else compType TBool te1    
      | TmBalance(t) -> Format.eprintf "(BAL) @.";
      Format.eprintf "%a @." pp_typ TNat ; ignore(typecheck (whites + 2) gamma ct (Some TAddress) t) ; TNat
      | Not(t1)-> Format.eprintf "(Not) @."; 
      let te1 = typecheck (whites + 2) gamma ct (Some TBool) t1 in 
      if( te1 != TBool) then compType TBool te1 else typecheck (whites + 2) gamma ct (Some TBool) (TmValue(VTrue))
      | TmAddress(t) -> Format.eprintf "(ADDR) @.";
        begin match t with 
        | TmValue(VContract(c)) -> Format.eprintf "%a @." pp_typ TAddress ; 
        ignore(typecheck (whites + 2) gamma ct (Some (TContract(getContractName(get_type gamma c)))) t) ; TAddress
        | c -> invTerm (TmValue(VContract("contractName"))) c
        end
      | TmReturn(e) -> Format.eprintf "(RETURN) @.";
      let t = typecheck (whites + 2) gamma ct None e in Format.eprintf "%a @." pp_typ t ; t
      | TmDecl(t, x, e1, e2) -> Format.eprintf "(DECL) @.";
      Format.eprintf "%a @." pp_typ t ; ignore(typecheck (whites + 2) gamma ct (Some t) e1) ; 
      typecheck (whites + 2) (binding gamma x t) ct None e2 
      | TmIf(t1, t2, t3) -> Format.eprintf "(IF) @."; 
        ignore(typecheck (whites + 2) gamma ct (Some TBool) t1) ; 
        let tt1 = typecheck (whites + 2) gamma ct None t2 in 
          let tt2 = typecheck (whites + 2) gamma ct None t3 in
            Format.eprintf "%a @." pp_typ tt1 ; if tt1 == tt2 then tt1 else invTerm t1 t2
      | TmAssign(x, e) -> Format.eprintf "(ASS) @.";
      let te = typecheck (whites + 2) gamma ct None e in
      Format.eprintf "%a @." pp_typ te ;
      let tx = typecheck (whites + 2) gamma ct None (TmVar(x)) in 
      if te == tx then te else compType te tx 
      | Equals(x, e) -> Format.eprintf "(Equals) @.";
      let te = typecheck (whites + 2) gamma ct None e in
      Format.eprintf "%a @." pp_typ te ;
      let tx = typecheck (whites + 2) gamma ct None (x) in 
      if te == tx then te else compType te tx
      | Greater(x, e) | Less(x, e) | GreaterOrEquals(x, e) | LessOrEquals(x, e) -> Format.eprintf "(Cond ) @.";
      let te = typecheck (whites + 2) gamma ct (Some TNat) e in
      Format.eprintf "%a @." pp_typ te ;
      let tx = typecheck (whites + 2) gamma ct (Some TNat) x in 
      if te == tx then te else compType te tx
      |TmPlus(x, y) | TmMinus(x,y) | TmMult(x,y) | TmDiv(x,y)-> Format.eprintf "(Arit) @.";
      let te = typecheck (whites + 2) gamma ct (Some TNat) x in
      Format.eprintf "%a @." pp_typ te ;
      let tx = typecheck (whites + 2) gamma ct (Some TNat) y in
      if te == tx then te else compType te tx 
      | TmValue(VMapping(l)) -> Format.eprintf "(MAPPING) @.";
      let (v1, v2) = (List.hd l) in 
      let t1 = typecheck (whites + 2) gamma ct None (TmValue(v1)) in 
        let t2 = typecheck (whites + 2) gamma ct None (TmValue(v2)) in 
      Format.eprintf "%a @." pp_typ (TMapping(t1, t2)) ; TMapping(t1, t2)
      | TmMappAss(e1, e2, e3) -> Format.eprintf "(MAPPASS) @.";
      let t1 = typecheck (whites + 2) gamma ct None e2 in 
      let t2 = typecheck (whites + 2) gamma ct None e3 in 
      Format.eprintf "%a @." pp_typ (TMapping(t1, t2)) ;
      typecheck (whites + 2) gamma ct (Some (TMapping(t1, t2))) e1 
      | TmMappSel(e1, e2) -> Format.eprintf "(MAPPSEL) @.";
      let t = typecheck (whites + 2) gamma ct None e1 in
        begin match t with 
        | TMapping(t1, t2) -> ignore(typecheck (whites + 2) gamma ct (Some t1) e2) ; Format.eprintf "%a @." pp_typ t2 ; t2
        | t -> compType (TMapping(TUnit, TUnit)) t
        end
      | TmStateSel(e, s) -> Format.eprintf "(STATESEL) @.";
        begin match e with 
        | TmVar x -> let c1 = Gamma.find x gamma in ignore(typecheck (whites + 2) gamma ct (Some c1) e) ;
          let cname = getContractName c1 in 
            let (c , f) = CT.find cname ct in 
              let (ts, x) = List.find (fun (ts,x) -> x = s) c in Format.eprintf "%a @." pp_typ ts ; ts
        | x -> invTerm (TmVar("variable name")) x
        end
      | TmStateAss(e1, s, e2) -> Format.eprintf "(STATEASS) @.";
      let t1 = typecheck (whites + 2) gamma ct None (TmStateSel(e1, s)) in 
      let t2 = typecheck (whites + 2) gamma ct None e2 in
        Format.eprintf "%a @." pp_typ t1 ; compType t1 t2
      | TmNew(c, e1, e2) -> Format.eprintf "(NEW) @.";
      ignore(typecheck (whites + 2) gamma ct (Some TNat) e1) ;
      let (listp, f) = CT.find c ct in 
        let l = List.map (fun (t, x) -> t) listp in 
        List.iter2 (fun typ e -> ignore(typecheck (whites + 2) gamma ct (Some typ) e); ()) l e2; 
        Format.eprintf "%a @." pp_typ (TContract(c)) ; TContract(c)
      | TmFun(c, f) -> Format.eprintf "(FUN) @.";
        begin match c with
        | TmValue(VContract(cn)) -> let contract = getContractName (Gamma.find cn gamma) in 
        let tf = getTypeFunc ct contract f in 
        Format.eprintf "%a @." pp_typ tf ; 
        ignore(typecheck (whites + 2) gamma ct (Some (TContract(getContractName(get_type gamma cn)))) c ) ; tf
        | c -> invTerm (TmValue(VContract("contract"))) c  
        end
      | TmTransfer(e1, e2) -> Format.eprintf "(TRANSFER) @.";
      ignore(typecheck (whites + 2) gamma ct (Some TAddress) e1); 
      ignore(typecheck (whites + 2) gamma ct (Some TNat) e2); 
      Format.eprintf "%a @." pp_typ TUnit ; TUnit 
      | TmCall(e1, f, e2, e) -> Format.eprintf "(CALL) @.";
        begin match e1 with
        | TmValue(VContract(cn)) -> 
        let cname = getContractName (Gamma.find cn gamma) in 
        ignore(typecheck (whites + 2) gamma ct (Some (TContract(cname))) e1) ; 
        ignore(typecheck (whites + 2) gamma ct (Some TNat) e2) ; let funType = getTypeFunc ct cname f in 
          begin match funType with 
          | TFun(t1, t2) -> (* let (listp, f) = CT.find cname ct in *)
              (* let l = List.map (fun (t, x) -> t) listp in  *)
              
               List.iter2 (fun typ ee -> ignore(typecheck (whites + 2) gamma ct (Some typ) ee); ()) t1 e; t2
          | x -> compType (TFun([TUnit], TUnit)) x
          end
        | e1 -> invTerm (TmValue(VContract("contract name"))) e1
        end
      | TmCallTop(e1, f, e2, e3, e) -> Format.eprintf "(CALLTOPLEVEL) @.";
      ignore(typecheck (whites + 2) gamma ct (Some TAddress) e3) ; 
      typecheck (whites + 2) gamma ct None (TmCall(e1, f, e2, e))
      | TmSeq(e1, e2) -> Format.eprintf "(SEQ) @." ;
      ignore(typecheck (whites + 2) gamma ct None e1);
      typecheck (whites + 2) gamma ct None e2; 
    end 
  | Some ty -> for i = 0 to whites - 1 do Format.eprintf " " done ;
  Format.eprintf "%a , %a |- %a : %a@." pp_contract ct pp_gamma gamma pp_term t pp_typ ty ; 
    begin match t with 
      | TmValue(VTrue) -> Format.eprintf "(TRUE) @."; compType TBool ty 
      | TmValue(VFalse) -> Format.eprintf "(FALSE) @."; compType TBool ty           
      | TmValue(VCons(v)) -> Format.eprintf "(NAT) @."; compType TNat ty  
      | TmValue(VState(v)) -> Format.eprintf "(STATE) @."; compType TState ty    
      | TmValue(VString(s)) -> Format.eprintf "(String) @."; compType TString ty               
      | TmValue(VAddress(x)) -> Format.eprintf "(ADDRESS) @."; ignore(compType TAddress ty); compType (get_type gamma x) TAddress 
      | TmValue(VContract(x)) -> Format.eprintf "(REF) @."; ignore(compType (get_type gamma x) ty) ; compType (TContract(getContractName(get_type gamma x))) ty
      | TmValue(VUnit) -> Format.eprintf "(UNIT) @."; compType TUnit ty 
      | TmVar(x) -> Format.eprintf "(VAR) @.";compType (get_type gamma x) ty
      | TmGetParam(x) -> Format.eprintf "(PARAM) @.";compType (get_type gamma x) ty
      | TmGetState(x) -> Format.eprintf "(STATE) @.";ignore(compType (get_type gamma x) ty); compType TState ty
      | TmRevert -> Format.eprintf "(REVERT) @."; compType ty ty
      | TmBalance(t) -> Format.eprintf "(BAL) @.";ignore(typecheck (whites + 2) gamma ct (Some TAddress) t) ; compType TNat ty
      | TmPlus(x,y) | TmMinus(x,y) | TmMult(x,y) | TmDiv(x,y)-> Format.eprintf "(Op Arit) @."; ignore(typecheck (whites + 2) gamma ct (Some TNat) x) ; ignore(typecheck (whites + 2) gamma ct (Some TNat) y); compType TNat ty
      | TmAddress(t) -> Format.eprintf "(ADDR) @."; 
        begin match t with 
        | TmValue(VContract(c)) -> ignore(typecheck (whites + 2) gamma ct (Some (TContract(getContractName(get_type gamma c)))) t); compType TAddress ty
        | c -> invTerm (TmValue(VContract("contractName"))) c
        end
      | TmReturn(e) -> Format.eprintf "(RETURN) @."; typecheck (whites + 2) gamma ct (Some ty) e
      | TmDecl(t, x, e1, e2) -> Format.eprintf "(DECL) @."; ignore(typecheck (whites + 2) gamma ct (Some t) e1) ; typecheck (whites + 2) (binding gamma x t) ct (Some ty) e2 
      | TmIf(t1, t2, t3) -> Format.eprintf "(IF) @."; ignore(typecheck (whites + 2) gamma ct (Some TBool) t1) ; ignore(typecheck (whites + 2) gamma ct (Some ty) t2) ;
       typecheck (whites + 2) gamma ct (Some ty) t3 
      | Equals(t1, t2) -> Format.eprintf "(Equals op) @."; 
        ignore(typecheck (whites + 2) gamma ct None (Equals(t1,t2))); compType TBool ty;
      | Greater(t1, t2) | Less(t1,t2) | LessOrEquals(t1,t2) | GreaterOrEquals(t1,t2) -> Format.eprintf "(Bool Cond) @."; 
        ignore(typecheck (whites + 2) gamma ct None (Greater(t1,t2))); compType TBool ty;
      | And(t1, t2) | Or(t1,t2) -> Format.eprintf "(Bool cond) @."; 
        let te1 = typecheck (whites + 2) gamma ct (Some TBool) t1 in 
        let te2 = typecheck (whites + 2) gamma ct (Some TBool) t2 in 
        if te1 != TBool then compType TBool te1
        else if te2 != TBool then compType TBool te2 
        else if te1 == te2 then typecheck (whites + 2) gamma ct (Some TBool) (TmValue(VTrue)) else compType TBool te1     
      | Not(t1)-> Format.eprintf "(Not) @."; 
        let te1 = typecheck (whites + 2) gamma ct (Some TBool) t1 in 
        if( te1 != TBool) then compType TBool te1 else compType TBool ty
      | TmAssign(x, e) ->Format.eprintf "(ASS) @."; ignore(typecheck (whites + 2) gamma ct (Some ty) (TmVar(x))) ; typecheck (whites + 2) gamma ct (Some ty) e 
      | TmValue(VMapping(l)) -> Format.eprintf "(MAPPING) @.";
        begin match ty with
        | TMapping(t1, t2) -> ignore(List.map (fun (v1, v2) -> ignore(typecheck (whites + 2) gamma ct (Some t1) (TmValue(v1))) ;
        ignore(typecheck (whites + 2) gamma ct (Some t2) (TmValue(v2)))) l ); TMapping(t1, t2)
        | t1 -> compType (TMapping(TUnit, TUnit)) ty
        end
      | TmMappAss(e1, e2, e3) ->Format.eprintf "(MAPPASS) @.";
        begin match ty with
        | TMapping(t1, t2) -> ignore(typecheck (whites + 2) gamma ct (Some ty) e1) ; ignore(typecheck (whites + 2) gamma ct (Some t1) e2) ;
                                                  typecheck (whites + 2) gamma ct (Some t2) e3
        | ty -> compType (TMapping(TUnit, TUnit)) ty 
        end
      | TmMappSel(e1, e2) -> Format.eprintf "(MAPPSEL) @."; let t = typecheck (whites + 2) gamma ct None e1 in
        begin match t with 
        | TMapping(t1, t2) -> ignore(typecheck (whites + 2) gamma ct (Some t1) e2) ; compType t2 ty
        | t -> compType (TMapping(TUnit, TUnit)) t
        end
      | TmStateSel(e, s) -> Format.eprintf "(STATESEL) @.";
        begin match e with 
      | TmVar x -> let c1 = Gamma.find x gamma in ignore(typecheck (whites + 2) gamma ct (Some c1) e) ; 
        let cname = getContractName c1 in 
          let (p , f) = CT.find cname ct in 
            let (ts, x) = List.find (fun (ts,x) -> x = s) p in compType ts ty 
        | e ->  invTerm (TmVar("variable")) e 
        end
      | TmStateAss(e1, s, e2) -> Format.eprintf "(STATEASS) @."; 
      ignore(typecheck (whites + 2) gamma ct (Some ty) (TmStateSel(e1, s))) ; typecheck (whites + 2) gamma ct (Some ty) e2
      | TmNew(c, e1, e2) -> Format.eprintf "(NEW) @."; ignore(typecheck (whites + 2) gamma ct (Some TNat) e1) ; 
      let (listp, f) = CT.find c ct in 
        let l = List.map (fun (t, x) -> t) listp in 
        List.iter2 (fun typ e -> ignore(typecheck (whites + 2) gamma ct (Some typ) e); ()) l e2 ; compType (TContract(c)) ty 
      | TmFun(c, f) -> Format.eprintf "(FUN) @.";
        begin match c with
        | TmValue(VContract(cn)) -> let contract = getContractName (Gamma.find cn gamma) in 
        ignore(typecheck (whites + 2) gamma ct (Some (TContract(getContractName(get_type gamma cn)))) c)  ; 
        compType (getTypeFunc ct contract f) ty
        | c -> invTerm (TmValue(VContract("contract"))) c  
        end
      | TmTransfer(e1, e2) -> Format.eprintf "(TRANSFER) @.";
      ignore(typecheck (whites + 2) gamma ct (Some TAddress) e1) ; ignore(typecheck (whites + 2) gamma ct (Some TNat) e2) ; compType TUnit ty 
      | TmCall(e1, f, e2, e) -> Format.eprintf "(CALL) @.";
        begin match e1 with
        | TmValue(VContract(cn)) -> 
        let cname = getContractName (Gamma.find cn gamma) in 
        ignore(typecheck (whites + 2) gamma ct (Some (TContract(cname))) e1) ; 
        ignore(typecheck (whites + 2) gamma ct (Some TNat) e2) ; let funType = getTypeFunc ct cname f in 
          begin match funType with 
          | TFun(t1, t2) -> let (listp, f) = CT.find cname ct in
          let l = List.map (fun (t, x) -> t) listp in List.iter2 (fun typ ee -> ignore(typecheck (whites + 2) gamma ct (Some typ) ee); ()) l e; compType t2 ty 
          | t -> compType (TFun([TUnit], TUnit)) t
          end
        | e1 -> invTerm (TmValue(VContract("contract name"))) e1
        end
      | TmCallTop(e1, f, e2, e3, e) -> Format.eprintf "(CALLTOPLEVEL) @.";
      ignore(typecheck (whites + 2) gamma ct (Some TAddress) e3) ; 
      typecheck (whites + 2) gamma ct (Some ty) (TmCall(e1, f, e2, e)); 
      | TmSeq(e1, e2) ->Format.eprintf "(SEQ) @." ;
      ignore(typecheck (whites + 2) gamma ct None e1);
      typecheck (whites + 2) gamma ct (Some ty) e2; 
    end 



let rec typecheck_command whites gamma ct typ = function
  | Eval t -> Format.open_box 2 ; ignore(typecheck (whites + 2) gamma ct typ t) ; Format.close_box ()
  | CSeq(s1, s2) (*as c*) -> match typ with
                         | Some typ -> (*Format.eprintf "%a , %a |- %a : %a @." pp_contract ct pp_gamma gamma pp_cmd c pp_typ typ;*)
                         typecheck_command (whites + 2) gamma ct None s1; typecheck_command (whites + 2) gamma ct (Some typ) s2 
                         | None -> (*Format.eprintf "%a , %a |- %a : None @." pp_contract ct pp_gamma gamma pp_cmd c; *)
                         typecheck_command (whites + 2) gamma ct None s1; typecheck_command (whites + 2) gamma ct None s2  

let mk_eval t = Eval t
let mk_seq s1 s2 = CSeq(s1, s2)


(* -----------------TESTING----------------- *)
let test_func gamma ct t1 term = 
  try typecheck_command 0 gamma ct t1 term ; Format.eprintf "Success@."
  with TypMismatch (typ1, typ2) -> Format.eprintf "type mismatch : termected type %a but got type %a @." pp_typ typ1 pp_typ typ2 
  | InvalidTerm(t1, t2) -> Format.eprintf "term mismatch : termected %a but got %a@." pp_term t1 pp_term t2;;


let rec do_all ct gamma lst = 
  match lst with
  | [] -> ()
  | x :: xs -> 
               test_func gamma ct (Some TBool) (mk_eval x.requires); 
               test_func gamma ct (Some x.return_type) (mk_eval x.body); 
               do_all ct gamma xs;;

let typecheck_contract ct gamma contract = 
  let (_,init) = contract.init in
  let (_,invariant) = contract.invariant in
  test_func gamma ct (Some TBool) (mk_eval init);
  test_func gamma ct (Some TBool) (mk_eval invariant);
  let (_,cons_body) = contract.cons in
  test_func gamma ct (Some TUnit) (mk_eval cons_body);
  do_all ct gamma (contract.funcs) ;;


  let gammaenv = (Gamma.add "x" (TString) Gamma.empty);;
  let operation = TmPlus(TmVar("x"), TmMult( TmValue(VCons(3)) , TmValue(VCons(3))));;
(*  test_func gammaenv CT.empty (Some TNat) (mk_eval operation)*)

(*let ttrue = TmValue(VTrue)
let tfalse = TmValue(VFalse)
let taddress = TmValue(VAddress("aEOA"))
let tcontract = TmValue(VContract("x"))
let tone = TmValue(VCons(1))
let tzero = TmValue(VCons(0))
let tmPlus = TmPlus(tone,tone)
let tmMinus = TmMinus(tone,tone)
let tmMult = TmMult(tone,tone)
let tmDiv = TmMult(tone,tone)
let tmArComplex = TmSeq(Greater(tone, tone), TmReturn(TmValue(VUnit)))
test_func Gamma.empty CT.empty (Some TUnit) (mk_eval tmArComplex )

let tmEquals = Equals(tone,tzero)
let tmGreaterOrEquals = GreaterOrEquals(tzero,tzero)
let tmGetParam = TmGetParam("x")
let tmAnd = And(ttrue,ttrue)
let tmOr = Or(And(ttrue,ttrue),ttrue)
let tmOrC = Or(And(ttrue,tmGreaterOrEquals),tmEquals)
let tmNot = Not(tmOrC)
let tx = TmVar("x")
let tbalance = TmBalance(taddress)
let treturn = TmReturn(ttrue)
let tdecl = TmDecl(TNat, "x", tone, tx)
let tif = TmIf(ttrue, tone, tone)
let tassign = TmAssign("x", tone)
let tnew = TmNew("EOC", (TmValue(VCons(500))), [tone; ttrue])
let tstatesel = TmStateSel(tx,"b")
let taddress2 = TmAddress(tcontract)
let tstateass = TmStateAss(tx,"b", ttrue)
let tmap = TmValue(VMapping([(VCons(1), VTrue); (VCons(2), VFalse)]))
let tmapass =  TmMappAss(tmap, TmValue(VCons(13)), ttrue)
let tmapsel = TmMappSel(tmap, TmValue(VCons(13)))
let tfun = TmFun((TmValue(VContract("x"))), "f")
let tcall = TmCall(tcontract, "f", tone, [tone; ttrue])
let tcalltop = TmCallTop(tcontract, "f", tone, taddress, [tone; ttrue])
let ttransfer = TmTransfer(taddress, tone)

(*test map*)
let gammaenv3 = (Gamma.add "tmap" (TMapping(TAddress, TNat)) (Gamma.add "tmap_param"  (TMapping(TAddress, TNat)) (Gamma.add "sender"  (TAddress) Gamma.empty)))

let tmap = TmValue(VMapping([(VCons(1), VTrue); (VCons(2), VFalse)]))
let tmapass = TmMappAss(tmap, TmValue(VCons(13)), ttrue)
let tmapsel = TmMappSel(tmap, TmValue(VCons(13)))

let tmapp = TmVar("tmap")
test_func gammaenv3 CT.empty (Some (TMapping(TAddress, TNat))) (mk_eval tmapp)


let mapassing = TmAssign("tmap", TmGetParam("tmap_param"))
test_func gammaenv3 CT.empty (Some (TMapping(TAddress, TNat))) (mk_eval mapassing)

let sender = TmVar("sender")
test_func gammaenv3 CT.empty (Some (TAddress)) (mk_eval sender)

let tmapass = TmMappAss(tmapp, sender,tmPlus)
test_func Gamma.empty CT.empty (Some (TMapping(TAddress, TNat))) (mk_eval tmapass)

let tmapsel = TmMappSel(tmapp, TmVar("sender"))
test_func Gamma.empty CT.empty (Some TNat) (mk_eval tmapsel)

let complex = TmMappAss(tmapp, TmVar("sender"), TmPlus(tone,tmapsel))

let ctenv = (CT.add "Bank" ([], []) (CT.add "EOC" ([(TNat, "a") ; (TBool, "b")], []) CT.empty))
let gammaenv = (Gamma.add "aEOA" TAddress (Gamma.add "x" (TContract("Bank")) Gamma.empty))
let gammaenv2 = (Gamma.add "x" (TNat) Gamma.empty)
let ctenv2 = (CT.add "Bank" ([(TNat, "a") ; (TBool, "b")], [(TNat, "f", [(TNat, "a") ; (TBool, "b")])]) CT.empty)
let ctenv3 = (CT.add "Bank" ([], [(TNat, "deposit" , [])]) (CT.add "EOC" ([(TNat, "a") ; (TBool, "b")], []) CT.empty))
*
(* Auction *)
let ctAuction = (CT.add "Owner" ([], [])
                (CT.add "Client" ([(TNat, "balance")], [(TUnit, "withdraw", [])]) 
                (CT.add "Auction" ([((TMapping(TAddress, TNat)), "pendingReturns") ;
                                (TBool, "ended");
                                (TNat, "highestBid");
                                (TAddress, "highestBidder");
                                (TAddress, "owner") ], 
                                [(TUnit , "init" , []) ; 
                                (TUnit, "end", []) ; 
                                (TUnit, "bid", [(TNat, "amount")]) ;
                                (TUnit, "win", []); 
                                (TUnit, "Withdraw", [])]) CT.empty)))
let gammaAuction = (Gamma.add "aC1" TAddress 
                (Gamma.add "cC1" (TContract("Client")) 
                (Gamma.add "aOwner" TAddress 
                (Gamma.add "cOwner" (TContract("Owner")) 
                (Gamma.add "aC2" TAddress
                (Gamma.add "cC2" (TContract("Client")) 
                (Gamma.add "cAuction" (TContract("Auction"))
                (Gamma.add "auction" (TContract("Auction"))
                (Gamma.add "aAuction" TAddress Gamma.empty)))))))))


(*Bank*)
let ctBank =
            (CT.add "Bank" ([((TMapping(TAddress, TNat)), "balances")],
                            [(TUnit, "constuctor",[((TMapping(TAddress, TNat)),"balances")]); 
                            (TUnit, "deposit",[]);
                            (TNat, "getBalance", []);
                            (TUnit, "transfer", [(TAddress,"to");(TNat,"amount")]);
                            (TUnit, "withdraw", [(TNat,"amount")])
                            ]) CT.empty)
                        
let gammaBank = (Gamma.add "aC1" TAddress
                (Gamma.add "aC2" TAddress
                (Gamma.add "Bank" (TContract("Bank")) 
                (Gamma.add "aBank" TAddress Gamma.empty))))                         
                


(*let typecheck_funcs =*)  

let () = *)
  (* PLUS *)
  (*test_func Gamma.empty CT.empty (Some TNat) (mk_eval tmPlus)*)
  (* MINUS *)
  (*test_func Gamma.empty CT.empty (Some TNat) (mk_eval tmMinus)*)
  (* MULT *)
  (*test_func Gamma.empty CT.empty (Some TNat) (mk_eval tmMult)*)
  (* DIV *)
  (*test_func Gamma.empty CT.empty (Some TNat) (mk_eval tmDiv)*)
  (* EQUALS *)
  (*test_func Gamma.empty CT.empty (Some TBool) (mk_eval tmEquals)*)
  (* GREATEROREQUALS *)
  (*test_func Gamma.empty CT.empty (Some TBool) (mk_eval tmGreaterOrEquals)*)
  (* AND *)
  (*test_func Gamma.empty CT.empty (Some TBool) (mk_eval tmAnd)*)
  (* OR *)
  (*test_func Gamma.empty CT.empty (Some TBool) (mk_eval tmOr)*)
  (* NOT *)
  (*test_func Gamma.empty CT.empty (Some TBool) (mk_eval tmNot)*)
  (* GetParam *)
  (*test_func gammaenv2 CT.empty (Some TBool) (mk_eval tmGetParam)*)
  (* TRUE *)
  (* test_func Gamma.empty CT.empty (Some TBool) (mk_eval ttrue);
  test_func Gamma.empty CT.empty None (mk_eval ttrue); *)
  (* FALSE *)
  (* test_func Gamma.empty CT.empty (Some TBool) (mk_eval tfalse);
  test_func Gamma.empty CT.empty None (mk_eval tfalse); *)
  (* NAT *)
  (* test_func Gamma.empty CT.empty (Some TNat) (mk_eval tone);
  test_func Gamma.empty CT.empty None (mk_eval tone); *)
  (* ADDRESS *)
  (* test_func gammaenv ctenv (Some TAddress) (mk_eval taddress);
  test_func gammaenv ctenv None (mk_eval taddress); *)
  (* CONTRACT *)
  (* test_func gammaenv ctenv (Some (TContract("Bank"))) (mk_eval tcontract);
  test_func gammaenv ctenv None (mk_eval tcontract); *)
  (* UNIT *)
  (* test_func Gamma.empty CT.empty (Some TUnit) (mk_eval (TmValue(VUnit)));
  test_func Gamma.empty CT.empty None (mk_eval (TmValue(VUnit))); *)
  (* VAR *)
  (* test_func gammaenv ctenv (Some (TContract("Bank"))) (mk_eval tx);
  test_func gammaenv ctenv None (mk_eval tx); *)
  (* REVERT *)
  (* test_func gammaenv ctenv (Some (TContract("Bank"))) (mk_eval TmRevert);
  test_func gammaenv ctenv None (mk_eval TmRevert); *)
  (* BAL *)
  (* test_func gammaenv ctenv (Some TNat) (mk_eval tbalance);
  test_func gammaenv ctenv None (mk_eval tbalance); *)
  (* ADDR *)
  (* test_func gammaenv ctenv (Some TAddress) (mk_eval taddress2);
  test_func gammaenv ctenv None (mk_eval taddress2); *)
  (* RETURN *)
  (* test_func gammaenv ctenv (Some TBool) (mk_eval treturn);
  test_func gammaenv ctenv None (mk_eval treturn); *)
  (* SEQ *)
  (* test_func gammaenv ctenv (Some TNat) (mk_seq (mk_eval tdecl) (mk_eval tx));
  test_func gammaenv ctenv None ((mk_eval tdecl) (mk_eval tx)); *)
  (* DECL *)
  (* test_func Gamma.empty ctenv (Some TNat) (mk_eval tdecl);
  test_func Gamma.empty ctenv None (mk_eval tdecl); *) 
  (* IF *)
  (* test_func Gamma.empty ctenv (Some TNat) (mk_eval tif);
  test_func Gamma.empty ctenv None (mk_eval tif); *)
  (* ASS *)
  (* test_func (Gamma.add "x" TNat Gamma.empty) ctenv (Some TNat) (mk_eval tassign);
  test_func (Gamma.add "x" TNat Gamma.empty) ctenv None (mk_eval tassign); *)
  (* MAPPING *)
  (* test_func gammaenv ctenv (Some (TMapping(TNat, TBool))) (mk_eval tmap);
  test_func gammaenv ctenv None (mk_eval tmap); *)
  (* MAPPASS *)
  (* test_func gammaenv ctenv (Some (TMapping(TNat, TBool))) (mk_eval tmapass);
  test_func gammaenv ctenv None (mk_eval tmapass); *)
  (* MAPPSEL *)
  (* test_func gammaenv ctenv (Some TBool) (mk_eval tmapsel);
  test_func gammaenv ctenv None (mk_eval tmapsel);  *)
  (* STATESEL *)
  (* test_func (Gamma.add "aEOA" TAddress (Gamma.add "x" (TContract("EOC")) Gamma.empty)) ctenv (Some TBool) (mk_eval tstatesel);
  test_func (Gamma.add "aEOA" TAddress (Gamma.add "x" (TContract("EOC")) Gamma.empty)) ctenv None (mk_eval tstatesel);  *)
  (* STATEASS *)
  (* test_func (Gamma.add "aEOA" TAddress (Gamma.add "x" (TContract("EOC")) Gamma.empty)) ctenv (Some TBool) (mk_eval tstateass);
  test_func (Gamma.add "aEOA" TAddress (Gamma.add "x" (TContract("EOC")) Gamma.empty)) ctenv None (mk_eval tstateass); *)
  (* NEW *)
  (* test_func (Gamma.add "aEOA" TAddress (Gamma.add "x" (TContract("EOC")) Gamma.empty)) ctenv (Some (TContract("EOC"))) (mk_eval tnew);
  test_func (Gamma.add "aEOA" TAddress (Gamma.add "x" (TContract("EOC")) Gamma.empty)) ctenv None (mk_eval tnew); *)
  (* FUN *)
  (* test_func (Gamma.add "x" (TContract("Bank")) Gamma.empty) (CT.add "Bank" ([(TNat, "a") ; (TBool, "b")], [(TNat, "f", [(TNat, "a") ; (TBool, "b")])]) CT.empty) (Some (TFun([TNat; TBool], TNat))) (mk_eval tfun);
  test_func (Gamma.add "x" (TContract("Bank")) Gamma.empty) (CT.add "Bank" ([(TNat, "a") ; (TBool, "b")], [(TNat, "f", [(TNat, "a") ; (TBool, "b")])]) CT.empty) None (mk_eval tfun); *)
  (* CALL *)
(*   test_func gammaenv2 ctenv2 (Some TNat) (mk_eval tcall);
  test_func gammaenv2 ctenv2 None (mk_eval tcall);  *)
  (* CALLTOPLEVEL *)
  (* test_func gammaenv ctenv2 (Some TNat) (mk_eval tcalltop);
  test_func gammaenv ctenv2 None (mk_eval tcalltop); *) 
  (* TRANSFER *)
  (* test_func gammaenv ctenv2 (Some TUnit) (mk_eval ttransfer);
  test_func gammaenv ctenv2 None (mk_eval ttransfer); *)



(* 
  test_func (Gamma.add "EOC" (TContract("EOC")) Gamma.empty) ctenv3 None (mk_eval (TmDecl( TContract("EOC") ,"x" , (TmNew("EOC", (TmValue(VCons(500))), [tone; ttrue])), (TmDecl( TContract("Bank") ,"y" , (TmNew("Bank", (TmValue(VCons(0))), [])), (TmCall((TmValue(VContract("y")), "deposit", (TmValue(VCons(500))), [])))))))); *)
(* PIRO *)
  (* test_func (Gamma.add "EOC" (TContract("EOC")) Gamma.empty) ctenv3 (Some TNat) (mk_eval (TmDecl( TContract("EOC") ,"x" , (TmNew("EOC", (TmValue(VCons(500))), [tone; ttrue])), (TmDecl( TContract("Bank") ,"y" , (TmNew("Bank", (TmValue(VCons(0))), [])), (TmCallTop((TmValue(VContract("y")), "deposit", (TmValue(VCons(500))), TmAddress(TmValue(VContract("x"))) ,[])))))))); *)

  (*(test_func gammaAuction ctAuction None (mk_eval 
  (TmDecl( (TContract("Owner")) , "owner", (TmNew("Owner", (TmValue(VCons(500))), [] )), 
  (TmDecl ( (TContract("Client")), "c1" , (TmNew("Client", (TmValue(VCons(500))), [(TmValue(VCons(500)))] )) , 
  (TmDecl ((TContract("Client")), "c2" , (TmNew("Client", (TmValue(VCons(500))), [(TmValue(VCons(500)))] )) , 
  (TmDecl ((TContract("Auction")), "auction", 
  (TmNew("Auction", (TmValue(VCons(0))), [(TmValue(VMapping([( (VAddress("aC1")) , VCons(0)); ((VAddress("aC1")), VCons(0))]))) ; tfalse ; tzero ; (TmVar("aAuction")); (TmVar("aAuction"))] )) , 
  (TmSeq
  ((TmCallTop((TmValue(VContract("auction")), "init", (TmValue(VCons(0))), (TmAddress(TmValue(VContract("owner")))) ,[] ))), 
  (TmCallTop( (TmValue(VContract("auction"))) , "end" , tzero , (TmAddress(TmValue(VContract("c1")))) , []))) )) ))))))))) 
  (* (mk_eval (TmCallTop((TmValue(VContract("auction")), "init", (TmValue(VCons(0))), (TmAddress(TmValue(VContract("owner")))) ,[] ))))) *)*)
  (* (TmCallTop( (TmValue(VContract("auction"))) , "end" , tzero , (TmAddress(TmValue(VContract("c1")))) , []))) ) *)
  
  (* (TmCallTop( (TmValue(VContract("auction"))) , "init" , tzero , (TmAddress(TmValue(VContract("owner")))), [] ))   )))) ))) )) *)

  (*------------------------------------ Bank-------------------------------------*)

(*
(test_func gammaBank ctBank None (mk_eval
(TmDecl ((TContract("Bank")), "bank", 
(TmNew("Bank", (TmValue(VCons(0))), [(TmValue(VMapping([( (VAddress("aC1")) , VCons(0))])))] )), 
(TmSeq(
(TmCallTop((TmValue(VContract("bank")), "constuctor", (TmValue(VCons(0))), (TmAddress(TmValue(VContract("bank")))) ,[(TmValue(VMapping([( (VAddress("aC1")) , VCons(0))])))] ))),
(TmSeq((TmCallTop((TmValue(VContract("bank")), "deposit", (TmValue(VCons(5))), (TmAddress(TmValue(VContract("bank")))) ,[] ))),
(TmSeq((TmCallTop((TmValue(VContract("bank")), "getBalance", (TmValue(VCons(0))), (TmAddress(TmValue(VContract("bank")))) ,[] ))), 
(TmCallTop((TmValue(VContract("bank")), "transfer", (TmValue(VCons(5))), (TmAddress(TmValue(VContract("bank")))) ,[TmValue(VAddress("aC1")); TmValue(VCons(10))] ))) 
))))))))))

*)




(*-----------------------------------------------------------------------------Examples-------------------------------------------------------------------------------*)
(* Bank *)
let sender : term = TmGetParam("sender");;
let msg_value : term = TmVar("Msg_value");;
let balances = TmVar("Balances");;

let param_balances : params = (TMapping(TAddress, TNat), "balances_param");;
let param_balances_val : term = (TmGetParam("balances_param"));;
let bank_constructor : construtor_ = ([param_balances],TmSeq(TmAssign("Balances", param_balances_val), TmReturn(TmValue(VUnit)) ));;

let deposit : func = { requires = TmValue(VTrue); return_type = TUnit; func_name = "deposit"; params = []; body = TmSeq( TmMappAss(balances, sender, TmPlus( TmMappSel(balances, sender), msg_value)), TmReturn(TmValue(VUnit)))  };;

let get_balance : func = { requires = TmValue(VTrue); return_type = TNat; func_name = "get_balance"; params = []; body = TmReturn( TmMappSel(balances, sender) )  };;

let param_to : params = (TAddress, "to");;
let param_to_val : term = TmGetParam("to");;
let param_amount :params = (TNat, "amount");;
let param_amount_val : term = TmGetParam("amount");;
let transfer : func = {requires = TmValue(VTrue); return_type = TUnit; func_name = "transfer"; params = [param_to; param_amount];
body = TmSeq( TmIf( GreaterOrEquals(TmMappSel(balances, sender), param_amount_val), 
TmSeq( TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender),param_amount_val)),
TmSeq(TmMappAss(balances, param_to_val, TmPlus( TmMappSel(balances, param_to_val),param_amount_val)),TmReturn(TmValue(VUnit)))), 
TmReturn(TmValue(VUnit))), TmReturn(TmValue(VUnit))) };;

let param_withdraw_amount : params = (TNat, "W_amount");;
let param_withdraw_amount_val : term = TmGetParam("W_amount");;
let withdraw : func = {requires = TmValue(VTrue); return_type = TUnit; func_name = "withdraw"; params = [param_withdraw_amount]; body =TmSeq( TmIf( GreaterOrEquals(TmMappSel(balances, sender), param_withdraw_amount_val), 
TmSeq(TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender),param_withdraw_amount_val)),
      TmTransfer( sender,param_withdraw_amount_val ) ), 
      TmReturn(TmValue(VUnit))), TmReturn(TmValue(VUnit))) };;

(* test bank*)
let ctBank =
  (CT.add "Bank" ([((TNat), "Msg_value"); (TMapping(TAddress, TNat), "Balances");
                        (TMapping(TAddress, TNat), "balances_param");
                        ((TNat), "amount"); ((TAddress), "to");
                        ((TNat), "W_amount");
                        ],
                  [(TUnit, "bank_constructor",[((TNat), "msg_value"); ((TAddress), "sender"); ((TMapping(TAddress, TNat)), "balances_param");
                  ((TAddress), "to");
                  ((TNat), "amount");((TNat), "W_amount");]); 
                  (TUnit, "transfer",[((TNat), "amount");((TAddress), "to")]);
                  (TUnit, "withdraw",[((TNat), "W_amount")]);
                  (TNat, "deposit", []);
                  (TNat, "get_balance", []);
                  ]) CT.empty);;
              
let gammaBank = 
      (Gamma.add "Msg_value" TNat
      (Gamma.add "param_init" TAddress
      (Gamma.add "param_unsafe" TAddress
      (Gamma.add "Balances" (TMapping(TAddress, TNat))
      (Gamma.add "balances_param" (TMapping(TAddress, TNat))
      (Gamma.add "amount" TNat
      (Gamma.add "to" TAddress
      (Gamma.add "sender" TAddress
      (Gamma.add "W_amount" TNat
      (Gamma.add "Bank" (TContract("Bank")) 
      (Gamma.add "aBank" TAddress Gamma.empty)))))))))));;

let contractBank : contract_tc = {
  name = "Bank";
  init = ( [((TAddress,"param_init"))] ,GreaterOrEquals(TmMappSel(TmVar("Balances"), TmGetParam("param_init") ), TmValue(VCons(0))));
  invariant = ([(TAddress, "param_unsafe")],Less(TmMappSel(TmVar("Balances"), TmGetParam("param_unsafe") ), TmValue(VCons(0))));
  behavioral_types = [];
  vars = [(TmVar("Msg_value"), TNat);(TmVar("Balances"), TMapping(TAddress,TNat))];
  cons = bank_constructor;
  funcs = [deposit; get_balance; transfer; withdraw]
};;



let contractBank : contract_tc = {
  name = "Bank";
  init = ( [((TAddress,"param_init"))] ,GreaterOrEquals(TmMappSel(TmVar("Balances"), TmGetParam("param_init") ), TmValue(VCons(0))));
  invariant = ([(TAddress, "param_unsafe")],Less(TmMappSel(TmVar("Balances"), TmGetParam("param_unsafe") ), TmValue(VCons(0))));
  behavioral_types = [];
  vars = [(TmVar("Msg_value"), TNat);(TmVar("Balances"), TMapping(TAddress,TNat))];
  cons = bank_constructor;
  funcs = [deposit; get_balance; transfer; withdraw]
};;
      
(* Marketplace-azure *)

let ctMark =
  (CT.add "Marketplace" ([((TAddress), "InstanceOwner");((TString), "Description");
                        ((TNat), "AskingPrice"); ((TAddress), "InstanceBuyer");
                        ((TNat), "OfferPrice");
                        ((TString), "param_description");((TNat), "param_price");
                        ((TNat), "param_offer")],
                  [(TUnit, "marketplace_constructor",[((TString), "param_description"); ((TAddress), "OfferPrice")]); 
                  (TUnit, "make_offer",[(TNat), "param_offer"]);
                  (TNat, "accept", []);
                  (TUnit, "reject", []);
                  ]) CT.empty);;

let gammaMark = (Gamma.add "InstanceOwner" TAddress
(Gamma.add "CurrentState" TState
(Gamma.add "ItemAvailable" TState
(Gamma.add "OfferPlaced" TState
(Gamma.add "Accept" TState
(Gamma.add "Description" TString
(Gamma.add "AskingPrice" TNat
(Gamma.add "InstanceBuyer" TAddress
(Gamma.add "OfferPrice" TNat
(Gamma.add "sender" TAddress
(Gamma.add "param_description" TString
(Gamma.add "param_price" TNat
(Gamma.add "param_offer" TNat
(Gamma.add "Mark" (TContract("Mark")) 
(Gamma.add "aMark" TAddress Gamma.empty)))))))))))))));;

(*-----------------------------------------------------------------------------MARKETPLACE-----------------------------------------------------------------------------*)
let instanceOwner : term = TmVar("InstanceOwner");;
let description : term = TmVar("Description");;
let askingPrice : term = TmVar("AskingPrice");;
let instanceBuyer : term = TmVar("InstanceBuyer");;
let offerPrice : term = TmVar("OfferPrice");;
let sender : term = TmGetParam("sender");;
let param_description : params = (TString, "param_description");;
let param_description_val : term = TmGetParam("param_description");;
let param_price : params = (TNat,"param_price");;
let param_price_val : term = TmGetParam("param_price");;
let marketplace_constructor : construtor_ = ([param_description;param_price], TmSeq(TmSeq(TmAssign("CurrentState", TmGetState("ItemAvailable")) , TmSeq(TmAssign("InstanceOwner",sender), 
TmSeq(TmAssign("AskingPrice", param_price_val), TmAssign("Description", param_description_val)))), TmReturn(TmValue(VUnit)) ) );;

let param_offer : params = (TNat, "param_offer");;
let param_offer_val : term = TmGetParam("param_offer");;
let make_offer : func = {requires = And(Equals(TmGetParam("sender"), TmVar("InstanceBuyer")),And(Equals(TmGetState("ItemAvailable"), TmVar("CurrentState")),
 Greater(TmGetParam("param_offer"), TmVar("AskingPrice")))); return_type = TUnit; func_name = "make_offer"; params = [param_offer]; 
                      body = TmSeq( TmSeq( TmIf(Equals(param_offer_val, TmValue(VCons(0))), TmRevert, TmReturn(TmValue(VUnit))),
                      TmSeq( TmIf(Equals(sender, instanceOwner), TmRevert, TmReturn(TmValue(VUnit))), TmSeq( TmAssign("InstanceBuyer", sender), 
                      TmSeq( TmAssign("OfferPrice", param_offer_val), TmAssign("CurrentState", TmGetState("OfferPlaced")) ) ))), TmReturn(TmValue(VUnit)))};;
                
let param_offer_r : params = (TNat, "param_offer_r");;
let param_offer_r_val : term = TmGetParam("param_offer");;                      
let reject : func = {requires = And(Equals(TmGetParam("sender"), TmVar("InstanceOwner")),
                                And(Equals(TmGetState("OfferPlaced"), TmVar("CurrentState")),Not(Equals(param_offer_r_val, TmValue(VCons(0)))))); 
return_type = TUnit; func_name = "reject"; params = [param_offer_r]; body = TmSeq(TmAssign("InstanceBuyer", TmValue(VAddress("sender"))) , 
TmSeq( TmAssign("CurrentState", TmGetState("ItemAvailable")),TmReturn(TmValue(VUnit))))   };;

let param_offer_a : params = (TNat, "param_offer_a");;
let param_offer_a_val : term = TmGetParam("param_offer");;   
let accept : func = { requires = And(Equals(TmGetState("OfferPlaced"), TmVar("CurrentState")),(Equals( sender, instanceOwner)));
                      return_type = TUnit; func_name = "accept"; params = [param_offer_a]; body = TmSeq(TmIf((Equals(param_offer_a_val, TmValue(VCons(0)))), TmRevert, 
                                                        TmReturn(TmValue(VUnit))), TmSeq(TmAssign("CurrentState", TmGetState("Accept")),TmReturn(TmValue(VUnit))))};;  
let contractMark : contract_tc = {
  name = "Marketplace";
  init = ( [], And( Equals(TmVar("CurrentState"), TmGetState("ItemAvailable")), And(Greater( TmVar("AskingPrice"), TmValue(VCons(0))), Greater(TmVar("OfferPrice"), TmVar("AskingPrice")))));
  invariant = ([],Greater(TmVar("OfferPrice"), TmVar("AskingPrice"))); 
  behavioral_types = [TmGetState("ItemAvailable"); TmGetState("OfferPlaced"); TmGetState("Accept")];
  vars = [(TmVar("CurrentState"),TState); (TmVar("InstanceOwner"), TAddress);(TmVar("Description"), TString); (TmVar("AskingPrice"), TNat);
          (TmVar("InstanceBuyer"), TAddress); (TmVar("OfferPrice"), TNat)];
  cons = marketplace_constructor;
  funcs = [make_offer; reject; accept]
};;
                

(* Telemetry-azure *)
let sender : term = TmGetParam("sender");;
let owner : term = TmVar("Owner");;
let counterParty : term = TmVar("CounterParty");;
let device : term = TmVar("Device");;
let complianceStatus : term = TmVar("ComplianceStatus");;
let max_temp : term = TmVar("Max_Temperature");;
let min_temp : term = TmVar("Min_Temperature");;

let param_device : params = (TAddress,"param_device");;
let param_device_val : term = TmGetParam("param_device");;
let param_max_temp : params = (TAddress,"param_max_temp");;
let param_max_temp_val : term = TmGetParam("param_max_temp");;
let param_min_temp : params = (TAddress,"param_min_temp");;
let param_min_temp_val : term = TmGetParam("param_min_temp");;
let telemetry_constructor = ([param_device;param_max_temp; param_min_temp],
                            TmSeq(TmSeq( TmAssign("ComplianceStatus",TmValue(VTrue)) , TmSeq( TmAssign("CounterParty", sender), 
                            TmSeq(TmAssign("Owner", sender) , TmSeq(TmAssign("Device", param_device_val) , 
                            TmSeq(TmAssign("Max_Temperature", param_max_temp_val ) , TmAssign("Min_Temperature", param_min_temp_val )))) ) ), TmReturn(TmValue(VUnit)) ) );;  
 
let param_temp : params = (TNat, "param_temp");;     
let param_temp_val : term = TmGetParam("param_temp");;                           
let ingest_telemetry : func = {requires = And( Equals(TmGetParam("sender"), TmVar("Device")),Or( Equals(TmVar("CurrentState"), TmGetState("Created")), Equals(TmVar("CurrentState"), TmGetState("InTransit")) )); return_type = TUnit; func_name = "ingest_telemetry"; params = [param_temp]; 
body = TmSeq( TmSeq(TmIf( Or( Greater(param_temp_val, max_temp) , Less( param_temp_val, min_temp)), TmAssign("ComplianceStatus", TmValue(VFalse)) , TmAssign("ComplianceStatus", TmValue(VTrue))),
 TmSeq(TmIf( Not(Equals(sender, device)), TmRevert, TmReturn(TmValue(VUnit))), TmIf( Or( Greater(param_temp_val, max_temp), Less(param_temp_val, min_temp)),
 TmAssign("ComplianceStatus",TmValue(VFalse)),TmReturn(TmValue(VUnit))))),TmReturn(TmValue(VUnit)))  };;


let param_new_counter_party : params = (TAddress, "param_new_counter_party");;
let param_new_counter_party_val : term = TmGetParam("param_new_counter_party");;                         
let transfer_responsability : func = {requires = And( Equals(TmGetParam("sender"), TmVar("CounterParty")) ,Or( Equals(TmVar("CurrentState"), TmGetState("Created")), Equals(TmVar("CurrentState"), TmGetState("InTransit")))); return_type = TUnit; func_name = "transfer_responsability"; params = [param_new_counter_party]; 
                              body = TmSeq(
                                          TmIf( Equals(TmVar("CurrentState"), TmGetState("Created")), TmAssign("CurrentState", TmGetState("InTransit")) , TmAssign("CurrentState", TmGetState("Created"))),                               
                                          TmSeq( 
                                            TmSeq( TmIf( And(Not(Equals(sender,param_new_counter_party_val )),Not(Equals(sender,counterParty))), TmRevert ,TmReturn(TmValue(VUnit))),
                                            TmSeq(TmIf(Equals(param_new_counter_party_val,device), TmRevert, TmReturn(TmValue(VUnit))),TmAssign("CounterParty", param_new_counter_party_val) ) ) , TmReturn(TmValue(VUnit)))) };;

let complete : func = {requires =  (Equals(sender,owner )); return_type = TUnit; func_name = "complete"; params = []; body = TmSeq( TmAssign("CurrentState", TmGetState("Completed")) ,TmReturn(TmValue(VUnit)) ) };;
  
                 
let gammaTelemetry = (Gamma.add "sender" TAddress
(Gamma.add "Owner" TAddress
(Gamma.add "CurrentState" TState
(Gamma.add "CounterParty" TAddress
(Gamma.add "param_device" TAddress
(Gamma.add "ComplianceStatus" TBool
(Gamma.add "Max_Temperature" TNat
(Gamma.add "Min_Temperature" TNat
(Gamma.add "Device" TAddress
(Gamma.add "param_max_temp" TNat
(Gamma.add "param_min_temp" TNat
(Gamma.add "param_temp" TNat
(Gamma.add "Created" TState
(Gamma.add "InTransit" TState
(Gamma.add "OutOfCompliance" TState
(Gamma.add "Completed" TState
(Gamma.add "param_new_counter_party" TAddress
(Gamma.add "Telemetry" (TContract("Telemetry")) 
(Gamma.add "aTelemetry" TAddress Gamma.empty)))))))))))))))))));;

let contractTelemetry : contract_tc = {
  name = "Telemetry";
  init = ([],And(Greater(TmVar("Max_Temperature"), TmVar("Min_Temperature")),And(Greater(TmVar("Min_Temperature"), TmValue(VCons(0))), And( Equals(TmVar("ComplianceStatus"), TmValue(VTrue)), Equals(TmVar("CurrentState"),TmGetState("Created"))))));
  invariant = ([],Greater(TmVar("Max_Temperature"), TmVar("Min_Temperature")));
  behavioral_types = [TmGetState("Created"); TmGetState("InTransit"); TmGetState("OutOfCompliance");TmGetState("Completed")];
  vars = [(TmVar("Owner"),TAddress); (TmVar("CurrentState"), TState); (TmVar("CounterParty"), TAddress); (TmVar("Device"), TAddress);
          (TmVar("ComplianceStatus"), TBool); (TmVar("Max_Temperature"), TNat); (TmVar("Min_Temperature"), TNat)];
  cons = telemetry_constructor;
  funcs = [ingest_telemetry; transfer_responsability; complete]
};;
          
let ctTelemetry =
  (CT.add "Telemetry" ([((TAddress), "Owner");
                        ((TAddress), "CounterParty"); ((TAddress), "param_device");
                        ((TBool), "ComplianceStatus"); ((TNat), "Max_Temperature");
                        ((TNat), "Min_Temperature");((TAddress), "Device");
                        ((TNat), "param_max_temp");((TNat), "param_min_temp");
                        ((TNat), "param_temp");(TAddress, "param_new_counter_party")    ],
                  [(TUnit, "telemetry_constructor",[((TAddress), "param_device"); ((TNat), "param_max_temp");((TNat), "param_min_temp");]); 
                  (TUnit, "ingest_telemetry",[((TNat), "param_temp")]);
                  (TNat, "transfer_responsability", [((TAddress), "param_new_counter_party")]);
                  (TUnit, "complete", [])
                  ]) CT.empty);;


(* digital locker *)

              
let gammaDL = (Gamma.add "sender" TAddress
(Gamma.add "Owner" TAddress
(Gamma.add "CurrentState" TState
(Gamma.add "BankAgent" TAddress
(Gamma.add "LockerId" TString
(Gamma.add "CurrentAuthorizedUser" TAddress
(Gamma.add "Exp_Date" TNat
(Gamma.add "Image" TString
(Gamma.add "TPRequestor" TAddress
(Gamma.add "LockerStatus" TString
(Gamma.add "param_locker_id" TString
(Gamma.add "param_image" TString
(Gamma.add "param_tp" TAddress
(Gamma.add "param_exp_date" TNat
(Gamma.add "param_bank_agent" TAddress
(Gamma.add "Requested" TState
(Gamma.add "DocumentReview" TState
(Gamma.add "AvailableToShare" TState
(Gamma.add "SharingWithTp" TState
(Gamma.add "SharingRP" TState
(Gamma.add "Terminated" TState
(Gamma.add "Pending" TString
(Gamma.add "Rejected" TString
(Gamma.add "Shared" TString
(Gamma.add "Approved" TString
(Gamma.add "Available" TString
(Gamma.add "DL" (TContract("DL")) 
(Gamma.add "aDL" TAddress Gamma.empty))))))))))))))))))))))))))));;

let sender : term = TmGetParam("sender");;
let owner : term = TmVar("Owner");;
let currentState : term = TmVar("CurrentState");;
let bank_agent : term = TmVar("BankAgent");;
let lockerId : term = TmVar("LockerId");;
let curentAuthorizedUser : term = TmVar("CurrentAuthorizedUser");;
let exp_Date : term = TmVar("Exp_Date");;
let image : term = TmVar("Image");;
let tpRequestor : term = TmVar("TPRequestor");;
let lockerStatus : term = TmVar("LockerStatus");;


let param_bank : params = (TAddress,"param_bank_agent");;
let param_bank_val : term = TmGetParam("param_bank_agent");;
let dl_constructor = ([param_bank], TmSeq(TmSeq(TmAssign("Owner", TmGetParam("sender")), TmSeq( TmAssign("CurrentState",TmGetState("Requested")), TmAssign("BankAgent", param_bank_val) )), TmReturn(TmValue(VUnit))));;
                      
let begin_process_review : func = {requires = And((Equals(owner,sender)),Equals(TmGetState("Requested"),currentState)); return_type = TUnit; func_name = "begin_process_review"; params = []; 
body =TmSeq( TmSeq( TmAssign("BankAgent", sender),TmSeq(TmAssign("LockerStatus",TmValue(VString("Pending"))),TmAssign("CurrentState", TmGetState("DocumentReview"))) ), TmReturn(TmValue(VUnit))) };;


let reject_application : func = {requires = And((Equals(bank_agent,sender)),Equals(TmGetState("DocumentReview"),currentState)); return_type = TUnit; func_name = "reject_application"; params = []; 
body =TmSeq( TmSeq( TmAssign("BankAgent", sender),TmSeq(TmAssign("LockerStatus",TmValue(VString("Rejected"))),TmAssign("CurrentState", TmGetState("DocumentReview"))) ), TmReturn(TmValue(VUnit))) };;

let param_image : params = (TString,"param_image");;
let param_image_val : term = TmGetParam("param_image");;
let param_locker_id : params = (TString,"param_locker_id");;
let param_locker_id_val : term = TmGetParam("param_locker_id");;
let upload_documents : func = {requires = And((Equals(bank_agent,sender)),Equals(TmGetState("DocumentReview"),currentState)); return_type = TUnit; func_name = "upload_documents"; params = [param_image; param_locker_id]; 
body =TmSeq( TmSeq( TmAssign("LockerStatus",TmValue(VString("Approved"))),TmSeq(TmAssign("Image", param_image_val) , TmSeq(TmAssign("LockerId", param_locker_id_val) , TmAssign("CurrentState", TmGetState("AvailableToShare"))))), TmReturn(TmValue(VUnit))) };;

let param_tp : params = (TAddress,"param_tp");;
let param_tp_val : term = TmGetParam("param_tp");;
let param_exp_date : params = (TNat,"param_exp_date");;
let param_exp_date_val : term = TmGetParam("param_exp_date");;
let share_with_tp : func = {requires = And((Equals(owner,sender)),Equals(TmGetState("AvailableToShare"),currentState)); return_type = TUnit; func_name = "share_with_tp"; params = [param_tp; param_exp_date]; 
body =TmSeq( TmSeq(TmAssign("TPRequestor", param_tp_val),TmSeq( TmAssign("LockerStatus",TmValue(VString("Shared"))),TmSeq(TmAssign("Exp_Date", param_exp_date_val) , TmSeq(TmAssign("CurrentAuthorizedUser", param_tp_val) , TmAssign("CurrentState", TmGetState("SharingWithTp")))))), TmReturn(TmValue(VUnit))) };;

let accept_s_request : func = {requires = And(Equals(owner,sender), Equals(currentState, TmGetState("SharingRP"))); return_type = TUnit; func_name = "accept_s_request"; params = []; 
body =TmSeq( TmSeq(TmAssign("CurrentAuthorizedUser", tpRequestor),TmAssign("CurrentState", TmGetState("SharingWithTp"))), TmReturn(TmValue(VUnit))) };;

let reject_s_request : func = {requires = And(Equals(owner,sender),Equals(currentState, TmGetState("SharingRP"))); return_type = TUnit; func_name = "reject_s_request"; params = []; 
body =TmSeq( TmSeq(TmAssign("LockerStatus", TmValue(VString("Available"))),TmAssign("CurrentState", TmGetState("SharingWithTp"))), TmReturn(TmValue(VUnit))) };;

let request_l_access : func = {requires = And(Not(Equals(owner,sender)),Equals(currentState, TmGetState("SharingRP"))); return_type = TUnit; func_name = "request_l_access"; params = []; 
body =TmSeq( TmSeq(TmAssign("TPRequestor",sender),TmAssign("CurrentState", TmGetState("SharingRP"))), TmReturn(TmValue(VUnit))) };;

let release_l_access : func = {requires = And(Equals(curentAuthorizedUser,sender), Equals(currentState, TmGetState("SharingWithTp"))); return_type = TUnit; func_name = "release_l_access"; params = []; 
body =TmSeq( TmSeq(TmAssign("LockerStatus",TmValue(VString("Available"))),TmAssign("CurrentState", TmGetState("AvailableToShare"))), TmReturn(TmValue(VUnit))) };;

let revoke_access : func = {requires = And(Equals(owner,sender),Equals(currentState, TmGetState("SharingWithTp"))); return_type = TUnit; func_name = "revoke_access"; params = []; 
body =TmSeq( TmSeq(TmAssign("LockerStatus",TmValue(VString("Available"))),TmAssign("CurrentState", TmGetState("AvailableToShare"))), TmReturn(TmValue(VUnit))) };;


let terminate : func = {requires = And(And(Not(Equals(currentState, TmGetState("DocumentReview"))),Not(Equals(currentState, TmGetState("Requested")))),Equals(owner,sender)); return_type = TUnit; func_name = "terminate"; params = []; 
body =TmSeq( TmSeq(TmAssign("LockerStatus",TmValue(VString("Available"))),TmAssign("CurrentState", TmGetState("Terminated"))), TmReturn(TmValue(VUnit))) };;




  let contractDL : contract_tc = {
  name = "DL";
  init = ([], Equals(TmGetState("Requested"), currentState));
  invariant = ([],TmValue(VTrue));
  behavioral_types = [TmGetState("DocumentReview"); TmGetState("Requested"); TmGetState("AvailableToShare");TmGetState("SharingWithTp");TmGetState("SharingRP");TmGetState("Terminated")];
  vars = [(TmVar("Owner"),TAddress); (TmVar("CurrentState"), TState); (TmVar("BankAgent"), TAddress); (TmVar("LockerId"), TString);
          (TmVar("CurrentAuthorizedUser"), TAddress); (TmVar("Exp_Date"), TNat); (TmVar("Image"), TString);(TmVar("TPRequestor"), TAddress);(TmVar("LockerStatus"), TString)];
  cons = dl_constructor;
  funcs = [begin_process_review; reject_application; upload_documents;share_with_tp;accept_s_request;reject_s_request;request_l_access;release_l_access;revoke_access;terminate];
};;

     
let ctDL =
  (CT.add "DL" ([((TAddress), "Owner");
                        ((TState), "CurrentState"); ((TAddress), "BankAgent");
                        ((TString), "LockerId"); ((TAddress), "CurrentAuthorizedUser");
                        ((TNat), "Exp_Date");((TString), "Image");
                        ((TAddress), "TPRequestor");((TNat),  "LockerStatus");
                        ((TNat), "param_temp");(TNat, "LockerStatus")    ],
                  [(TUnit, "dl_constructor",[((TAddress), "param_bank_agent");]); 
                  (TUnit, "begin_review",[]);
                  (TUnit, "rejec_application", []);
                  (TUnit, "upload_documents", [((TString), "param_locker_id"); ((TString), "param_image")]);
                  (TUnit, "share_with_tp", [((TAddress), "param_tp"); ((TNat), "param_exp_date")]);
                  (TUnit, "accept_s_request", []);
                  (TUnit, "reject_s_request", []);
                  (TUnit, "request_l_access", []);
                  (TUnit, "release_l_access", []);
                  (TUnit, "revoke_access", []);
                  (TUnit, "terminate", [])
                  ]) CT.empty);;



(*place your code here :) *)

let ctMark =
  (CT.add "Marketplace" ([((TAddress), "InstanceOwner");((TString), "Description");
                        ((TNat), "AskingPrice"); ((TAddress), "InstanceBuyer");
                        ((TNat), "OfferPrice");
                        ((TString), "param_description");((TNat), "param_price");
                        ((TNat), "param_offer")],
                  [(TUnit, "marketplace_constructor",[((TString), "param_description"); ((TAddress), "OfferPrice")]); 
                  (TUnit, "make_offer",[(TNat), "param_offer"]);
                  (TNat, "accept", []);
                  (TUnit, "reject", []);
                  ]) CT.empty);;

let gammaMark = (Gamma.add "InstanceOwner" TAddress
(Gamma.add "CurrentState" TState
(Gamma.add "ItemAvailable" TState
(Gamma.add "OfferPlaced" TState
(Gamma.add "Accept" TState
(Gamma.add "Description" TString
(Gamma.add "AskingPrice" TNat
(Gamma.add "InstanceBuyer" TAddress
(Gamma.add "OfferPrice" TNat
(Gamma.add "sender" TAddress
(Gamma.add "param_description" TString
(Gamma.add "param_price" TNat
(Gamma.add "param_offer" TNat
(Gamma.add "Mark" (TContract("Mark")) 
(Gamma.add "aMark" TAddress Gamma.empty)))))))))))))));;

(*-----------------------------------------------------------------------------MARKETPLACE-----------------------------------------------------------------------------*)
let instanceOwner : term = TmVar("InstanceOwner");;
let description : term = TmVar("Description");;
let askingPrice : term = TmVar("AskingPrice");;
let instanceBuyer : term = TmVar("InstanceBuyer");;
let offerPrice : term = TmVar("OfferPrice");;
let sender : term = TmGetParam("sender");;
let param_description : params = (TString, "param_description");;
let param_description_val : term = TmGetParam("param_description");;
let param_price : params = (TNat,"param_price");;
let param_price_val : term = TmGetParam("param_price");;
let marketplace_constructor : construtor_ = ([param_description;param_price], TmSeq(TmSeq(TmAssign("CurrentState", TmGetState("ItemAvailable")) , TmSeq(TmAssign("InstanceOwner",sender), 
TmSeq(TmAssign("AskingPrice", param_price_val), TmAssign("Description", param_description_val)))), TmReturn(TmValue(VUnit)) ) );;

let param_offer : params = (TNat, "param_offer");;
let param_offer_val : term = TmGetParam("param_offer");;
let make_offer : func = {requires = And(Equals(TmGetParam("sender"), TmVar("InstanceBuyer")),And(Equals(TmGetState("ItemAvailable"), TmVar("CurrentState")),
 Greater(TmGetParam("param_offer"), TmVar("AskingPrice")))); return_type = TUnit; func_name = "make_offer"; params = [param_offer]; 
                      body = TmSeq( TmSeq( TmIf(Equals(param_offer_val, TmValue(VCons(0))), TmRevert, TmReturn(TmValue(VUnit))),
                      TmSeq( TmIf(Equals(sender, instanceOwner), TmRevert, TmReturn(TmValue(VUnit))), TmSeq( TmAssign("InstanceBuyer", sender), 
                      TmSeq( TmAssign("OfferPrice", param_offer_val), TmAssign("CurrentState", TmGetState("OfferPlaced")) ) ))), TmReturn(TmValue(VUnit)))};;
                
let param_offer_r : params = (TNat, "param_offer_r");;
let param_offer_r_val : term = TmGetParam("param_offer");;               
let reject : func = {requires = And(Equals(TmGetParam("sender"), TmVar("InstanceOwner")),
                                And(Equals(TmGetState("OfferPlaced"), TmVar("CurrentState")),Not(Equals(param_offer_r_val, TmValue(VCons(0)))))); 
return_type = TUnit; func_name = "reject"; params = [param_offer_r]; body = TmSeq(TmAssign("InstanceBuyer", TmValue(VAddress("sender"))) , 
TmSeq( TmAssign("CurrentState", TmGetState("ItemAvailable")),TmReturn(TmValue(VUnit))))   };;

let param_offer_a : params = (TNat, "param_offer_a");;
let param_offer_a_val : term = TmGetParam("param_offer");;
let accept : func = { requires = And(Equals(TmGetState("OfferPlaced"), TmVar("CurrentState")),(Equals( sender, instanceOwner)));
                      return_type = TUnit; func_name = "accept"; params = [param_offer_a]; body = TmSeq(TmIf((Equals(param_offer_a_val, TmValue(VCons(0)))), TmRevert, 
                                                        TmReturn(TmValue(VUnit))), TmSeq(TmAssign("CurrentState", TmGetState("Accept")),TmReturn(TmValue(VUnit))))};;   
let contractMark : contract_tc = {
  name = "Marketplace";
  init = ( [], And( Equals(TmVar("CurrentState"), TmGetState("ItemAvailable")), And(Greater( TmVar("AskingPrice"), TmValue(VCons(0))), Greater(TmVar("OfferPrice"), TmVar("AskingPrice")))));
  invariant = ([],Greater(TmVar("OfferPrice"), TmVar("AskingPrice"))); 
  behavioral_types = [TmGetState("ItemAvailable"); TmGetState("OfferPlaced"); TmGetState("Accept")];
  vars = [(TmVar("CurrentState"),TState); (TmVar("InstanceOwner"), TAddress);(TmVar("Description"), TString); (TmVar("AskingPrice"), TNat);
          (TmVar("InstanceBuyer"), TAddress); (TmVar("OfferPrice"), TNat)];
  cons = marketplace_constructor;
  funcs = [make_offer; reject; accept];
};;
                


typecheck_contract ctMark gammaMark contractMark;;
(* typecheck_contract ctDL gammaDL contractDL; *)
(*typecheck_contract ctTelemetry gammaTelemetry contractTelemetry;*)
(*typecheck_contract ctBank gammaBank contractBank;;*)

