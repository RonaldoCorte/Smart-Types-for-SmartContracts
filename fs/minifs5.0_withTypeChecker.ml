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

 
type term = 
  | TmValue of values          (* v *)     (*hasInCubicle*)
  | TmVar of string            (* x *)     (*hasInCubicle*)
  | TmGetParam of string
  | TmBalance of term           (* balance(e) *)
  | TmAddress of term                       (* address(e) *)
  | TmMappSel of term * term * typ     (* e[e] *)  (*hasInCubicle*)
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
  | TmAssign of string * term * typ               (* x = e *)               (*hasInCubicle*)
  | TmMappAss of term * term * term * typ        (* e[e -> e] *)             (*hasInCubicle*)
  | TmFun of term * string                    (* c.f *)    
  | TmIf of term * term * term              (* if e then e else e *)  (*hasInCubicle*)
  | TmIfSameVar of term * term * term
  | TmRevert                                (* revert *)             
  | TmCall of term * string * term * term list (* e1.f.value(e2)(e) *)      
  | TmCallTop of term * string * term * term * term list (* e1.f.value(e2).sender(e3)(e) *)
  | TmSeq of term * typ * term * typ                                            (*hasInCubicle*)
  | TmReturn of term                        (* return e *)

  
type params = typ * string
type func_ = typ * string * params list * term
type construtor_ =  params list * term

type func = {
  return_type: typ;
  name: string;
  params: params list;
  body: term;
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
  | TmAssign(x, e, t) -> Format.fprintf fmt "%s = %a" x pp_term e 
  | TmMappAss(e1, e2, e3, t) -> Format.fprintf fmt "%a[%a -> %a]" pp_term e1 pp_term e2 pp_term e3
  | TmMappSel(e1, e2, t) -> Format.fprintf fmt "%a[%a]" pp_term e1 pp_term e2
  | TmIf(t1, t2, t3) -> Format.fprintf fmt "if %a then %a else %a" pp_term t1 pp_term t2 pp_term t3
  | TmFun(c, f) -> Format.fprintf fmt "%a.%s" pp_term c f
  | TmReturn(e) -> Format.fprintf fmt "return %a" pp_term e 
  | TmRevert -> Format.fprintf fmt "revert"
  | TmCall(e1, f, e2, e) -> Format.fprintf fmt "%a.%s.value(%a)(%a)" pp_term e1 f pp_term e2 (pp_listparams pp_term comma) e
  | TmCallTop(e1, f, e2, e3, e) -> Format.fprintf fmt "%a.%s.value(%a).sender(%a)(%a)" pp_term e1 f pp_term e2 pp_term e3
   (pp_listparams pp_term comma) e
  | TmSeq(e1, t1, e2, t2) -> Format.fprintf fmt "%a ; %a" pp_term e1 pp_term e2
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
      | TmValue(VAddress(x)) -> Format.eprintf "(ADDRESS) @."; Format.eprintf "%a @." pp_typ TAddress ; compType TAddress (get_type gamma x) 
      | TmValue(VContract(x)) -> Format.eprintf "(REF) @.";
      let ctype = get_type gamma x in Format.eprintf "%a @." pp_typ ctype ;
      compType (TContract(getContractName(ctype))) ctype 
      | TmValue(VString(s)) -> Format.eprintf "(STRING) @."; Format.eprintf "%a @." pp_typ TString ; TString
      | TmValue(VUnit) -> Format.eprintf "(UNIT) @."; Format.eprintf "%a @." pp_typ TUnit ; TUnit  
      | TmVar(x) -> Format.eprintf "(NAT) @."; let t = get_type gamma x in Format.eprintf "%a @." pp_typ t ; t
      | TmGetParam(x) -> Format.eprintf "(NAT) @."; let t = get_type gamma x in Format.eprintf "%a @." pp_typ t ; t
      | TmRevert -> Format.eprintf "(REVERT) @."; Format.eprintf "%a @." pp_typ TUnit; TUnit
      | TmBalance(t) -> Format.eprintf "(BAL) @.";
      Format.eprintf "%a @." pp_typ TNat ; ignore(typecheck (whites + 2) gamma ct (Some TAddress) t) ; TNat
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
      | TmAssign(x, e, t) -> Format.eprintf "(ASS) @.";
      let te = typecheck (whites + 2) gamma ct None e in
      Format.eprintf "%a @." pp_typ te ;
      let tx = typecheck (whites + 2) gamma ct None (TmVar(x)) in 
      if te == tx then te else compType te tx 
      | TmValue(VMapping(l)) -> Format.eprintf "(MAPPING) @.";
      let (v1, v2) = (List.hd l) in 
      let t1 = typecheck (whites + 2) gamma ct None (TmValue(v1)) in 
        let t2 = typecheck (whites + 2) gamma ct None (TmValue(v2)) in 
      Format.eprintf "%a @." pp_typ (TMapping(t1, t2)) ; TMapping(t1, t2)
      | TmMappAss(e1, e2, e3, ty1) -> Format.eprintf "(MAPPASS) @.";
      let t1 = typecheck (whites + 2) gamma ct None e2 in 
      let t2 = typecheck (whites + 2) gamma ct None e3 in 
      Format.eprintf "%a @." pp_typ (TMapping(t1, t2)) ;
      typecheck (whites + 2) gamma ct (Some (TMapping(t1, t2))) e1 
      | TmMappSel(e1, e2, ty1) -> Format.eprintf "(MAPPSEL) @.";
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
      | TmSeq(e1, t1, e2, t2) -> Format.eprintf "(SEQ) @." ;
      ignore(typecheck (whites + 2) gamma ct None e1);
      typecheck (whites + 2) gamma ct None e2; 
    end 
  | Some ty -> for i = 0 to whites - 1 do Format.eprintf " " done ;
  Format.eprintf "%a , %a |- %a : %a@." pp_contract ct pp_gamma gamma pp_term t pp_typ ty ; 
    begin match t with 
      | TmValue(VTrue) -> Format.eprintf "(TRUE) @."; compType TBool ty 
      | TmValue(VFalse) -> Format.eprintf "(FALSE) @."; compType TBool ty           
      | TmValue(VCons(v)) -> Format.eprintf "(NAT) @."; compType TNat ty   
      | TmValue(VString(s)) -> Format.eprintf "(String) @."; compType TString ty               
      | TmValue(VAddress(x)) -> Format.eprintf "(ADDRESS) @."; ignore(compType TAddress ty); compType (get_type gamma x) TAddress 
      | TmValue(VContract(x)) -> Format.eprintf "(REF) @."; ignore(compType (get_type gamma x) ty) ; compType (TContract(getContractName(get_type gamma x))) ty
      | TmValue(VUnit) -> Format.eprintf "(UNIT) @."; compType TUnit ty 
      | TmVar(x) -> Format.eprintf "(VAR) @.";compType (get_type gamma x) ty
      | TmGetParam(x) -> Format.eprintf "(PARAM) @.";compType (get_type gamma x) ty
      | TmRevert -> Format.eprintf "(REVERT) @."; compType ty ty
      | TmBalance(t) -> Format.eprintf "(BAL) @.";ignore(typecheck (whites + 2) gamma ct (Some TAddress) t) ; compType TNat ty
      | TmPlus(e1,e2) -> Format.eprintf "(Plus) @."; ignore(typecheck (whites + 2) gamma ct (Some TNat) e1) ; typecheck (whites + 2) gamma ct (Some TNat) e2 ; compType TNat ty
      | TmMinus(e1,e2) -> Format.eprintf "(Minus) @."; ignore(typecheck (whites + 2) gamma ct (Some TNat) e1) ; typecheck (whites + 2) gamma ct (Some TNat) e2 ; compType TNat ty
      | TmMult(e1,e2) -> Format.eprintf "(Mult) @."; ignore(typecheck (whites + 2) gamma ct (Some TNat) e1) ; typecheck (whites + 2) gamma ct (Some TNat) e2 ; compType TNat ty
      | TmDiv(e1,e2) -> Format.eprintf "(Div) @."; ignore(typecheck (whites + 2) gamma ct (Some TNat) e1) ; typecheck (whites + 2) gamma ct (Some TNat) e2 ; compType TNat ty
      | TmAddress(t) -> Format.eprintf "(ADDR) @."; 
        begin match t with 
        | TmValue(VContract(c)) -> ignore(typecheck (whites + 2) gamma ct (Some (TContract(getContractName(get_type gamma c)))) t); compType TAddress ty
        | c -> invTerm (TmValue(VContract("contractName"))) c
        end
      | TmReturn(e) -> Format.eprintf "(RETURN) @."; typecheck (whites + 2) gamma ct (Some ty) e
      | TmDecl(t, x, e1, e2) -> Format.eprintf "(DECL) @."; ignore(typecheck (whites + 2) gamma ct (Some t) e1) ; typecheck (whites + 2) (binding gamma x t) ct (Some ty) e2 
      | TmIf(t1, t2, t3) -> Format.eprintf "(IF) @."; ignore(typecheck (whites + 2) gamma ct (Some TBool) t1) ; ignore(typecheck (whites + 2) gamma ct (Some ty) t2) ;
       typecheck (whites + 2) gamma ct (Some ty) t3 
      | Equals(t1, t2) -> Format.eprintf "(Equals) @."; 
        let te1 = typecheck (whites + 2) gamma ct None t1 in  (*meter ignore*)
        Format.eprintf "%a @." pp_typ te1 ;
        let te2 = typecheck (whites + 2) gamma ct None t2 in 
        if te1 == te2 then typecheck (whites + 2) gamma ct (Some TBool) (TmValue(VTrue)) else compType te1 te2
      | Greater(t1, t2) | Less(t1,t2) | LessOrEquals(t1,t2) | GreaterOrEquals(t1,t2) -> Format.eprintf "(Equals) @."; 
        let te1 = typecheck (whites + 2) gamma ct (Some TNat) t1 in  (*meter ignore*)
        let te2 = typecheck (whites + 2) gamma ct (Some TNat) t2 in 
        if te1 != TNat then compType TNat te1
        else if te2 != TNat then compType TNat te2 
        else if te1 == te2 then typecheck (whites + 2) gamma ct (Some TBool) (TmValue(VTrue)) else compType TNat te1 
      | And(t1, t2) | Or(t1,t2) -> Format.eprintf "(Bool cond) @."; 
        let te1 = typecheck (whites + 2) gamma ct (Some TBool) t1 in 
        let te2 = typecheck (whites + 2) gamma ct (Some TBool) t2 in 
        if te1 != TBool then compType TBool te1
        else if te2 != TBool then compType TBool te2 
        else if te1 == te2 then typecheck (whites + 2) gamma ct (Some TBool) (TmValue(VTrue)) else compType TBool te1     
      | Not(t1)-> Format.eprintf "(Not) @."; 
        let te1 = typecheck (whites + 2) gamma ct (Some TBool) t1 in 
        if( te1 != TBool) then compType TBool te1 else typecheck (whites + 2) gamma ct (Some TBool) (TmValue(VTrue))
      | TmAssign(x, e, t) -> Format.eprintf "(ASS) @."; ignore(typecheck (whites + 2) gamma ct (Some t) (TmVar(x))) ; typecheck (whites + 2) gamma ct (Some t) e 
      | TmValue(VMapping(l)) -> Format.eprintf "(MAPPING) @.";
        begin match ty with
        | TMapping(t1, t2) -> ignore(List.map (fun (v1, v2) -> ignore(typecheck (whites + 2) gamma ct (Some t1) (TmValue(v1))) ;
        ignore(typecheck (whites + 2) gamma ct (Some t2) (TmValue(v2)))) l ); TMapping(t1, t2)
        | t1 -> compType (TMapping(TUnit, TUnit)) ty
        end
      | TmMappAss(e1, e2, e3, ty1) -> Format.eprintf "(MAPPASS) @.";
        begin match ty1 with
        | TMapping(t1, t2) -> ignore(typecheck (whites + 2) gamma ct (Some ty1) e1) ; ignore(typecheck (whites + 2) gamma ct (Some t1) e2) ;
                                                  typecheck (whites + 2) gamma ct (Some t2) e3
        | ty1 -> compType (TMapping(TUnit, TUnit)) ty1 
        end
      | TmMappSel(e1, e2, ty1) -> Format.eprintf "(MAPPSEL) @."; let t = typecheck (whites + 2) gamma ct None e1 in
        begin match ty1 with 
        | TMapping(t1, t2) -> ignore(typecheck (whites + 2) gamma ct (Some t1) e2) ; compType t2 ty
        | ty1 -> compType (TMapping(TUnit, TUnit)) ty1 
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
      | TmSeq(e1, t1, e2, t2) -> Format.eprintf "(SEQ) @." ;
      ignore(typecheck (whites + 2) gamma ct (Some t1) e1);
      typecheck (whites + 2) gamma ct (Some t2) e2; 
    end 



let rec typecheck_command whites gamma ct typ = function
  | Eval t -> Format.open_box 2 ; ignore(typecheck (whites + 2) gamma ct typ t) ; Format.close_box ()
  | CSeq(s1, s2) as c -> match typ with
                         | Some typ -> Format.eprintf "%a , %a |- %a : %a @." pp_contract ct pp_gamma gamma pp_cmd c pp_typ typ;
                         typecheck_command (whites + 2) gamma ct None s1; typecheck_command (whites + 2) gamma ct (Some typ) s2 
                         | None -> Format.eprintf "%a , %a |- %a : None @." pp_contract ct pp_gamma gamma pp_cmd c; 
                         typecheck_command (whites + 2) gamma ct None s1; typecheck_command (whites + 2) gamma ct None s2  

let mk_eval t = Eval t
let mk_seq s1 s2 = CSeq(s1, s2)


(* -----------------TESTING----------------- *)
let test_func gamma ct t1 term = 
  try typecheck_command 0 gamma ct t1 term ; Format.eprintf "Success@."
  with TypMismatch (typ1, typ2) -> Format.eprintf "type mismatch : termected type %a but got type %a @." pp_typ typ1 pp_typ typ2 
  | InvalidTerm(t1, t2) -> Format.eprintf "term mismatch : termected %a but got %a@." pp_term t1 pp_term t2

let ttrue = TmValue(VTrue)
let tfalse = TmValue(VFalse)
let taddress = TmValue(VAddress("aEOA"))
let tcontract = TmValue(VContract("x"))
let tone = TmValue(VCons(1))
let tzero = TmValue(VCons(0))
let tmPlus = TmPlus(tone,tone)
let tmMinus = TmMinus(tone,tone)
let tmMult = TmMult(tone,tone)
let tmDiv = TmMult(tone,tone)
let tmArComplex = TmPlus(TmMult(TmMinus(TmDiv(tone,tone),tone),tzero),tzero)
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
let tassign = TmAssign("x", tone, TNat)
let tnew = TmNew("EOC", (TmValue(VCons(500))), [tone; ttrue])
let tstatesel = TmStateSel(tx,"b")
let taddress2 = TmAddress(tcontract)
let tstateass = TmStateAss(tx,"b", ttrue)
let tmap = TmValue(VMapping([(VCons(1), VTrue); (VCons(2), VFalse)]))
let tmapass =  TmMappAss(tmap, TmValue(VCons(13)), ttrue, TMapping(TNat,TBool))
let tmapsel = TmMappSel(tmap, TmValue(VCons(13)),TMapping(TNat,TBool))
let tfun = TmFun((TmValue(VContract("x"))), "f")
let tcall = TmCall(tcontract, "f", tone, [tone; ttrue])
let tcalltop = TmCallTop(tcontract, "f", tone, taddress, [tone; ttrue])
let ttransfer = TmTransfer(taddress, tone)

(*test map*)
let tmap = TmValue(VMapping([(VCons(1), VTrue); (VCons(2), VFalse)]))
let tmapass = TmMappAss(tmap, TmValue(VCons(13)), ttrue, TMapping(TNat,TBool))
let tmapsel = TmMappSel(tmap, TmValue(VCons(13)),TMapping(TNat,TBool))

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

 (* MAPPING *)
  (* test_func gammaenv ctenv (Some (TMapping(TNat, TBool))) (mk_eval tmap);
  test_func gammaenv ctenv None (mk_eval tmap); *)
  (* MAPPASS *)
  (* test_func gammaenv ctenv (Some (TMapping(TNat, TBool))) (mk_eval tmapass);
  test_func gammaenv ctenv None (mk_eval tmapass); *)
  (* MAPPSEL *)
  (* test_func gammaenv ctenv (Some TBool) (mk_eval tmapsel);
  test_func gammaenv ctenv None (mk_eval tmapsel);*)  
let ctenv = (CT.add "Bank" ([], []) (CT.add "EOC" ([(TNat, "a") ; (TBool, "b")], []) CT.empty))
let gammaenv = (Gamma.add "aEOA" TAddress (Gamma.add "x" (TContract("Bank")) Gamma.empty))
let gammaenv2 = (Gamma.add "x" (TNat) Gamma.empty)
let gammaenv3 = (Gamma.add "tmap" (TMapping(TAddress, TNat)) (Gamma.add "tmap_param"  (TMapping(TAddress, TNat)) (Gamma.add "sender"  (TAddress) Gamma.empty)))
let ctenv2 = (CT.add "Bank" ([(TNat, "a") ; (TBool, "b")], [(TNat, "f", [(TNat, "a") ; (TBool, "b")])]) CT.empty)
let ctenv3 = (CT.add "Bank" ([], [(TNat, "deposit" , [])]) (CT.add "EOC" ([(TNat, "a") ; (TBool, "b")], []) CT.empty))

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

let () = 
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

  (test_func gammaAuction ctAuction None (mk_eval 
  (TmDecl( (TContract("Owner")) , "owner", (TmNew("Owner", (TmValue(VCons(500))), [] )), 
  (TmDecl ( (TContract("Client")), "c1" , (TmNew("Client", (TmValue(VCons(500))), [(TmValue(VCons(500)))] )) , 
  (TmDecl ((TContract("Client")), "c2" , (TmNew("Client", (TmValue(VCons(500))), [(TmValue(VCons(500)))] )) , 
  (TmDecl ((TContract("Auction")), "auction", 
  (TmNew("Auction", (TmValue(VCons(0))), [(TmValue(VMapping([( (VAddress("aC1")) , VCons(0)); ((VAddress("aC1")), VCons(0))]))) ; tfalse ; tzero ; (TmVar("aAuction")); (TmVar("aAuction"))] )) , 
  (TmSeq
  ((TmCallTop((TmValue(VContract("auction")), "init", (TmValue(VCons(0))), (TmAddress(TmValue(VContract("owner")))) ,[] ))), 
  (TmCallTop( (TmValue(VContract("auction"))) , "end" , tzero , (TmAddress(TmValue(VContract("c1")))) , []))) )) ))))))))) 
  (* (mk_eval (TmCallTop((TmValue(VContract("auction")), "init", (TmValue(VCons(0))), (TmAddress(TmValue(VContract("owner")))) ,[] ))))) *)
  (* (TmCallTop( (TmValue(VContract("auction"))) , "end" , tzero , (TmAddress(TmValue(VContract("c1")))) , []))) ) *)
  
  (* (TmCallTop( (TmValue(VContract("auction"))) , "init" , tzero , (TmAddress(TmValue(VContract("owner")))), [] ))   )))) ))) )) *)

  (*------------------------------------ Bank-------------------------------------*)


(test_func gammaBank ctBank None (mk_eval
(TmDecl ((TContract("Bank")), "bank", 
(TmNew("Bank", (TmValue(VCons(0))), [(TmValue(VMapping([( (VAddress("aC1")) , VCons(0))])))] )), 
(TmSeq(
(TmCallTop((TmValue(VContract("bank")), "constuctor", (TmValue(VCons(0))), (TmAddress(TmValue(VContract("bank")))) ,[(TmValue(VMapping([( (VAddress("aC1")) , VCons(0))])))] ))),
(TmSeq((TmCallTop((TmValue(VContract("bank")), "deposit", (TmValue(VCons(5))), (TmAddress(TmValue(VContract("bank")))) ,[] ))),
(TmSeq((TmCallTop((TmValue(VContract("bank")), "getBalance", (TmValue(VCons(0))), (TmAddress(TmValue(VContract("bank")))) ,[] ))), 
(TmCallTop((TmValue(VContract("bank")), "transfer", (TmValue(VCons(5))), (TmAddress(TmValue(VContract("bank")))) ,[TmValue(VAddress("aC1")); TmValue(VCons(10))] ))) 
))))))))))






(*-----------------------------------------------------------------------------Examples-------------------------------------------------------------------------------*)
(* Bank *)
let sender : term = TmVar("sender") 
let msg_value : term = TmVar("msg_value")
let balances = TmVar("balances")

let param_balances : params = (TMapping(TAddress, TNat), "balances_param")
let param_balances_val : term = (TmGetParam("balances_param"))
let bank_constructor : construtor_ = ([param_balances],TmSeq(TmAssign("balances", param_balances_val, TMapping(TAddress, TNat)), (TUnit), TmReturn(TmValue(VUnit)), TUnit ))

let deposit : func = { return_type = TUnit; name = "deposit"; params = []; body = TmSeq( TmMappAss(balances, sender, TmPlus( TmMappSel(balances, sender, TMapping(TAddress, TNat) ) , msg_value), TMapping(TAddress, TNat) ),TUnit, TmReturn(TmValue(VUnit)), TUnit)  }

let get_balance : func = { return_type = TNat; name = "get_balance"; params = []; body = TmReturn( TmMappSel(balances, sender,TMapping(TAddress, TNat)) )  }

let param_to : params = (TAddress, "to")
let param_to_val : term = TmGetParam("to")
let param_amount :params = (TNat, "amount")
let param_amount_val : term = TmGetParam("amount")
let transfer : func = {return_type = TUnit; name = "transfer"; params = [param_to; param_amount]; body = TmSeq( TmIf( GreaterOrEquals(TmMappSel(balances, sender,TMapping(TAddress, TNat)), param_amount_val), 
                                                                      TmSeq( TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender,TMapping(TAddress, TNat)),param_amount_val),TMapping(TAddress, TNat)), TUnit,
                                                                      TmMappAss(balances, param_to_val, TmPlus( TmMappSel(balances, param_to_val,TMapping(TAddress, TNat)),param_amount_val),TMapping(TAddress, TNat)), TUnit), 
                                                                      TmReturn(TmValue(VUnit))), TUnit, TmReturn(TmValue(VUnit)), TUnit ) }

let param_withdraw_amount : params = (TNat, "W_amount") 
let param_withdraw_amount_val : term = TmGetParam("W_amount") 
let withdraw : func = {return_type = TUnit; name = "withdraw"; params = [param_withdraw_amount]; body = TmSeq( TmIf( GreaterOrEquals(TmMappSel(balances, sender,TMapping(TAddress, TNat)), param_withdraw_amount_val), 
                                                                  TmSeq(TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender,TMapping(TAddress, TNat)),param_withdraw_amount_val),TMapping(TAddress, TNat)),(TUnit), 
                                                                        TmTransfer( sender,param_withdraw_amount_val ), TUnit ), 
                                                                        TmReturn(TmValue(VUnit))),(TUnit), TmReturn(TmValue(VUnit)), TUnit) }
let ctBank = (CT.add "Bank" ( (
             [(TAddress,"Sender"); (TNat,"MsgValue");(TNat,"Balances")], 
             bank_constructor,
             [ deposit; get_balance; transfer; withdraw]) ) )
(* test bank*)
(*ver o mappsel*)
let ctBank =
  (CT.add "Bank" ([((TAddress), "sender");
                        ((TNat), "msg_value"); (TMapping(TAddress, TNat), "balances");
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
                  ]) CT.empty)
              
let gammaBank = (Gamma.add "sender" TAddress
      (Gamma.add "msg_value" TNat
      (Gamma.add "balances" (TMapping(TAddress, TNat))
      (Gamma.add "balances_param" (TMapping(TAddress, TNat))
      (Gamma.add "InstanceBuyer" TAddress
      (Gamma.add "amount" TNat
      (Gamma.add "to" TAddress
      (Gamma.add "W_amount" TNat
      (Gamma.add "param_price" TNat
      (Gamma.add "param_offer" TNat
      (Gamma.add "Bank" (TContract("Bank")) 
      (Gamma.add "aBank" TAddress Gamma.empty))))))))))))  

let constructor_body = TmSeq(TmAssign("balances", param_balances_val, TMapping(TAddress, TNat)), (TUnit), TmReturn(TmValue(VUnit)), TUnit )
test_func gammaBank ctBank (Some TUnit) (mk_eval constructor_body)

let deposit_body =  TmSeq( TmMappAss(balances, sender, TmPlus( TmMappSel(balances, sender, TMapping(TAddress, TNat) ) , msg_value), TMapping(TAddress, TNat) ),TUnit, TmReturn(TmValue(VUnit)), TUnit) 
test_func gammaBank ctBank (Some TUnit) (mk_eval deposit_body)

let getBalance_body =  TmReturn( TmMappSel(balances, sender,TMapping(TAddress, TNat)) )
test_func gammaBank ctBank (Some TNat) (mk_eval getBalance_body)

let transfer_body =  TmSeq( TmIf( GreaterOrEquals(TmMappSel(balances, sender,TMapping(TAddress, TNat)), param_amount_val), 
TmSeq( TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender,TMapping(TAddress, TNat)),param_amount_val),TMapping(TAddress, TNat)), TUnit,
TmMappAss(balances, param_to_val, TmPlus( TmMappSel(balances, param_to_val,TMapping(TAddress, TNat)),param_amount_val),TMapping(TAddress, TNat)), TUnit), 
TmReturn(TmValue(VUnit))), TUnit, TmReturn(TmValue(VUnit)), TUnit )
test_func gammaBank ctBank (Some TUnit) (mk_eval transfer_body)


let withdraw_body =  TmSeq( TmIf( GreaterOrEquals(TmMappSel(balances, sender,TMapping(TAddress, TNat)), param_withdraw_amount_val), 
TmSeq(TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender,TMapping(TAddress, TNat)),param_withdraw_amount_val),TMapping(TAddress, TNat)),(TUnit), 
      TmTransfer( sender,param_withdraw_amount_val ), TUnit ), 
      TmReturn(TmValue(VUnit))),(TUnit), TmReturn(TmValue(VUnit)), TUnit) 
      
test_func gammaBank ctBank (Some TUnit) (mk_eval withdraw_body)


(* Marketplace-azure *)

let instanceOwner : term = TmVar("InstanceOwner")
let description : term = TmVar("Description")
let askingPrice : term = TmVar("AskingPrice")
let instanceBuyer : term = TmVar("InstanceBuyer")
let offerPrice : term = TmVar("OfferPrice")
let sender : term = TmVar("sender")

let param_description : params = (TString, "param_description")
let param_description_val : term = TmGetParam("param_description")
let param_price : params = (TNat,"param_price")
let param_price_val : term = TmGetParam("param_price")
let marketplace_constructor : construtor_ = TmSeq(TmSeq( TmAssign("InstanceOwner",sender, TAddress), TUnit, TmSeq(TmAssign("AskingPrice", param_price_val, TNat),TUnit, TmAssign("Description", param_description_val, TString), TUnit ), TUnit), TUnit, TmReturn(TmValue(VUnit)),TUnit ) 

let param_offer : params = (TNat, "param_offer")
let param_offer_val : term = TmGetParam("param_offer")
let make_offer : func = {return_type = TUnit; name = "make_offer"; params = [param_offer]; 
                      body = TmReturnUnit( TmSeq( TmIf(Equals(param_offer_val, TmValue(VCons(0))), TmRevert, TmReturn(TmValue(VUnit))),TmSeq( TmIf(Equals(sender, instanceOwner), TmRevert, TmReturn(TmValue(VUnit))),
                      TmSeq( TmAssign("InstanceBuyer", sender), TmAssign("OfferPrice", param_offer_val) ) )))}
                

let param_offer_r : params = (TNat, "param_offer_r")
let param_offer_r_val : term = TmGetParam("param_offer")                      
let reject : func = {return_type = TUnit; name = "reject"; params = [param_offer_r]; body = TmReturnUnit(TmSeq( TmIf(Not(Equals(param_offer_r_val, TmValue(VCons(0)))), 
                                                              TmRevert, 
                                                              TmReturn(TmValue(VUnit))), 
                                                       TmAssign("InstanceBuyer", TmValue(VAddress("0x000000000"))) ) ) }


let param_offer_a : params = (TNat, "param_offer_a")
let param_offer_a_val : term = TmGetParam("param_offer")    
let accept : func = {return_type = TUnit; name = "accept"; params = [param_offer_a]; body = TmReturn(TmIf(Not(Equals(param_offer_a_val, TmValue(VCons(0)))), 
                                                        TmRevert, 
                                                        TmReturn(TmValue(VUnit))))}
                                                    
 
(*test marketplace*)
let constructor_body =  TmSeq(TmSeq( TmAssign("InstanceOwner",sender, TAddress), TUnit, TmSeq(TmAssign("AskingPrice", param_price_val, TNat),TUnit, TmAssign("Description", param_description_val, TString), TUnit ), TUnit), TUnit, TmReturn(TmValue(VUnit)),TUnit ) 
test_func gammaMark ctMark (Some TUnit) (mk_eval constructor_body);;

let make_offer_body = TmReturnUnit( TmSeq( TmIf(Equals(param_offer_val, TmValue(VCons(0))), TmRevert, TmReturn(TmValue(VUnit))),TmSeq( TmIf(Equals(sender, instanceOwner), TmRevert, TmReturn(TmValue(VUnit))), TmSeq( TmAssign("InstanceBuyer", sender), TmAssign("OfferPrice", param_offer_val) ) )))
test_func gammaMark ctMark (Some TUnit) (mk_eval make_offer_body);;

let accept_offer_body = TmReturnUnit(TmIf(Not(Equals(param_offer_a_val, TmValue(VCons(0)))), 
TmRevert, 
TmReturn(TmValue(VUnit))))
test_func gammaMark ctMark (Some TUnit) (mk_eval accept_offer_body);;

let reject_offer_body =  TmReturnUnit(TmSeq( TmIf(Not(Equals(param_offer_r_val, TmValue(VCons(0)))), TmRevert, TmReturn(TmValue(VUnit))), TmAssign("InstanceBuyer", TmValue(VAddress("sender"))) ) ) 
test_func gammaMark ctMark (Some TUnit) (mk_eval reject_offer_body);;

let ctMark =
    (CT.add "Marketplace" ([((TAddress), "InstanceOwner");((TString), "Description");
                          ((TAddress), "AskingPrice"); ((TAddress), "InstanceBuyer");
                          ((TNat), "OfferPrice"); ((TAddress), "sender");
                          ((TString), "param_description");((TNat), "param_price");
                          ((TNat), "param_offer")],
                    [(TUnit, "marketplace_constructor",[((TString), "param_description"); ((TAddress), "OfferPrice")]); 
                    (TUnit, "make_offer",[(TNat), "param_offer"]);
                    (TNat, "accept", []);
                    (TUnit, "reject", []);
                    ]) CT.empty)
                
let gammaMark = (Gamma.add "InstanceOwner" TAddress
        (Gamma.add "Description" TString
        (Gamma.add "AskingPrice" TNat
        (Gamma.add "InstanceBuyer" TAddress
        (Gamma.add "OfferPrice" TNat
        (Gamma.add "sender" TAddress
        (Gamma.add "param_description" TString
        (Gamma.add "param_price" TNat
        (Gamma.add "param_offer" TNat
        (Gamma.add "Mark" (TContract("Mark")) 
        (Gamma.add "aMark" TAddress Gamma.empty)))))))))))                         
                                                         
(* Telemetry-azure *)
let sender : term = TmVar("Sender")
let owner : term = TmVar("Owner")
let counterParty : term = TmVar("CounterParty")
let device : term = TmVar("Device")
let complianceStatus : term = TmVar("ComplianceStatus")
let max_temp : term = TmVar("Max_Temperature")
let min_temp : term = TmVar("Min_Temperature")

let param_device : params = (TAddress,"param_device")
let param_device_val : term = TmGetParam("param_device")
let param_max_temp : params = (TAddress,"param_max_temp")
let param_max_temp_val : term = TmGetParam("param_max_temp")
let param_min_temp : params = (TAddress,"param_min_temp")
let param_min_temp_val : term = TmGetParam("param_min_temp")
let telemetry_constructor = ([param_device;param_max_temp; param_min_temp],
                            TmReturn(TmSeq( TmAssign("ComplianceStatus",TmValue(VTrue)) , TmSeq( TmAssign("CounterParty", sender), 
                            TmSeq(TmAssign("Owner", sender) , TmSeq(TmAssign(" Device", param_device_val) , 
                            TmSeq(TmAssign("Max_Temperature", param_max_temp_val ) , TmAssign("Min_Temperature", param_min_temp_val )))) ) ) ) )  
 
let param_temp : params = (TNat, "param_temp")     
let param_temp_val : term = TmGetParam("param_temp")                           
let ingest_telemetry : func = {return_type = TUnit; name = "ingest_telemetry"; params = [param_temp]; body = TmReturn( TmSeq(TmIf( Not(Equals(sender, device)), TmRevert, TmReturn(TmValue(VUnit))), 
                              TmSeq(TmIf( Or( Greater(param_temp_val, max_temp), Less(param_temp_val, min_temp)),TmAssign("ComplianceStatus",TmValue(VFalse)),TmReturn(TmValue(VUnit))) ,TmReturn(TmValue(VUnit))))) }

let param_new_counter_party : params = (TAddress, "param_new_counter_party")   
let param_new_counter_party_val : term = TmGetParam("param_new_counter_party")                         
let transfer_responsability : func = {return_type = TUnit; name = "transfer_responsability"; params = [param_new_counter_party]; 
                              body = TmReturn( TmSeq( TmIf( And(Not(Equals(sender,param_new_counter_party_val )),Not(Equals(sender,counterParty))), TmRevert ,TmReturn(TmValue(VUnit))),
                                     TmSeq(TmIf(Equals(param_new_counter_party_val,device), TmRevert, TmReturn(TmValue(VUnit))),TmAssign("counterParty", param_new_counter_party_val) ) ) ) }

let complete : func = { return_type = TUnit; name = "complete"; params = []; body = TmReturn( TmSeq( TmIf( Not(Equals(sender,owner )), TmRevert ,TmReturn(TmValue(VUnit))), 
                      TmAssign("CounterParty", TmValue(VString("0x000000000")))  ) ) } 
                      
          
let ctTelemetry =  (CT.add "Telemetry" ( (
  [(TAddress,"Sender"); (TNat,"MsgValue");(TAddress,"Owner");(TAddress,"InitialCounterParty"); (TAddress,"CounterParty"); (TAddress,"PreviousParty"); (TAddress,"Device");
  (TAddress,"SupplyChainObserver");(TAddress,"SupplyChainOwner");(TNat,"Max_Temperature");(TNat,"Min_Temperature");], 
  telemetry_constructor,
  [ ingest_telemetry; transfer_responsability; complete]) ) );    
  
(* test telemetry *)