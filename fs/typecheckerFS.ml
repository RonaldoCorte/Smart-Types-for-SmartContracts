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

type params = typ * string
type func = typ * string * params list
type contract = params list * func list

exception TypMismatch of typ * typ
let compType expected received = 
  if not (received = expected) then raise (TypMismatch (expected, received)) else received

type values =
  | VTrue                   (* true *)
  | VFalse                  (* false *)
  | VCons of int            (* n *)
  | VAddress of string      (* address *)
  | VContract of string     (* contract c *)
  | VUnit                   (* u *)
  | VMapping of (values * values) list 

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
  | TmAssign of string * term               (* x = e ; e *)
  | TmMappAss of term * term * term         (* e[e -> e] *)
  | TmMappSel of term * term                (* e[e] *)
  | TmFun of term * string                    (* c.f *)
  | TmIf of term * term * term              (* if e then e else e *)
  | TmReturn of term                        (* return e *)
  | TmRevert                                (* revert *)
  | TmCall of term * string * term * term list (* e1.f.value(e2)(e) *)     
  | TmCallTop of term * string * term * term * term list (* e1.f.value(e2).sender(e3)(e) *)
  | TmSeq of term * term 
  
exception InvalidTerm of term * term
let invTerm expected received =
  raise (InvalidTerm (expected, received))  
  
type command = 
  | Eval of term
  | CSeq of command * command

let comma fmt () = Format.fprintf fmt ", "

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
      | TmValue(VUnit) -> Format.eprintf "(UNIT) @."; Format.eprintf "%a @." pp_typ TUnit ; TUnit  
      | TmVar(x) -> Format.eprintf "(NAT) @."; let t = get_type gamma x in Format.eprintf "%a @." pp_typ t ; t
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
      | TmAssign(x, e) -> Format.eprintf "(ASS) @.";
      let te = typecheck (whites + 2) gamma ct None e in
      Format.eprintf "%a @." pp_typ te ;
      let tx = typecheck (whites + 2) gamma ct None (TmVar(x)) in 
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
      | TmValue(VAddress(x)) -> Format.eprintf "(ADDRESS) @."; ignore(compType TAddress ty); compType (get_type gamma x) TAddress 
      | TmValue(VContract(x)) -> Format.eprintf "(REF) @."; ignore(compType (get_type gamma x) ty) ; compType (TContract(getContractName(get_type gamma x))) ty
      | TmValue(VUnit) -> Format.eprintf "(UNIT) @."; compType TUnit ty 
      | TmVar(x) -> Format.eprintf "(VAR) @.";compType (get_type gamma x) ty
      | TmRevert -> Format.eprintf "(REVERT) @."; compType ty ty
      | TmBalance(t) -> Format.eprintf "(BAL) @.";ignore(typecheck (whites + 2) gamma ct (Some TAddress) t) ; compType TNat ty
      | TmAddress(t) -> Format.eprintf "(ADDR) @."; 
        begin match t with 
        | TmValue(VContract(c)) -> ignore(typecheck (whites + 2) gamma ct (Some (TContract(getContractName(get_type gamma c)))) t); compType TAddress ty
        | c -> invTerm (TmValue(VContract("contractName"))) c
        end
      | TmReturn(e) -> Format.eprintf "(RETURN) @."; typecheck (whites + 2) gamma ct (Some ty) e
      | TmDecl(t, x, e1, e2) -> Format.eprintf "(DECL) @."; ignore(typecheck (whites + 2) gamma ct (Some t) e1) ; typecheck (whites + 2) (binding gamma x t) ct (Some ty) e2 
      | TmIf(t1, t2, t3) -> Format.eprintf "(IF) @."; ignore(typecheck (whites + 2) gamma ct (Some TBool) t1) ; ignore(typecheck (whites + 2) gamma ct (Some ty) t2) ;
       typecheck (whites + 2) gamma ct (Some ty) t3 
      | TmAssign(x, e) -> Format.eprintf "(ASS) @."; ignore(typecheck (whites + 2) gamma ct (Some ty) (TmVar(x))) ; typecheck (whites + 2) gamma ct (Some ty) e 
      | TmValue(VMapping(l)) -> Format.eprintf "(MAPPING) @.";
        begin match ty with
        | TMapping(t1, t2) -> ignore(List.map (fun (v1, v2) -> ignore(typecheck (whites + 2) gamma ct (Some t1) (TmValue(v1))) ;
        ignore(typecheck (whites + 2) gamma ct (Some t2) (TmValue(v2)))) l ); TMapping(t1, t2)
        | t1 -> compType (TMapping(TUnit, TUnit)) ty
        end
      | TmMappAss(e1, e2, e3) -> Format.eprintf "(MAPPASS) @.";
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
      | TmSeq(e1, e2) -> Format.eprintf "(SEQ) @." ;
      ignore(typecheck (whites + 2) gamma ct None e1);
      typecheck (whites + 2) gamma ct (Some ty) e2; 
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

let ttrue = TmValue(VTrue)
let tfalse = TmValue(VFalse)
let taddress = TmValue(VAddress("aEOA"))
let tcontract = TmValue(VContract("x"))
let tone = TmValue(VCons(1))
let tzero = TmValue(VCons(0))
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
let tmapass = TmMappAss(tmap, TmValue(VCons(13)), ttrue)
let tmapsel = TmMappSel(tmap, tone)
let tfun = TmFun((TmValue(VContract("x"))), "f")
let tcall = TmCall(tcontract, "f", tone, [tone; ttrue])
let tcalltop = TmCallTop(tcontract, "f", tone, taddress, [tone; ttrue])
let ttransfer = TmTransfer(taddress, tone)


let ctenv = (CT.add "Bank" ([], []) (CT.add "EOC" ([(TNat, "a") ; (TBool, "b")], []) CT.empty))
let gammaenv = (Gamma.add "aEOA" TAddress (Gamma.add "x" (TContract("Bank")) Gamma.empty))
let gammaenv2 = (Gamma.add "x" (TContract("Bank")) Gamma.empty)
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

let test_func gamma ct t1 exp = 
  try typecheck_command 0 gamma ct t1 exp ; Format.eprintf "Success@."
  with TypMismatch (typ1, typ2) -> Format.eprintf "type mismatch : expected type %a but got type %a @." pp_typ typ1 pp_typ typ2 
  | InvalidTerm(t1, t2) -> Format.eprintf "term mismatch : expected %a but got %a@." pp_term t1 pp_term t2


let () = 
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


let ctBank =
  (CT.add "Bank" ([((TMapping(TAddress, TNat)), "balances")],
                  [(TUnit, "constuctor",[((TMapping(TAddress, TNat)),"balances")]); 
                  (TUnit, "deposit",[]);
                  (TNat, "getBalance", []);
                  (TUnit, "transfer", [(TAddress,"to");(TNat,"amount")]);
                  (TUnit, "withdraw", [(TNat,"amount")])
                  ]) CT.empty);;
                  
let gammaBank = (Gamma.add "aC1" TAddress
          (Gamma.add "Bank" (TContract("Bank")) 
          (Gamma.add "aBank" TAddress Gamma.empty)));;

(test_func gammaBank ctBank None (mk_eval
(TmDecl ((TContract("Bank")), "bank", 
(TmNew("Bank", (TmValue(VCons(500))), [(TmValue(VMapping([( (VAddress("aC1")) , VCons(550))])))] )), 
(TmSeq(
(TmCallTop((TmValue(VContract("bank")), "constuctor", (TmValue(VCons(500))), (TmAddress(TmValue(VContract("bank")))) ,[(TmValue(VMapping([( (VAddress("aC1")) , VCons(500))])))] ))),
(TmSeq((TmCallTop((TmValue(VContract("bank")), "deposit", (TmValue(VCons(100))), (TmAddress(TmValue(VContract("bank")))) ,[] ))),
(TmSeq((TmCallTop((TmValue(VContract("bank")), "getBalance", (TmValue(VCons(0))), (TmAddress(TmValue(VContract("bank")))) ,[] ))), 
(TmCallTop((TmValue(VContract("bank")), "transfer", (TmValue(VCons(100))), (TmAddress(TmValue(VContract("bank")))) ,[TmValue(VAddress("aC1")); TmValue(VCons(100))] ))) 
))))))))))