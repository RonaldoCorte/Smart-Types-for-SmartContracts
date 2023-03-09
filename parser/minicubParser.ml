(*
   ocamlopt -c types.ml
   ocamlopt -c minicubParser.ml
   ocamlopt -o parser types.cmx minicubParser.cmx
*)
open Types
module Gamma = Map.Make (String)

let get_type gamma x =
  Gamma.find x gamma;;

let binding gamma x t =
  Gamma.add x t gamma;;

let hasVar cases var = 
  let cl = List.map (fun (x,_) -> x) !cases in
  List.exists (fun(x) -> x = var) cl;;

let rec find x lst = 
  match lst with
  | [] -> raise (Failure "Not found")
  | h::t -> let (c,_) = h in  
            if x = c then 0 else 1 + find x t;;

let replace l pos a = List.mapi (fun i x -> if i = pos then a else x) l ;;

let update_var cases t cond var =
  let i = find var !cases in
  let (elem_var, elem_lst) = List.find (fun (v,_) -> v = var) !cases in 
  let new_elem = (elem_var, elem_lst @ [(cond,t)]) in
  cases := replace !cases i new_elem ;;     
                        

let rec find_cases gamma cond t cases =  (* case = [ (var,[(cond,e1);(!cond,e2);(cond,e3)]) ]*)
  begin match t with
  | TmAssign(x, e) -> if ((hasVar (cases) (x) ) = false) then cases := !cases @ [(x,[(cond,t)])] else ignore(update_var cases t cond x);
                      Printf.printf "(assign) \n";
  | TmMappAss(e1, e2, e3) -> begin match e1 with
                            | TmVar(var) -> if ((hasVar (cases) (var) ) = false) then cases := !cases @ [(var,[(And(cond, Equals(TmVar("c"),e2)),t)])] else ignore(update_var cases t (And(cond, Equals(TmVar("c"),e2))) var);          
                                            Printf.printf "(map assign) \n";
                            | _ ->  Printf.printf "non implemented \n"; 
                            end;
  | TmRevert -> let x = "Revert" in
                if ((hasVar (cases) (x) ) = false) then (cases := !cases @ [(x,[(cond,t)])]) else (ignore(update_var cases t cond x));
                Printf.printf "(revert) \n";
  | TmSeq(e1, e2) -> ignore(find_cases gamma cond e1 cases); ignore(find_cases gamma cond e2 cases); Printf.printf "(seq) \n";
  | _ -> Printf.printf "non implemented :| \n";
end;;


let rec deal_with_cases l= 
  match l with
  | [] -> raise(Failure "Error");
  | h::t -> let(var,lst) = h in
            let c = C_Case(var,lst) in
            if(t != []) then  C_Seq(c,deal_with_cases t) else c;;
            

let rec parse_type t  = 
  begin match t with
  | TBool -> Bool
  | TNat -> Int
  | TUnit -> Unit
  | TAddress -> Proc
  | TMapping(a,b) -> CArr(parse_type a ,parse_type b )
  | TString -> String
  | TState -> State
  | _ -> Proc
end
;;

let rec parse_term t gamma cases cubvars extra_exps func_name= 
  begin match t with
  | TmValue(VTrue) -> C_Value(CBool(true))
  | TmValue(VFalse) -> C_Value(CBool(false))
  | TmValue(VCons(v)) -> C_Value(CCons(v)) 
  | TmValue(VAddress(x)) -> C_Value(CProc(x)) 
  | TmValue(VString(s)) -> C_Value(CString(s)) 
  | TmValue(VUnit) -> C_Value(CUnit) 
  | TmValue(VState(a)) -> C_Value(CState(a)) 
  | TmVar(x) -> C_GetVar(x)
  | TmGetParam(x) ->let ty = get_type gamma x in
    begin match ty with
    | TBool | TNat | TString ->  C_GetI(C_Get_Param("Random"^"_"^x),C_Get_Param("sender"))
    | TMapping(a,b) -> C_GetI(C_Get_Param("Random"^"_"^x),C_Get_Param("sender"))
    | TUnit -> C_Get_Param("non implemented")
    | TAddress -> C_Get_Param(x)
    | TContract(s) -> C_Get_Param("non implemented") 
    | TFun(a,b) ->  C_Get_Param("non implemented") 
    | TState -> C_Get_Param("non implemented")  
    end; 
  | TmGetState(x) -> C_GetState(x) 
  | And(t1, t2) -> C_And(parse_term t1 gamma cases cubvars extra_exps func_name, parse_term t2 gamma cases cubvars extra_exps func_name)
  | Or(t1,t2) -> C_Or(parse_term t1 gamma cases cubvars extra_exps func_name,parse_term t2 gamma cases cubvars extra_exps func_name)
  | Not(t1)-> C_Not(parse_term t1 gamma cases cubvars extra_exps func_name)
  | TmAddress(t) ->C_Address(parse_term t gamma cases cubvars extra_exps func_name)
  | TmAssign(x, e) -> C_Assign(x,parse_term e gamma cases cubvars extra_exps func_name)
  | Equals(x, e) -> C_Equals(parse_term x gamma cases cubvars extra_exps func_name, parse_term e gamma cases cubvars extra_exps func_name )
  | Greater(x, e) -> C_Greater(parse_term x gamma cases cubvars extra_exps func_name, parse_term e gamma cases cubvars extra_exps func_name ) 
  | Less(x, e) -> C_Less(parse_term x gamma cases cubvars extra_exps func_name, parse_term e gamma cases cubvars extra_exps func_name )
  | GreaterOrEquals(x, e) -> C_GreaterOrEquals(parse_term x gamma cases cubvars extra_exps func_name, parse_term e gamma cases cubvars extra_exps func_name) 
  | LessOrEquals(x, e) -> C_LessOrEquals(parse_term x gamma cases cubvars extra_exps func_name, parse_term e gamma cases cubvars extra_exps func_name )
  | TmPlus(x, y) -> let exp_x = parse_term x gamma cases cubvars extra_exps func_name in
                    let exp_y = parse_term y gamma cases cubvars extra_exps func_name in
                     begin match (exp_x,exp_y) with
                    | (C_GetI(a,b),C_GetI(c,d) ) -> begin match a with
                                                    | C_GetVar(x) -> cubvars := !cubvars @ [(C_GetVar(x^"ArrayArithmeticOperation"^ string_of_int(List.length !extra_exps)^"_"^func_name), Int)]; 
                                                                    extra_exps := !extra_exps @ [C_Assign(x^"ArrayArithmeticOperation"^ string_of_int((List.length !extra_exps))^"_"^func_name, exp_y )];
                                                                    C_Plus(exp_x, C_GetVar(x^"ArrayArithmeticOperation"^ string_of_int((List.length !extra_exps) -1)^"_"^func_name));
                                                    | _ -> C_Plus(exp_x, exp_y);
                                                    end;
                    | _ -> C_Plus(exp_x, exp_y);
                    end;
  | TmMinus(x,y) -> let exp_x = parse_term x gamma cases cubvars extra_exps func_name in
                    let exp_y = parse_term y gamma cases cubvars extra_exps func_name in
                    begin match (exp_x,exp_y) with
                    | (C_GetI(a,b),C_GetI(c,d) ) -> begin match a with
                                                    | C_GetVar(x) -> cubvars := !cubvars @ [(C_GetVar(x^"ArrayArithmeticOperation"^ string_of_int(List.length !extra_exps)^"_"^func_name), Int)]; 
                                                                    extra_exps := !extra_exps @ [C_Assign(x^"ArrayArithmeticOperation"^ string_of_int(List.length !extra_exps)^"_"^func_name, exp_y )];
                                                                    C_Minus(exp_x, C_GetVar(x^"ArrayArithmeticOperation"^ string_of_int((List.length !extra_exps) -1)^"_"^func_name));
                                                    | _ -> C_Minus(exp_x, exp_y);
                                                    end;
                    | _ -> C_Minus(exp_x, exp_y);
                    end;
                    
  | TmMult(x,y) ->let exp_x = parse_term x gamma cases cubvars extra_exps func_name in
                  let exp_y = parse_term y gamma cases cubvars extra_exps func_name in
                  begin match (exp_x,exp_y) with
                  | (C_GetI(a,b),C_GetI(c,d) ) -> begin match a with
                                                  | C_GetVar(x) -> cubvars := !cubvars @ [(C_GetVar(x^"ArrayArithmeticOperation"^ string_of_int(List.length !extra_exps)^"_"^func_name), Int)]; 
                                                                  extra_exps := !extra_exps @ [C_Assign(x^"ArrayArithmeticOperation"^ string_of_int(List.length !extra_exps)^"_"^func_name, exp_y )];
                                                                  C_Mult(exp_x, C_GetVar(x^"ArrayArithmeticOperation"^ string_of_int((List.length !extra_exps) -1)^"_"^func_name));
                                                  | _ -> C_Mult(exp_x, exp_y);
                                                  end;
                  | _ -> C_Mult(exp_x, exp_y)
                  end;
  | TmDiv(x,y)->  let exp_x = parse_term x gamma cases cubvars extra_exps func_name in
                  let exp_y = parse_term y gamma cases cubvars extra_exps func_name in
                  begin match (exp_x,exp_y) with
                  | (C_GetI(a,b),C_GetI(c,d) ) -> begin match a with
                                                  | C_GetVar(x) -> cubvars := !cubvars @ [(C_GetVar(x^"ArrayArithmeticOperation"^ string_of_int(List.length !extra_exps)^"_"^func_name), Int)]; 
                                                                  extra_exps := !extra_exps @ [C_Assign(x^"ArrayArithmeticOperation"^ string_of_int(List.length !extra_exps)^"_"^func_name, exp_y )];
                                                                  C_Div(exp_x, C_GetVar(x^"ArrayArithmeticOperation"^ string_of_int((List.length !extra_exps) -1)^"_"^func_name));
                                                  | _ -> C_Div(exp_x, exp_y);
                                                  end;
                  | _ -> C_Div(exp_x, exp_y);
                  end;
  | TmSeq(e1, e2) ->  C_Seq(parse_term e1 gamma cases cubvars extra_exps func_name, parse_term e2 gamma cases cubvars extra_exps func_name)
  | TmBalance(t) ->  C_GetI(C_Get_Param("GlobalBalances"),C_Get_Param("sender")) 
  | TmMappAss(e1, e2, e3) -> C_AssignArr(parse_term e1 gamma cases cubvars extra_exps func_name, parse_term e2 gamma cases cubvars extra_exps func_name, parse_term e3 gamma cases cubvars extra_exps func_name)
  | TmMappSel(e1, e2) -> C_GetI(parse_term e1 gamma cases cubvars extra_exps func_name, parse_term e2 gamma cases cubvars extra_exps func_name) 
  | TmReturn(e) -> begin match e with
                   | TmValue(VUnit) -> parse_term e gamma cases cubvars extra_exps func_name
                   | _ -> C_Assign("Return_"^func_name,parse_term e gamma cases cubvars extra_exps func_name)
                end;
  | TmIf(t1, t2, t3) -> find_cases gamma t1 t2 cases;   (*ver o caso de duas definicoes do mesmo array na mesma funcao*)
                        find_cases gamma (Not(t1)) t3 cases;
                        C_Value(CUnit);
  | TmRevert ->  C_Assign("Revert",C_Value(CBool(true)))
  | TmValue(VMapping(l)) -> C_Value(CProc("non implemented"))   
  | TmValue(VContract(x)) -> C_Value(CProc("non implemented")) 
  | TmStateSel(e, s) -> C_Value(CProc("non implemented")) 
  | TmStateAss(e1, s, e2) -> C_Value(CProc("non implemented")) 
  | TmNew(c, e1, e2) -> C_Value(CProc("non implemented")) 
  | TmFun(c, f) -> C_Value(CProc("non implemented")) 
  | TmTransfer(e1, e2) -> C_Value(CProc("non implemented")) 
  | TmCall(e1, f, e2, e) ->C_Value(CProc("non implemented")) 
  | TmCallTop(e1, f, e2, e3, e) ->C_Value(CProc("non implemented")) (*no caso de uma chamada de uma funcao retornar um valor da funcao ou ver se tem uma var com esse nome*)
  | TmDecl(t, x, e1, e2) -> C_Value(CProc("non implemented")) 
end
;;

let rec parse_params params funcname cubvars cubparams gamma = match params with
| [] -> Printf.printf "All %s params are parsed! \n" funcname; (*!cubparams;*)
| head::body -> let param_type,param_name = head in
                begin match param_type with
                | TBool ->  ignore(binding (gamma) ("Random"^"_"^param_name) (TMapping(TAddress, TBool))); ignore(cubvars := !cubvars @ [(C_GetVar("Random"^"_"^param_name),parse_type (TMapping(TAddress, TBool)))]); Printf.printf("param bool parsed \n");
                | TNat ->  ignore(binding (gamma) ("Random"^"_"^param_name) (TMapping(TAddress, TNat))); ignore(cubvars := !cubvars @ [(C_GetVar("Random"^"_"^param_name),parse_type (TMapping(TAddress, TNat)))]); Printf.printf("param nat parsed \n");
                | TUnit -> Printf.printf("invalid param unit \n");
                | TAddress -> ignore(cubparams := !cubparams @ [C_Get_Param(param_name)]); Printf.printf("param address parsed \n");
                | TMapping(a, b) ->  ignore(binding (gamma) ("Random"^"_"^param_name) (TMapping(a, b))); ignore(cubvars := !cubvars @ [(C_GetVar("Random"^"_"^param_name), parse_type param_type)]); Printf.printf("param tmapping parsed \n");
                | TString -> ignore(binding (gamma) ("Random"^"_"^param_name) (TMapping(TAddress, TString))); ignore(cubvars := !cubvars @ [(C_GetVar("Random"^"_"^param_name),parse_type  (TMapping(TAddress, TString)))]); Printf.printf("param string parsed \n");
                | TContract(s) ->  Printf.printf("invalid param contract \n");
                | TFun(a,b) ->  Printf.printf("invalid param fun \n");
                | TState -> Printf.printf("invalid param tsate \n");
                end;
                parse_params body funcname cubvars cubparams gamma;;


let parse_requires requires cub_requires gamma cubvars= 
  Printf.printf "Parsing requires .... \n";
  cub_requires := parse_term requires gamma (ref[]) cubvars (ref[]) "requires";
  Printf.printf "Requires parsed with success :) \n";;


let rec deal_with_extra_exps lst = 
  begin match lst with
  | [] -> C_Value(CUnit);
  | h::v -> C_Seq(h,deal_with_extra_exps v) 
  end;;

let parse_fun params funcname cubvars cubparams gamma requires cub_requires return_type body body_cub_func =
  cubparams := !cubparams @ [C_Get_Param("sender")];
  parse_params params funcname cubvars cubparams gamma;
  parse_requires requires cub_requires gamma cubvars;
  begin match return_type with
  | TUnit -> cubvars := !cubvars;
  | _ -> cubvars := !cubvars @ [(C_GetVar("Return_" ^ funcname),parse_type return_type)];
  end;
  Printf.printf "Parsing func body .... \n";
  let cases= ref[] in
  let extra_exps = ref [] in
  body_cub_func := parse_term body gamma cases cubvars extra_exps funcname;

  if((List.length !cases) > 0) then(
    let l = List.map (fun(x,y) -> (x, List.map( fun(c,f) -> (parse_term (c) (gamma) (cases) (cubvars) extra_exps funcname),parse_term (f) (gamma) (cases) (cubvars) extra_exps funcname) y) ) !cases in
    body_cub_func := C_Seq(!body_cub_func,deal_with_cases l) ;
  );

  if((List.length !extra_exps) > 0) then (
    body_cub_func := C_Seq( (deal_with_extra_exps !extra_exps) ,!body_cub_func);
  );
  Printf.printf"Func %s parsed \n" funcname;;

let rec parse_vars fsvars cubvars gamma = match fsvars with
| [] -> Printf.printf "All vars are parsed! \n"; !cubvars;
| head::body -> let (fs_var,fs_typ) = head in
                let current_var = (parse_term fs_var gamma (ref[]) cubvars (ref[]) "", parse_type fs_typ) in
                cubvars := !cubvars @ [current_var];
                parse_vars body cubvars gamma;;

let rec process_fun funcs gamma cubvars cubfuncs = 
  match funcs with
  | [] -> Printf.printf "----------------------------------------------------All funcs are parsed...----------------------------------------------------------- \n";
  | h::t -> let cub_requires = ref (C_Value(CBool(true))) in
            let cubparams = ref[] in
            let body_cub_func =  ref (C_Value(CBool(true))) in (*default value*)
            parse_fun h.params h.func_name cubvars cubparams gamma h.requires cub_requires h.return_type h.body body_cub_func;
           (*let cubfunc = (h.name, !cubparams, !cub_requires, !body_cub_func) in *)
            let cubfunc : cubfunc_ = {
              requires_ = !cub_requires;
              name_ = h.func_name;
              params_ = !cubparams;
              body_ = !body_cub_func
            } in
            cubfuncs := !cubfuncs @ [cubfunc];
            process_fun t gamma cubvars cubfuncs;;

let parse_unsafe_or_init_params params funcname cubvars cubparams gamma  = 
  parse_params params funcname cubvars cubparams gamma;;

let parse_contract contract_name fsvars gamma funcs bt unsafe_fs init_fs = 
  let cubvars = ref [] in 
  let cubfuncs = ref[] in
  let new_unsafe_params = ref[] in
  let new_init_params = ref[] in
  let (unsafe_params, unsafe_cond) = unsafe_fs in
  let (init_params, init_cond) = init_fs in
  parse_unsafe_or_init_params unsafe_params "unsafe" cubvars new_unsafe_params gamma;
  parse_unsafe_or_init_params init_params "init" cubvars new_init_params gamma;
  Printf.printf "----fsvars------------------------------------------------Parsing vars...----------------------------------------------------------- \n";
  ignore(parse_vars fsvars cubvars gamma);
  cubvars := !cubvars @ [(C_GetVar("GlobalBalances"),CArr(Proc,Int) )];
  Printf.printf "----------------------------------------------------Parsing funcs...----------------------------------------------------------- \n";
  process_fun funcs gamma cubvars cubfuncs;
  let cub_bt = ref[] in 
  List.iter (fun(x) -> (cub_bt := !cub_bt @ [parse_term x gamma (ref[]) cubvars (ref[]) ""])) bt;
  let new_contract : contract_cub = {
    name = contract_name;
    init = ((!new_init_params),(parse_term (init_cond) (gamma) (ref[]) cubvars (ref[]) ""));
    unsafe = (!new_unsafe_params,((parse_term (Not(unsafe_cond)) (gamma) (ref[]) cubvars (ref[]) "")));
    behavioral_types = !cub_bt;
    vars = !cubvars;
    funcs = !cubfuncs;
  } in
  new_contract;;

(*let x = Equals(GreaterOrEquals(TmValue(VCons(0)),Not(TmValue(VFalse))),TmValue(VTrue))
let c = parse_term x *)

(*--------------------------------------------------marketplace-------------------------------------------------------*)
let instanceOwner : term = TmVar("InstanceOwner")
let description : term = TmVar("Description")
let askingPrice : term = TmVar("AskingPrice")
let instanceBuyer : term = TmVar("InstanceBuyer")
let offerPrice : term = TmVar("OfferPrice")
let sender : term = TmGetParam("sender")

let param_description : params = (TString, "param_description")
let param_description_val : term = TmGetParam("param_description")
let param_price : params = (TNat,"param_price")
let param_price_val : term = TmGetParam("param_price")
let marketplace_constructor : construtor_ = ([param_description;param_price], TmSeq(TmSeq(TmAssign("CurrentState", TmGetState("ItemAvailable")) , TmSeq(TmAssign("InstanceOwner",sender), TmSeq(TmAssign("AskingPrice", param_price_val), TmAssign("Description", param_description_val)))), TmReturn(TmValue(VUnit)) ) )

let param_offer : params = (TNat, "param_offer")
let param_offer_val : term = TmGetParam("param_offer")
let make_offer : func = {requires = And(Equals(TmGetState("ItemAvailable"), TmVar("CurrentState")), Greater(TmGetParam("param_offer"), TmVar("AskingPrice"))); return_type = TUnit; func_name = "make_offer"; params = [param_offer]; 
                      body = TmSeq( TmSeq( TmIf(Equals(param_offer_val, TmValue(VCons(0))), TmRevert, TmReturn(TmValue(VUnit))),TmSeq( TmIf(Equals(sender, instanceOwner), TmRevert, TmReturn(TmValue(VUnit))), TmSeq( TmAssign("InstanceBuyer", sender), TmSeq( TmAssign("OfferPrice", param_offer_val), TmAssign("CurrentState", TmGetState("OfferPlaced")) ) ))), TmReturn(TmValue(VUnit)))}
                

let param_offer_r : params = (TNat, "param_offer_r")
let param_offer_r_val : term = TmGetParam("param_offer")                      
let reject : func = {requires = And(Equals(TmGetState("OfferPlaced"), TmVar("CurrentState")),Not(Equals(param_offer_r_val, TmValue(VCons(0))))); return_type = TUnit; func_name = "reject"; params = [param_offer_r]; body = TmSeq(TmAssign("InstanceBuyer", TmValue(VAddress("sender"))) , TmSeq( TmAssign("CurrentState", TmGetState("ItemAvailable")),TmReturn(TmValue(VUnit))))   }


let param_offer_a : params = (TNat, "param_offer_a")
let param_offer_a_val : term = TmGetParam("param_offer")    
let accept : func = { requires = And(Equals(TmGetState("OfferPlaced"), TmVar("CurrentState")),Not(Equals( sender, instanceOwner)));return_type = TUnit; func_name = "accept"; params = [param_offer_a]; body = TmSeq(TmIf((Equals(param_offer_a_val, TmValue(VCons(0)))), 
                                                        TmRevert, 
                                                        TmReturn(TmValue(VUnit))), TmSeq(TmAssign("CurrentState", TmGetState("Accept")),TmReturn(TmValue(VUnit))))}
                                                    

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
(Gamma.add "aMark" TAddress Gamma.empty)))))))))))))))

let contractMark : contract_tc = {
  name = "Marketplace";
  init = ( [], And( Equals(TmVar("CurrentState"), TmGetState("ItemAvailable")), And(Greater( TmVar("AskingPrice"), TmValue(VCons(0))), Greater(TmVar("OfferPrice"), TmVar("AskingPrice")))));
  invariant = ([],Greater(TmVar("OfferPrice"), TmVar("AskingPrice"))); 
  behavioral_types = [TmGetState("ItemAvailable"); TmGetState("OfferPlaced"); TmGetState("Accept")];
  vars = [(TmVar("CurrentState"),TState); (TmVar("InstanceOwner"), TAddress);(TmVar("AskingPrice"), TNat);
          (TmVar("InstanceBuyer"), TAddress); (TmVar("OfferPrice"), TNat)];
  cons = marketplace_constructor;
  funcs = [make_offer; reject; accept];
};;

(*-----------------------------------Telemetry----------------------------------------------------*)
let sender : term = TmGetParam("sender")
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
                            TmSeq(TmSeq( TmAssign("ComplianceStatus",TmValue(VTrue)) , TmSeq( TmAssign("CounterParty", sender), 
                            TmSeq(TmAssign("Owner", sender) , TmSeq(TmAssign("Device", param_device_val) , 
                            TmSeq(TmAssign("Max_Temperature", param_max_temp_val ) , TmAssign("Min_Temperature", param_min_temp_val )))) ) ), TmReturn(TmValue(VUnit)) ) )  
 
let param_temp : params = (TNat, "param_temp")     
let param_temp_val : term = TmGetParam("param_temp")                           
let ingest_telemetry : func = {requires = And( Equals(TmGetParam("sender"), TmVar("Device")),Or( Equals(TmVar("CurrentState"), TmGetState("Created")), Equals(TmVar("CurrentState"), TmGetState("InTransit")) )); return_type = TUnit; func_name = "ingest_telemetry"; params = [param_temp]; 
body = TmSeq( TmSeq(TmIf( Or( Greater(param_temp_val, max_temp) , Less( param_temp_val, min_temp)), TmAssign("ComplianceStatus", TmValue(VFalse)) , TmAssign("ComplianceStatus", TmValue(VTrue))),
 TmSeq(TmIf( Not(Equals(sender, device)), TmRevert, TmReturn(TmValue(VUnit))), TmIf( Or( Greater(param_temp_val, max_temp), Less(param_temp_val, min_temp)),
 TmAssign("ComplianceStatus",TmValue(VFalse)),TmReturn(TmValue(VUnit))))),TmReturn(TmValue(VUnit)))  }


 let param_new_counter_party : params = (TAddress, "param_new_counter_party")   
 let param_new_counter_party_val : term = TmGetParam("param_new_counter_party")                         
 let transfer_responsability : func = {requires = And( Equals(TmGetParam("sender"), TmVar("CounterParty")) ,Or( Equals(TmVar("CurrentState"), TmGetState("Created")), Equals(TmVar("CurrentState"), TmGetState("InTransit")))); return_type = TUnit; func_name = "transfer_responsability"; params = [param_new_counter_party]; 
                               body = TmSeq(TmIf( Equals(TmVar("CurrentState"), TmGetState("Created")), TmAssign("CurrentState", TmGetState("InTransit")) , TmAssign("CurrentState", TmGetState("Created"))),                               
                               TmSeq( TmSeq( TmIf( And(Not(Equals(sender,param_new_counter_party_val )),Not(Equals(sender,counterParty))), TmRevert ,TmReturn(TmValue(VUnit))),
                                      TmSeq(TmIf(Equals(param_new_counter_party_val,device), TmRevert, TmReturn(TmValue(VUnit))),TmAssign("CounterParty", param_new_counter_party_val) ) ) , TmReturn(TmValue(VUnit)))) }
 
 let complete : func = {requires =  (Equals(sender,owner )); return_type = TUnit; func_name = "complete"; params = []; body = TmSeq( TmAssign("CurrentState", TmGetState("Completed")) ,TmReturn(TmValue(VUnit)) ) } 
   
                 
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
(Gamma.add "aTelemetry" TAddress Gamma.empty)))))))))))))))))))


let contractTelemetry : contract_tc = {
  name = "Telemetry";
  init = ([],And(Greater(TmVar("Max_Temperature"), TmVar("Min_Temperature")),And(Greater(TmVar("Min_Temperature"), TmValue(VCons(0))), And( Equals(TmVar("ComplianceStatus"), TmValue(VTrue)), Equals(TmVar("CurrentState"),TmGetState("Created"))))));
  invariant = ([],Greater(TmVar("Max_Temperature"), TmVar("Min_Temperature")));
  behavioral_types = [TmGetState("Created"); TmGetState("InTransit"); TmGetState("OutOfCompliance");TmGetState("Completed")];
  vars = [(TmVar("Owner"),TAddress); (TmVar("CurrentState"), TState); (TmVar("CounterParty"), TAddress); (TmVar("Device"), TAddress);
          (TmVar("ComplianceStatus"), TBool); (TmVar("Max_Temperature"), TNat); (TmVar("Min_Temperature"), TNat)];
  cons = telemetry_constructor;
  funcs = [ingest_telemetry; transfer_responsability; complete];
};;

(*-----------------------------------------------------------------------------Bank-------------------------------------------------------------------------------*)
(* Bank *)
let sender : term = TmGetParam("sender") 
let msg_value : term = TmVar("Msg_value")
let balances = TmVar("Balances")

let param_balances : params = (TMapping(TAddress, TNat), "balances_param")
let param_balances_val : term = (TmGetParam("balances_param"))
let bank_constructor : construtor_ = ([param_balances],TmSeq(TmAssign("Balances", param_balances_val), TmReturn(TmValue(VUnit)) ))

let deposit : func = { requires = TmValue(VTrue); return_type = TUnit; func_name = "deposit"; params = []; body = TmSeq( TmMappAss(balances, sender, TmPlus( TmMappSel(balances, sender), msg_value)), TmReturn(TmValue(VUnit)))  }

let get_balance : func = { requires = TmValue(VTrue); return_type = TNat; func_name = "get_balance"; params = []; body = TmReturn( TmMappSel(balances, sender) )  }

let param_to : params = (TAddress, "to")
let param_to_val : term = TmGetParam("to")
let param_amount :params = (TNat, "amount")
let param_amount_val : term = TmGetParam("amount")
let transfer : func = {requires = TmValue(VTrue); return_type = TUnit; func_name = "transfer"; params = [param_to; param_amount]; 
body = TmSeq( TmIf( GreaterOrEquals(TmMappSel(balances, sender), param_amount_val), 
TmSeq( TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender),param_amount_val)),
TmSeq(TmMappAss(balances, param_to_val, TmPlus( TmMappSel(balances, param_to_val),param_amount_val)),TmReturn(TmValue(VUnit)))), 
TmReturn(TmValue(VUnit))), TmReturn(TmValue(VUnit))) }

let param_withdraw_amount : params = (TNat, "W_amount") 
let param_withdraw_amount_val : term = TmGetParam("W_amount") 
let withdraw : func = {requires = TmValue(VTrue); return_type = TUnit; func_name = "withdraw"; params = [param_withdraw_amount]; body =TmSeq( TmIf( GreaterOrEquals(TmMappSel(balances, sender), param_withdraw_amount_val), 
TmSeq(TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender),param_withdraw_amount_val)),
      TmTransfer( sender,param_withdraw_amount_val ) ), 
      TmReturn(TmValue(VUnit))), TmReturn(TmValue(VUnit))) }
              
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
  invariant = ([(TAddress, "param_unsafe")],GreaterOrEquals(TmMappSel(TmVar("Balances"), TmGetParam("param_unsafe") ), TmValue(VCons(0))));
  behavioral_types = [];
  vars = [(TmVar("Msg_value"), TNat);(TmVar("Balances"), TMapping(TAddress,TNat))];
  cons = bank_constructor;
  funcs = [deposit; get_balance; transfer; withdraw];
};;

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
(Gamma.add "aDL" TAddress Gamma.empty))))))))))))))))))))))))))))

let sender : term = TmGetParam("sender")
let owner : term = TmVar("Owner")
let currentState : term = TmVar("CurrentState")
let bank_agent : term = TmVar("BankAgent")
let lockerId : term = TmVar("LockerId")
let curentAuthorizedUser : term = TmVar("CurrentAuthorizedUser")
let exp_Date : term = TmVar("Exp_Date")
let image : term = TmVar("Image")
let tpRequestor : term = TmVar("TPRequestor")
let lockerStatus : term = TmVar("LockerStatus")


let param_bank : params = (TAddress,"param_bank_agent")
let param_bank_val : term = TmGetParam("param_bank_agent")
let dl_constructor = ([param_bank], TmSeq(TmSeq(TmAssign("Owner", TmGetParam("sender")), TmSeq( TmAssign("CurrentState",TmGetState("Requested")), TmAssign("BankAgent", param_bank_val) )), TmReturn(TmValue(VUnit))))
                      
let begin_process_review : func = {requires = And((Equals(owner,sender)),Equals(TmGetState("Requested"),currentState)); return_type = TUnit; func_name = "begin_process_review"; params = []; 
body =TmSeq( TmSeq( TmAssign("BankAgent", sender),TmSeq(TmAssign("LockerStatus",TmValue(VString("Pending"))),TmAssign("CurrentState", TmGetState("DocumentReview"))) ), TmReturn(TmValue(VUnit))) }


let reject_application : func = {requires = And((Equals(bank_agent,sender)),Equals(TmGetState("DocumentReview"),currentState)); return_type = TUnit; func_name = "reject_application"; params = []; 
body =TmSeq( TmSeq( TmAssign("BankAgent", sender),TmSeq(TmAssign("LockerStatus",TmValue(VString("Rejected"))),TmAssign("CurrentState", TmGetState("DocumentReview"))) ), TmReturn(TmValue(VUnit))) }


let param_image : params = (TString,"param_image")
let param_image_val : term = TmGetParam("param_image")
let param_locker_id : params = (TString,"param_locker_id")
let param_locker_id_val : term = TmGetParam("param_locker_id")
let upload_documents : func = {requires = And((Equals(bank_agent,sender)),Equals(TmGetState("DocumentReview"),currentState)); return_type = TUnit; func_name = "upload_documents"; params = [param_image; param_locker_id]; 
body =TmSeq( TmSeq( TmAssign("LockerStatus",TmValue(VString("Approved"))),TmSeq(TmAssign("Image", param_image_val) , TmSeq(TmAssign("LockerId", param_locker_id_val) , TmAssign("CurrentState", TmGetState("AvailableToShare"))))), TmReturn(TmValue(VUnit))) }

let param_tp : params = (TAddress,"param_tp")
let param_tp_val : term = TmGetParam("param_tp")
let param_exp_date : params = (TNat,"param_exp_date")
let param_exp_date_val : term = TmGetParam("param_exp_date")
let share_with_tp : func = {requires = And((Equals(owner,sender)),Equals(TmGetState("AvailableToShare"),currentState)); return_type = TUnit; func_name = "share_with_tp"; params = [param_tp; param_exp_date]; 
body =TmSeq( TmSeq(TmAssign("TPRequestor", param_tp_val),TmSeq( TmAssign("LockerStatus",TmValue(VString("Shared"))),TmSeq(TmAssign("Exp_Date", param_exp_date_val) , TmSeq(TmAssign("CurrentAuthorizedUser", param_tp_val) , TmAssign("CurrentState", TmGetState("SharingWithTp")))))), TmReturn(TmValue(VUnit))) }

let accept_s_request : func = {requires = And(Equals(owner,sender), Equals(currentState, TmGetState("SharingRP"))); return_type = TUnit; func_name = "accept_s_request"; params = []; 
body =TmSeq( TmSeq(TmAssign("CurrentAuthorizedUser", tpRequestor),TmAssign("CurrentState", TmGetState("SharingWithTp"))), TmReturn(TmValue(VUnit))) }

let reject_s_request : func = {requires = And(Equals(owner,sender),Equals(currentState, TmGetState("SharingRP"))); return_type = TUnit; func_name = "reject_s_request"; params = []; 
body =TmSeq( TmSeq(TmAssign("LockerStatus", TmValue(VString("Available"))),TmAssign("CurrentState", TmGetState("SharingWithTp"))), TmReturn(TmValue(VUnit))) }

let request_l_access : func = {requires = And(Not(Equals(owner,sender)),Equals(currentState, TmGetState("SharingRP"))); return_type = TUnit; func_name = "request_l_access"; params = []; 
body =TmSeq( TmSeq(TmAssign("TPRequestor",sender),TmAssign("CurrentState", TmGetState("SharingRP"))), TmReturn(TmValue(VUnit))) }

let release_l_access : func = {requires = And(Equals(curentAuthorizedUser,sender), Equals(currentState, TmGetState("SharingWithTp"))); return_type = TUnit; func_name = "release_l_access"; params = []; 
body =TmSeq( TmSeq(TmAssign("LockerStatus",TmValue(VString("Available"))),TmAssign("CurrentState", TmGetState("AvailableToShare"))), TmReturn(TmValue(VUnit))) }

let revoke_access : func = {requires = And(Equals(owner,sender),Equals(currentState, TmGetState("SharingWithTp"))); return_type = TUnit; func_name = "revoke_access"; params = []; 
body =TmSeq( TmSeq(TmAssign("LockerStatus",TmValue(VString("Available"))),TmAssign("CurrentState", TmGetState("AvailableToShare"))), TmReturn(TmValue(VUnit))) }


let terminate : func = {requires = And(And(Not(Equals(currentState, TmGetState("DocumentReview"))),Not(Equals(currentState, TmGetState("Requested")))),Equals(owner,sender)); return_type = TUnit; func_name = "terminate"; params = []; 
body =TmSeq( TmSeq(TmAssign("LockerStatus",TmValue(VString("Available"))),TmAssign("CurrentState", TmGetState("Terminated"))), TmReturn(TmValue(VUnit))) }

  let contractDL : contract_tc = {
  name = "DL";
  init = ([], Equals(TmGetState("Requested"), currentState));
  invariant = ([],TmValue(VTrue));
  behavioral_types = [TmGetState("DocumentReview"); TmGetState("Requested"); TmGetState("AvailableToShare");TmGetState("SharingWithTp");TmGetState("SharingRP");TmGetState("Terminated")];
  vars = [(TmVar("Owner"),TAddress); (TmVar("CurrentState"), TState); (TmVar("BankAgent"), TAddress); (TmVar("LockerId"), TString);
          (TmVar("CurrentAuthorizedUser"), TAddress); (TmVar("Exp_Date"), TNat); (TmVar("Image"), TString);(TmVar("TPRequestor"), TAddress);(TmVar("LockerStatus"), TString);
          (TmValue(VString("Pending")), TString); (TmValue(VString("Rejected")), TString); (TmValue(VString("Shared")), TString); (TmValue(VString("Approved")), TString); (TmValue(VString("Available")), TString);];
  cons = dl_constructor;
  funcs = [begin_process_review; reject_application; upload_documents;share_with_tp;accept_s_request;reject_s_request;request_l_access;release_l_access;revoke_access;terminate];
};;

(*let contractBank_parsed = parse_contract contractBank.name contractBank.vars gammaBank contractBank.funcs contractBank.behavioral_types contractBank.invariant contractBank.init;;
let contractTelemtry_parsed = parse_contract contractTelemetry.name contractTelemetry.vars gammaTelemetry contractTelemetry.funcs contractTelemetry.behavioral_types contractTelemetry.invariant contractTelemetry.init;;
let contractDL_parsed = parse_contract contractDL.name contractDL.vars gammaDL contractDL.funcs contractDL.behavioral_types contractDL.invariant contractDL.init;;*)



(*-----------------------------------------------------------------------------MarketplaceUnsafe-----------------------------------------------------------------------------*)
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
let acceptUnsafe : func = { requires = (Equals( sender, instanceOwner));
                      return_type = TUnit; func_name = "accept"; params = [param_offer_a]; body = TmSeq(TmIf((Equals(param_offer_a_val, TmValue(VCons(0)))), TmRevert, 
                                                        TmReturn(TmValue(VUnit))), TmSeq(TmAssign("CurrentState", TmGetState("Accept")),TmReturn(TmValue(VUnit))))};;   
let contractMarkUnsafe : contract_tc = {
  name = "MarketplaceUnsafe";
  init = ( [], And( Equals(TmVar("CurrentState"), TmGetState("ItemAvailable")), And(Greater( TmVar("AskingPrice"), TmValue(VCons(0))), Greater(TmVar("OfferPrice"), TmVar("AskingPrice")))));
  invariant = ([],Greater(TmVar("OfferPrice"), TmVar("AskingPrice"))); 
  behavioral_types = [TmGetState("ItemAvailable"); TmGetState("OfferPlaced"); TmGetState("Accept")];
  vars = [(TmVar("CurrentState"),TState); (TmVar("InstanceOwner"), TAddress);(TmVar("Description"), TString); (TmVar("AskingPrice"), TNat);
          (TmVar("InstanceBuyer"), TAddress); (TmVar("OfferPrice"), TNat)];
  cons = marketplace_constructor;
  funcs = [make_offer; reject; acceptUnsafe];
};;


let contractMark_parsed = parse_contract contractMark.name contractMark.vars gammaMark contractMark.funcs contractMark.behavioral_types contractMark.invariant contractMark.init;;
