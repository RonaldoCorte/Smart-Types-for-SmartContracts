(*
   ocamlopt -c types.ml
   ocamlopt -c parser.ml
   ocamlopt -o parser types.cmx parser.cmx
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

let replace l pos a = List.mapi (fun i x -> if i = pos then a else x) l ;; (* preciso igualar *)

let update_var cases t cond var =
  let i = find var !cases in
  let (elem_var, elem_lst) = List.find (fun (v,_) -> v = var) !cases in 
  let new_elem = (elem_var, elem_lst @ [(cond,t)]) in
  cases := replace !cases i new_elem ;;     
                        

let rec find_cases gamma cond t cases =  (* case = [ (var,[(cond,e1);(!cond,e2);(cond,e3)]) ]*) (*se existir um elemento da mesma var com a mesma condicao o que fazer?*) (*so pode ser com map assings, derivar condicao booleana dai*)
  begin match t with
  | TmAssign(x, e) -> if ((hasVar (cases) (x) ) = false) then cases := !cases @ [(x,[(cond,t)])] else ignore(update_var cases t cond x);
                      Printf.printf "(assign) \n";
  | TmMappAss(e1, e2, e3) -> begin match e1 with
                            | TmVar(var) -> if ((hasVar (cases) (var) ) = false) then cases := !cases @ [(var,[(cond,t)])] else ignore(update_var cases t cond var);          
                                            Printf.printf "(map assign) \n";
                            | _ ->  Printf.printf "non implemented \n"; 
                            end;
  | TmRevert -> let x = "Revert" in
                if ((hasVar (cases) (x) ) = false) then (cases := !cases @ [(x,[(cond,t)])]) else (ignore(update_var cases t cond x));
                Printf.printf "(revert) \n";
  | TmSeq(e1, e2) -> ignore(find_cases gamma cond e1 cases); ignore(find_cases gamma cond e2 cases); Printf.printf "(seq) \n";
  | _ -> Printf.printf "non implemented :| \n";
end;;




let rec deal_with_cases l = 
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
  | TString -> Proc
  | TState -> State
  | _ -> Proc
end
;;

let rec parse_term t gamma = 
  begin match t with
  | TmValue(VTrue) -> C_Value(CBool(true))
  | TmValue(VFalse) -> C_Value(CBool(false))
  | TmValue(VCons(v)) -> C_Value(CCons(v)) 
  | TmValue(VAddress(x)) -> C_Value(CProc(x)) 
  | TmValue(VString(s)) -> C_Value(CProc(s)) 
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
  | And(t1, t2) -> C_And(parse_term t1 gamma,parse_term t2 gamma)
  | Or(t1,t2) -> C_Or(parse_term t1 gamma,parse_term t2 gamma)
  | Not(t1)-> C_Not(parse_term t1 gamma)
  | TmAddress(t) ->C_Address(parse_term t gamma)
  | TmAssign(x, e) -> C_Assign(x,parse_term e gamma)
  | Equals(x, e) -> C_Equals(parse_term x gamma, parse_term e gamma)
  | Greater(x, e) -> C_Greater(parse_term x gamma, parse_term e gamma) 
  | Less(x, e) -> C_Less(parse_term x gamma, parse_term e gamma)
  | GreaterOrEquals(x, e) -> C_GreaterOrEquals(parse_term x gamma, parse_term e gamma)
  | LessOrEquals(x, e) -> C_LessOrEquals(parse_term x gamma, parse_term e gamma)
  | TmPlus(x, y) -> C_Plus(parse_term x gamma, parse_term y gamma) (*verificar se sao dois arrays*)
  | TmMinus(x,y) -> C_Minus(parse_term x gamma, parse_term y gamma)
  | TmMult(x,y) -> C_Mult(parse_term x gamma, parse_term y gamma)
  | TmDiv(x,y)-> C_Div(parse_term x gamma, parse_term y gamma)
  | TmSeq(e1, e2) -> C_Seq(parse_term e1 gamma, parse_term e2 gamma)
  | TmBalance(t) ->  C_GetI(C_Get_Param("GlobalBalances"),C_Get_Param("sender"))  (*CHECK*)
  | TmMappAss(e1, e2, e3) -> C_AssignArr(parse_term e1 gamma, parse_term e2 gamma, parse_term e3 gamma)
  | TmMappSel(e1, e2) -> C_GetI(parse_term e1 gamma, parse_term  e2 gamma) 
  | TmReturn(e) -> parse_term e gamma
  | TmIf(t1, t2, t3) -> let cases = ref [] in 
                        find_cases gamma t1 t2 cases;   (*ver o caso de duas definicoes do mesmo array na mesma funcao*)
                        find_cases gamma (Not(t1)) t3 cases;
                        let l = List.map (fun(x,y) -> (x, List.map( fun(c,f) -> (parse_term c gamma),parse_term f gamma) y) ) !cases in
                        deal_with_cases l;
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

(*no requires comparar i com sender*)
let rec parse_params params funcname cubvars cubparams gamma = match params with
| [] -> Printf.printf "All func %s params are parsed! \n" funcname; (*!cubparams;*)
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


(*no requires comparar i com sender*)
let parse_requires requires cub_requires gamma = 
  Printf.printf "Parsing requires .... \n";
  cub_requires := parse_term requires gamma;
  Printf.printf "Requires parsed with success :) \n";;

let parse_fun params funcname cubvars cubparams gamma requires cub_requires return_type body body_cub_func =
  cubparams := !cubparams @ [C_Get_Param("sender")];
  parse_params params funcname cubvars cubparams gamma;
  parse_requires requires cub_requires gamma;
  Printf.printf "Parsing func body .... \n";
  body_cub_func := parse_term body gamma;;
  Printf.printf "Func body parsed with success :) .... \n";;



let rec parse_vars fsvars cubvars gamma = match fsvars with
| [] -> Printf.printf "All vars are parsed! \n"; !cubvars;
| head::body -> let (fs_var,fs_typ) = head in
                let current_var = (parse_term fs_var gamma, parse_type fs_typ) in
                cubvars := !cubvars @ [current_var];
                parse_vars body cubvars gamma;;

let rec process_fun funcs gamma cubvars cubfuncs = 
  match funcs with
  | [] -> Printf.printf "----------------------------------------------------All funcs are parsed...----------------------------------------------------------- \n";
  | h::t -> let cub_requires = ref (C_Value(CBool(true))) in
            let cubparams = ref[] in
            let body_cub_func =  ref (C_Value(CBool(true))) in (*default value*)
            parse_fun h.params h.name cubvars cubparams gamma h.requires cub_requires h.return_type h.body body_cub_func;
           (*let cubfunc = (h.name, !cubparams, !cub_requires, !body_cub_func) in *)
            let cubfunc : cubfunc_ = {
              requires_ = !cub_requires;
              name_ = h.name;
              params_ = !cubparams;
              body_ = !body_cub_func
            } in
            cubfuncs := !cubfuncs @ [cubfunc];
            process_fun t gamma cubvars cubfuncs;;

let generate_unsafe unsafes_fs gamma= (*meter input do utilizador em fs ou minicub*)
  Printf.printf "----------------------------------------------------Generating unsafes...----------------------------------------------------------- \n";
  let unsafes = ref[] in
  List.iter (fun(x) -> unsafes := !unsafes @ [parse_term (Not(x)) gamma]) unsafes_fs;
  !unsafes;;



let parse_contract contract_name fsvars gamma funcs bt unsafes_fs init_fs = 
  let cubvars = ref [] in 
  let cubfuncs = ref[] in
  let unsafe = generate_unsafe unsafes_fs gamma in
  Printf.printf "----------------------------------------------------Parsing vars...----------------------------------------------------------- \n";
  ignore(parse_vars fsvars cubvars gamma);
  Printf.printf "----------------------------------------------------Parsing funcs...----------------------------------------------------------- \n";
  process_fun funcs gamma cubvars cubfuncs;
  let cub_bt = ref[] in 
  List.iter (fun(x) -> (cub_bt := !cub_bt @ [parse_term x gamma])) bt;
  let new_contract : contract_cub = {
    name = contract_name;
    init = (parse_term (init_fs) (gamma));
    unsafe = unsafe;
    behavioral_types = !cub_bt;
    vars = !cubvars;
    funcs = !cubfuncs;
  }in
  new_contract;;

(*let x = Equals(GreaterOrEquals(TmValue(VCons(0)),Not(TmValue(VFalse))),TmValue(VTrue))
let c = parse_term x *)

(*--------------------------------------------------marketplace-------------------------------------------------------*)
                
             
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
let make_offer : func = {requires = Equals(TmGetState("ItemAvailable"), TmVar("CurrentState")); return_type = TUnit; name = "make_offer"; params = [param_offer]; 
                      body = TmSeq( TmSeq( TmIf(Equals(param_offer_val, TmValue(VCons(0))), TmRevert, TmReturn(TmValue(VUnit))),TmSeq( TmIf(Equals(sender, instanceOwner), TmRevert, TmReturn(TmValue(VUnit))), TmSeq( TmAssign("InstanceBuyer", sender), TmSeq( TmAssign("OfferPrice", param_offer_val), TmAssign("CurrentState", TmGetState("OfferPlaced")) ) ))), TmReturn(TmValue(VUnit)))}
                

let param_offer_r : params = (TNat, "param_offer_r")
let param_offer_r_val : term = TmGetParam("param_offer")                      
let reject : func = {requires = And(Equals(TmGetState("OfferPlaced"), TmVar("CurrentState")),Not(Equals(param_offer_r_val, TmValue(VCons(0))))); return_type = TUnit; name = "reject"; params = [param_offer_r]; body = TmSeq(TmAssign("InstanceBuyer", TmValue(VAddress("Sender"))) , TmSeq( TmAssign("CurrentState", TmGetState("ItemAvailable")),TmReturn(TmValue(VUnit))))   }


let param_offer_a : params = (TNat, "param_offer_a")
let param_offer_a_val : term = TmGetParam("param_offer")    
let accept : func = { requires = And(Equals(TmGetState("OfferPlaced"), TmVar("CurrentState")),Not(Equals( sender, instanceOwner)));return_type = TUnit; name = "accept"; params = [param_offer_a]; body = TmSeq(TmIf(Not(Equals(param_offer_a_val, TmValue(VCons(0)))), 
                                                        TmRevert, 
                                                        TmReturn(TmValue(VUnit))), TmSeq(TmAssign("CurrentState", TmGetState("Accept")),TmReturn(TmValue(VUnit))))}
                                                    
                                      

(*-----------------------------------Telemetry----------------------------------------------------*)
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
                            TmSeq(TmSeq( TmAssign("ComplianceStatus",TmValue(VTrue)) , TmSeq( TmAssign("CounterParty", sender), 
                            TmSeq(TmAssign("Owner", sender) , TmSeq(TmAssign("Device", param_device_val) , 
                            TmSeq(TmAssign("Max_Temperature", param_max_temp_val ) , TmAssign("Min_Temperature", param_min_temp_val )))) ) ), TmReturn(TmValue(VUnit)) ) )  
 
let param_temp : params = (TNat, "param_temp")     
let param_temp_val : term = TmGetParam("param_temp")                           
let ingest_telemetry : func = {requires = TmValue(VTrue); return_type = TUnit; name = "ingest_telemetry"; params = [param_temp]; body = TmSeq( TmSeq(TmIf( Not(Equals(sender, device)), TmRevert, TmReturn(TmValue(VUnit))), 
TmSeq(TmSeq(TmIf( Or( Greater(param_temp_val, max_temp), Less(param_temp_val, min_temp)),TmSeq(TmAssign("ComplianceStatus",TmValue(VFalse)),TmReturn(TmValue(VUnit))),TmReturn(TmValue(VUnit))), TmReturn(TmValue(VUnit))) ,TmReturn(TmValue(VUnit)))), TmReturn(TmValue(VUnit)))  }

let param_new_counter_party : params = (TAddress, "param_new_counter_party")   
let param_new_counter_party_val : term = TmGetParam("param_new_counter_party")                         
let transfer_responsability : func = {requires = TmValue(VTrue); return_type = TUnit; name = "transfer_responsability"; params = [param_new_counter_party]; 
                              body = TmSeq( TmSeq( TmIf( And(Not(Equals(sender,param_new_counter_party_val )),Not(Equals(sender,counterParty))), TmRevert ,TmReturn(TmValue(VUnit))),
                                     TmSeq(TmIf(Equals(param_new_counter_party_val,device), TmRevert, TmReturn(TmValue(VUnit))),TmAssign("CounterParty", param_new_counter_party_val) ) ) , TmReturn(TmValue(VUnit))) }

let complete : func = {requires =  Not(Equals(sender,owner )); return_type = TUnit; name = "complete"; params = []; body = TmSeq(  TmAssign("CounterParty", TmValue(VAddress("0x000000000"))) 
                      , TmReturn(TmValue(VUnit)) ) } 
                      
              
              
let gammaTelemetry = (Gamma.add "Sender" TAddress
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
(Gamma.add "0x000000000" TAddress
(Gamma.add "Created" TState
(Gamma.add "InTransit" TState
(Gamma.add "OutOfCompliance" TState
(Gamma.add "Completed" TState
(Gamma.add "param_new_counter_party" TAddress
(Gamma.add "Telemetry" (TContract("Telemetry")) 
(Gamma.add "aTelemetry" TAddress Gamma.empty))))))))))))))))))))

(*-----------------------------------------------------------------------------Bank-------------------------------------------------------------------------------*)
(* Bank *)
let sender : term = TmVar("sender") 
let msg_value : term = TmVar("msg_value")
let balances = TmVar("balances")

let param_balances : params = (TMapping(TAddress, TNat), "balances_param")
let param_balances_val : term = (TmGetParam("balances_param"))
let bank_constructor : construtor_ = ([param_balances],TmSeq(TmAssign("balances", param_balances_val), TmReturn(TmValue(VUnit)) ))

let deposit : func = { requires = TmValue(VTrue); return_type = TUnit; name = "deposit"; params = []; body = TmSeq( TmMappAss(balances, sender, TmPlus( TmMappSel(balances, sender), msg_value)), TmReturn(TmValue(VUnit)))  }

let get_balance : func = { requires = TmValue(VTrue); return_type = TNat; name = "get_balance"; params = []; body = TmReturn( TmMappSel(balances, sender) )  }

let param_to : params = (TAddress, "to")
let param_to_val : term = TmGetParam("to")
let param_amount :params = (TNat, "amount")
let param_amount_val : term = TmGetParam("amount")
let transfer : func = {requires = TmValue(VTrue); return_type = TUnit; name = "transfer"; params = [param_to; param_amount]; body = TmSeq( TmIf( GreaterOrEquals(TmMappSel(balances, sender), param_amount_val), 
TmSeq( TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender),param_amount_val)),
TmSeq(TmMappAss(balances, param_to_val, TmPlus( TmMappSel(balances, param_to_val),param_amount_val)),TmReturn(TmValue(VUnit)))), 
TmReturn(TmValue(VUnit))), TmReturn(TmValue(VUnit))) }

let param_withdraw_amount : params = (TNat, "W_amount") 
let param_withdraw_amount_val : term = TmGetParam("W_amount") 
let withdraw : func = {requires = TmValue(VTrue); return_type = TUnit; name = "withdraw"; params = [param_withdraw_amount]; body =TmSeq( TmIf( GreaterOrEquals(TmMappSel(balances, sender), param_withdraw_amount_val), 
TmSeq(TmMappAss(balances, sender, TmMinus( TmMappSel(balances, sender),param_withdraw_amount_val)),
      TmTransfer( sender,param_withdraw_amount_val ) ), 
      TmReturn(TmValue(VUnit))), TmReturn(TmValue(VUnit))) }

              
let gammaBank = (Gamma.add "sender" TAddress
      (Gamma.add "msg_value" TNat
      (Gamma.add "CurrentState" TState
      (Gamma.add "GlobalBalances" (TMapping(TAddress, TNat))
      (Gamma.add "balances" (TMapping(TAddress, TNat))
      (Gamma.add "balances_param" (TMapping(TAddress, TNat))
      (Gamma.add "InstanceBuyer" TAddress
      (Gamma.add "amount" TNat
      (Gamma.add "to" TAddress
      (Gamma.add "W_amount" TNat
      (Gamma.add "param_price" TNat
      (Gamma.add "param_offer" TNat
      (Gamma.add "Bank" (TContract("Bank")) 
      (Gamma.add "aBank" TAddress Gamma.empty))))))))))))))  


let contractBank : contract_tc = {
  name = "Bank";
  init = GreaterOrEquals(TmMappSel(TmVar("balances"), TmVar("sender") ), TmValue(VCons(0)));
  invariant = [GreaterOrEquals(TmMappSel(TmVar("balances"), TmVar("sender") ), TmValue(VCons(0)))];
  behavioral_types = [];
  vars = [(TmVar("sender"), TAddress); (TmVar("msg_value"), TNat);(TmVar("CurrentState"), TState);(TmVar("balances"), TMapping(TAddress,TNat))];
  cons = bank_constructor;
  funcs = [deposit; get_balance; transfer; withdraw];
};;
      

let contractTelemetry : contract_tc = {
  name = "Telemtry";
  init = And(Greater(TmVar("Max_Temperature"), TmVar("Min_Temperature")),And(Greater(TmVar("Min_Temperature"), TmValue(VCons(0))), And( Equals(TmVar("ComplianceStatus"), TmValue(VTrue)), Equals(TmVar("CurrentState"),TmGetState("Created")))));
  invariant = [Greater(TmVar("Max_Temperature"), TmVar("Min_Temperature"))];
  behavioral_types = [TmGetState("Created"); TmGetState("InTransit"); TmGetState("OutOfCompliance");TmGetState("Completed")];
  vars = [(TmVar("Sender"), TAddress); (TmVar("Owner"),TAddress); (TmVar("CurrentState"), TState); (TmVar("CounterParty"), TAddress); (TmVar("Device"), TAddress);
          (TmVar("ComplianceStatus"), TBool); (TmVar("Max_Temperature"), TNat); (TmVar("Min_Temperature"), TNat)];
  cons = telemetry_constructor;
  funcs = [ingest_telemetry; transfer_responsability; complete];
};;

let contractMark : contract_tc = {
  name = "Marketplace";
  init = And( Equals(TmVar("CurrentState"), TmGetState("ItemAvailable")), Greater( TmVar("AskingPrice"), TmValue(VCons(0))));
  invariant = [Greater(TmVar("OfferPrice"), TmVar("AskingPrice"))]; (*fazer typecheck das invariantes e traduzilas para unsafes*)
  behavioral_types = [TmGetState("ItemAvailable"); TmGetState("OfferPlaced"); TmGetState("Accept")];
  vars = [(TmVar("CurrentState"),TState); (TmVar("InstanceOwner"), TAddress);(TmVar("Description"), TString); (TmVar("AskingPrice"), TNat);
          (TmVar("InstanceBuyer"), TAddress); (TmVar("OfferPrice"), TNat)];
  cons = marketplace_constructor;
  funcs = [make_offer; reject; accept];
};;
(*---------------------------------------------------------------
let cub_requires = ref (C_Value(CBool(true)));;
let cubparams = ref[];;                      
let cond = Equals(param_offer_val, TmValue(VCons(0)));;
let notCond = Not(cond);;
let t1 = TmRevert;;
let t2 = TmReturn(TmValue(VUnit));;
let requires = And(Equals(TmGetState("OfferPlaced"), TmVar("CurrentState")),Not(Equals( sender, instanceOwner)));;
let body =  TmSeq( TmSeq( TmIf(Equals(param_offer_val, TmValue(VCons(0))), TmRevert, TmReturn(TmValue(VUnit))),TmSeq( TmIf(Equals(sender, instanceOwner), TmRevert, TmReturn(TmValue(VUnit))), TmSeq( TmAssign("InstanceBuyer", sender), TmAssign("OfferPrice", param_offer_val) ) )), TmReturn(TmValue(VUnit)));;
let body_cub_func =  ref (C_Value(CBool(true))) ;; (*default value*)

parse_vars contractMark.vars cubvars gammaMark;;
parse_params [param_offer] "make_offer" cubvars cubparams gammaMark;;
parse_requires requires cub_requires gammaMark;;
parse_fun [param_offer] "make_offer" cubvars cubparams gammaMark requires cub_requires TUnit body body_cub_func;; *)



(*let cub_requires = ref (C_Value(CBool(true)));;*)
(*let cub_params = ref[];;*)

parse_contract contractMark.name contractMark.vars gammaMark contractMark.funcs contractMark.behavioral_types contractMark.invariant contractMark.init;;
(*parse_contract contractTelemetry.vars gammaTelemetry contractTelemetry.funcs contractTelemetry.behavioral_types contractTelemetry.invariant contractTelemetry.init;; (*falta requires em fs*)
parse_contract contractBank.vars gammaBank contractBank.funcs contractBank.behavioral_types contractBank.invariant contractBank.init;;*)

(*parse_params make_offer.params "make_offer" cubvars cubparams;;
let requires = And(Equals(TmGetState("OfferPlaced"), TmVar("CurrentState")),Not(Equals(param_offer_r_val, TmValue(VCons(0)))));;
parse_requires requires cub_requires gammaMark;;*)
