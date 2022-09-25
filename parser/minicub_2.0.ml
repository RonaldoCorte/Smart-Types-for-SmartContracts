type cub_typ =
| Int 
| Bool 
| Proc

type cub_values =
| CBool of bool
| CCons of int            (* n *)
| CProc of string      
| CUnit                   (* u *)
| CMapping of (values * values) list 

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
| C_And of exp * exp          (* x C_And y *)
| C_Or of exp * exp            (* x C_Or y *)
| C_LessOrEquals of exp * exp  (* x <= 3*)
| C_GreaterOrEquals of exp * exp (* x >= 3*)
| C_GetI of exp * exp         (* C_Arr[i] *)    (*CHANGED*)
| C_Get_Param of string
| C_GetVar of string
| C_TS of string (*typestate*)
| C_Dec_param of cub_typ * string
| C_Decl of cub_typ * string         (* var x : int *)
| C_Arr of cub_typ * cub_typ * string    (* C_Arr x [Type] : Type *)
| C_Assign of string * exp       (* x = 3 *)       
| C_AssignArr of exp * exp * exp (*  C_Arr[i] = 4*)  (*CHANGED*)
| C_Seq of exp * exp          (* exp;exp *)
| C_RandomProcess of exp
| C_Case of exp * (exp * exp) list  (*  CurrentState := C_Case | CurrentState = Created : InTransit;*) 


type behavioral_types = exp list  
type cub_func = string * exp list * exp * exp
type cub_vars =  exp list
type cub_contract = cub_vars * cub_func list(* * init * unsafe*)
(*---------------------------------------------------------------------*)
let turn = C_Decl(Proc,"Turn")
let want = C_Arr(Proc, Bool, "Want")
let crit = C_Arr(Proc, Bool, "Crit")

let param_init = C_Dec_param(Proc,"i") 
let param_init_j = C_Dec_param(Proc,"j") 
let init = C_And(C_Not( C_GetI("Want",VProc("i"))),C_Not(C_GetI("Turn",VProc("i"))))
let unsafe = C_And(C_Equals(C_GetI("Crit",VProc("i")),VBool(true)),C_Not(C_Equals(C_GetI("Crit",VProc("j")),VBool(true))))

let param_i_req = C_Dec_param(Proc,"i_req") 
let param_j_req = C_Dec_param(Proc,"j_req") 
let requires_req = C_Not(C_GetI("Want",C_Get_Param("i_req")))
let body_req = C_Case( C_GetI("Want",C_Get_Param("j_req")) , [( C_Equals(C_Get_Param("i_req"), C_Get_Param("j_req")), VBool(true)); (NotEquals(C_Get_Param("i_req"), C_Get_Param("j_req")), C_GetI("want",C_Get_Param("j_req")))   ] ) 
let req = ("req", [param_i_req], requires_req, body_req)

let param_enter = C_Dec_param(Proc,"enter") 
let requires_enter = C_And( C_Equals(C_GetI("Want",C_Get_Param("enter")), VBool(true)), C_And(  C_Not(C_GetI("Crit",VProc("enter"))), C_Equals(C_GetI("Turn", VProc("Turn")), C_Get_Param("i_req"))))
let body_enter = C_Case(  C_GetI("Crit",C_Get_Param("enter")) , [( C_Equals(C_Get_Param("i_req"), C_Get_Param("j_req")), VBool(true)); (NotEquals(C_Get_Param("i_req"), C_Get_Param("j_req")), C_GetI("Crit",C_Get_Param("enter")))] )
let enter = ("enter", [param_enter], requires_enter, body_enter)

let param_exit = C_Dec_param(Proc,"exit") 
let param_j_exit = C_Dec_param(Proc,"j_exit") 
let requires_exit = C_Not(C_GetI("Crit",C_Get_Param("i_req")))
let body_exit = C_Seq( C_RandomProcess(VProc("Turn")), C_Seq(  C_Case(  C_GetI("Crit",C_Get_Param("enter")) , [( C_Equals(C_Get_Param("exit"), C_Get_Param("j_exit")), VBool(true)); (NotEquals(C_Get_Param("exit"), C_Get_Param("j_exit")), C_GetI("Crit",C_Get_Param("enter")))] ) , C_Case( C_GetI("Want",C_Get_Param("j_exit")) , [( C_Equals(C_Get_Param("exit"), C_Get_Param("j_exit")), VBool(true)); (NotEquals(C_Get_Param("exit"), C_Get_Param("j_exit")), C_GetI("want",C_Get_Param("j_exit")))   ] ) ) )
let exit = ("exit", [param_exit], requires_exit, body_exit)
(*---------------------------------------------------------------------*)

(*------------------------------simple bank----------------------------*)

let balances = C_Arr( Proc, Int, "Balances" )
let random_amount = C_Arr(Proc, Int, "Random_Amounts")
let sender = VProc("Sender")
let sender_Balance = C_Decl(Int,"Sender_Balance")
let currentRandom =  C_Decl(Int,"Current_Random")

let param_init = C_Dec_param(Proc, "param_init")
let init = C_And(C_GreaterOrEquals(C_GetI("Random", C_Get_Param("param_init")) , VInt(0)), C_GreaterOrEquals(C_GetI("Balances", C_Get_Param("param_init")) , VInt(0)))
let unsafe = C_LessOrEquals(C_GetI("Balances", C_Get_Param("param_init")) , VInt(0))

let param_getBalance = C_Dec_param(Proc,"i_gb")
let requires_getBalance = C_Equals(C_Get_Param("i_gb"), C_GetVar("Sender"))
let body_getBalance = C_Assign("Sender_Balance", C_GetI("Balances",C_GetVar("Sender")) ) 
let getBalance = ("getBalance", [param_getBalance], requires_getBalance, body_getBalance)

let param_deposit = C_Dec_param(Proc,"param_deposit")
let requires_deposit = C_And(C_Equals(C_Get_Param("param_deposit"), C_GetVar("Sender")), C_Greater(C_GetVar("Current_Random"), VInt(0)))
let body_deposit = C_Seq( C_Assign("Current_Random",C_GetI("Random_Amounts", C_Get_Param("param_deposit")) ) , C_AssignArr("Balances", C_Get_Param("param_deposit"), C_Plus(C_GetVar("CurrentRandom"), C_GetI("Balances", C_Get_Param("param_deposit")))))
let deposit = ("deposit", [param_deposit], requires_deposit, body_deposit) 

let param_transfer_i = C_Dec_param(Proc,"transfer_i")
let param_transfer_j = C_Dec_param(Proc,"transfer_j")
let requires_transfer = C_And( C_Equals(C_Get_Param("i_gb"), C_GetVar("Sender")), C_And( C_GreaterOrEquals(C_GetI("Balances",C_Get_Param("param_transfer_i")), C_GetVar("Current_Random")), C_And(C_GreaterOrEquals(C_GetI("Balances",C_Get_Param("param_transfer_j")), C_GetVar("Current_Random")), C_Greater(C_GetVar("Current_Random"), VInt(0)) )) )
let body_transfer = C_Seq(C_Assign("Current_Random",C_GetI("Random_Amounts", C_Get_Param("param_deposit")) ), C_Case(C_GetI("Balances", C_Get_Param("c")), [(C_Equals(C_Get_Param("c"), C_Get_Param("param_transfer_i")),C_Minus( C_GetI("Balances", C_Get_Param("param_transfer_i")),C_GetVar("CurrentRandom") )); ((C_Equals(C_Get_Param("c"), C_Get_Param("param_transfer_j")),C_Plus( C_GetI("Balances", C_Get_Param("param_transfer_j")),C_GetVar("CurrentRandom") )))]))
let transfer = ("transfer", [param_transfer_i;param_transfer_j], requires_transfer, body_transfer)

let param_withdraw = C_Dec_param(Proc,"param_withdraw")
let requires_withdraw =C_And( C_Equals(C_Get_Param("i_gb"), C_GetVar("Sender")), C_And( C_GreaterOrEquals(C_GetI("Balances",C_Get_Param("param_transfer_i")), C_GetVar("Current_Random")), C_Greater(C_GetVar("Current_Random"), VInt(0)) )) 
let body_withdraw = C_Seq(C_Assign("Current_Random",C_GetI("Random_Amounts", C_Get_Param("param_deposit")) ), C_AssignArr("Balances", C_Get_Param("param_deposit"), C_Plus(C_GetVar("CurrentRandom"), C_GetI("Balances", C_Get_Param("param_deposit")))))
let withdraw = ("withdraw",[param_withdraw], requires_withdraw, body_withdraw)   

(*---------------------------------marketplace-azure-----------------------*)
(*behavioral_types*)
let marketplace_state : behavioral_types = [C_TS("ItemAvailable"); C_TS("OfferPlaced"); C_TS("Accept")]

(* Var Declarations*) 
  
let owner = C_Decl(Proc, "Owner")
let buyer =  C_Decl(Proc, "Buyer")

let askingPrice = C_Decl(Int, "AskingPrice")
let offerPrice = C_Decl(Int, "OfferPrice")
let description = C_Decl(Int, "Description")
let currentState = C_TS("CurrentState")
let random_offers = C_Arr(Proc, Int, "Random_offers")

(* Initialization *)
let init = (C_And(C_Greater( C_GetI("Random_offers",VProc("i")),VInt(0)), C_And( C_Equals(C_GetVar("CurrentState"), C_TS("ItemAvailable")), C_Greater(C_GetVar("AskingPrice") , VInt(0)))))
(*  unsafe *)
let unsafe = C_And(C_LessOrEquals(C_GetVar("OfferPrice"),VInt(0)), C_Equals(C_GetVar("CurrentState"), C_TS("Accept")))
(*cub_func*)
let param_make_offer_i = C_Dec_param(Proc,"i")
let param_make_offer_j = C_Dec_param(Proc,"j")
let requires_make_offer : exp = C_And(C_Equals(C_Get_Param("param_make_offer_i"), C_GetVar("Buyer")), C_And(C_Equals(C_TS("ItemAvailable"), C_GetVar("CurrentState")), C_And(C_GreaterOrEquals(C_GetVar("Buyer_balance") , C_GetI("Random_offers", C_Get_Param("param_make_offer_i"))), C_GreaterOrEquals(C_GetVar("ItemValue") , C_GetI("Random_offers", C_Get_Param("param_make_offer_j")))) ))
let params_make_offer = [param_make_offer_i;param_make_offer_j]
let body_make_offer = C_Seq( C_Assign("Offer", C_GetI("Random_offers", C_Get_Param("param_make_offer_i"))), C_Assign(" CurrentState", C_TS("OfferPlaced") ) )
let func_make_offer : cub_func = ("make_offer",params_make_offer, requires_make_offer, body_make_offer ) 

let param_accept_i  = C_Dec_param(Proc,"i") 
let requires_accept : exp = C_And(C_Equals(C_Get_Param("param_accept_i"), C_GetVar("Owner")), C_And(C_Equals(C_TS("OfferPlaced"), C_GetVar("CurrentState")), C_And(C_GreaterOrEquals(C_GetVar("Offer"),VInt(0)), C_And( C_Less(C_GetVar("Offer"), C_GetVar("Buyer_balance")), C_Equals(VBool(false), C_GetVar("IsSold")) ) ) ))
let body_accept = C_Seq(C_Assign("OwnerBalance", C_Plus(C_GetVar("Owner_balance"), C_GetVar("Offer")) ), C_Seq(C_Assign("BuyerBalance", Minus(C_GetVar("Buyer_balance"), C_GetVar("Offer")) ), C_Seq(C_Assign("IsSold", VBool(true)), C_Assign("CurrentState", C_TS("Accept")) )) )
let params_accept = [param_accept_i]
let func_accept : cub_func = ("accept",params_accept, requires_accept, body_accept)
                         
let param_reject_i = C_Dec_param(Proc,"i") 
let requires_reject = C_And(C_Equals(C_Get_Param("param_accept_i"), C_GetVar("owner")), C_Equals(C_TS("OfferPlaced"), C_GetVar("currentState")))
let body_reject  = C_Seq(C_Assign("CurrentState", C_TS("ItemAvailable")), C_Assign("IsSold", VBool(false)) )
let params_reject = [param_reject_i]
let func_reject : cub_func = ("reject",params_reject, requires_reject, body_reject)

(*------------------------------------telemtry-azure-------------------------------------*)
(*behavioral_types*)
let telemetry_state : behavioral_types = ["Created"; "InTransit"; "OutOfCompliance"; "Completed"]

(* Var Declarations*)  
let owner = C_Decl(Proc, "Owner")
let device =  C_Decl(Proc, "Device")
let currentCounterParty =  C_Decl(Proc, "CurrentCounterParty")
let maxTemp = C_Decl(Int, "MaxTemp")
let minTemp = C_Decl(Int, "MinTemp")
let complianceStatus = C_Decl(Bool, "ComplianceStatus")

let init = C_And(C_Greater(C_GetVar("Max_Temp"),C_GetVar("Min_Temp")),C_And(C_Equals(C_GetVar("CurrentState"), C_TS("Created")),C_Equals(C_GetVar("ComplianceStatus"), VBool(true))))
let unsafe = C_And( C_Equals(C_GetVar("ComplianceStatus"), VBool(false)), C_Not(C_Equals(C_GetVar("CurrentState"), C_TS("OutOfCompliance"))))

let param_it = C_Dec_param(Proc,"param_it") 
let requires_it = C_And(C_Equals(C_Get_Param("i"), C_GetVar("Device")), C_Or(C_Equals(C_GetVar("ComplianceStatus"), C_TS("Created")),C_Equals(C_GetVar("ComplianceStatus"), C_TS("InTransit")) ))                                 (*ver como expressar o "_"*)
let body_it = C_Seq(C_Case( C_GetVar("ComplianceStatus"), [( C_Or(C_Greater(C_GetI("RandomTemps",C_Get_Param("param_it")), C_GetVar("MaxTemp")),C_Less(C_GetI("RandomTemps",C_Get_Param("param_it")), C_GetVar("MinTemp")) ),VBool(false)); (VBool(true),VBool(true))]), C_Case( C_GetVar("CurrentState"),[ (C_Or(C_Greater(C_GetI("RandomTemps",C_Get_Param("param_it")), C_GetVar("MaxTemp")),C_Less(C_GetI("RandomTemps",C_Get_Param("param_it")), C_GetVar("MinTemp")) ),C_TS("OutOfCompliance"))]))
let fun_it = ("ingest_telemetry",[param_it], requires_it, body_it)

let param_tr = C_Dec_param(Proc,"param_tr") 
let requires_tr = C_And(C_Equals(C_Get_Param("i"), C_GetVar("CurrentCounterParty")), C_Or(C_Equals(C_GetVar("ComplianceStatus"), C_TS("Created")),C_Equals(C_GetVar("ComplianceStatus"), C_TS("InTransit")) ))                                 (*ver como expressar o "_"*)
let body_tr = C_Seq(C_Assign("CurrentCounterParty",C_Get_Param("param_tr")), C_Case( C_GetVar("CurrentState"),[ (C_Or(C_Greater(C_GetI("RandomTemps",C_Get_Param("param_it")), C_GetVar("MaxTemp")),C_Less(C_GetI("RandomTemps",C_Get_Param("param_it")), C_GetVar("MinTemp")) ),C_TS("OutOfCompliance"))]))
let fun_it = ("transfer_resp",[param_tr], requires_tr, body_tr)

let param_c = C_Dec_param(Proc,"param_c") 
let requires_tr = C_And(C_Equals(C_GetVar("Owner"), C_Get_Param("param_c")), C_Equals(C_GetVar("currentState"), C_TS("InTransit")))
let body_tr = C_Assign("CurrentState", C_TS("Completed"))
let fun_it = ("transfer_resp",[param_c], requires_tr, body_tr)


