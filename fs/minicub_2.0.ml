(* TYPES *)
type typ =
  | Int 
  | Bool 
  | Proc


type exp =
  | VInt of int
  | VProc of string
  | Plus of exp * exp (*  3 + 4 *)
  | Minus of exp * exp (*  3 - 4 *) 
  | VBool of bool
  | Equals of exp * exp         (* x == 3 *)
  | NotEquals of exp * exp     (* x != 3 *)
  | Less of exp * exp          (* x < 3*)
  | Greater of exp * exp       (* x > 3*)
  | Not of exp                  (* !x *)
  | And of exp * exp          (* x AND y *)
  | Or of exp * exp            (* x OR y *)
  | LessOrEquals of exp * exp  (* x <= 3*)
  | GreaterOrEquals of exp * exp (* x >= 3*)
  | GetI of string * exp         (* arr[i] *)
  | Get_Param of string
  | GetVar of string
  | TS of string (*typestate*)

type command = 
  | Dec_param of typ * string
  | Decl of typ * string         (* var x : int *)
  | Arr of typ * typ * string    (* Arr x [Type] : Type *)
  | Assign of string * exp       (* x = 3 *)
  | AssignArr of string * exp * exp (*  arr[i] = 4*)
  | Seq of command * command          (* exp;exp *)
  | RandomProcess of exp
  | Case of exp * (exp * exp) list  (*  CurrentState := case | CurrentState = Created : InTransit;*) 
  

type behavioral_types = exp list  
type func = string * command list * exp * command
(*---------------------------------------------------------------------*)
let turn = Decl(Proc,"Turn")
let want = Arr(Proc, Bool, "Want")
let crit = Arr(Proc, Bool, "Crit")

let param_init = Dec_param(Proc,"i") 
let param_init_j = Dec_param(Proc,"j") 
let init = And(Not( GetI("Want",VProc("i"))),Not(GetI("Turn",VProc("i"))))
let unsafe = And(Equals(GetI("Crit",VProc("i")),VBool(true)),Not(Equals(GetI("Crit",VProc("j")),VBool(true))))

let param_i_req = Dec_param(Proc,"i_req") 
let param_j_req = Dec_param(Proc,"j_req") 
let requires_req = Not(GetI("Want",Get_Param("i_req")))
let body_req = Case( GetI("Want",Get_Param("j_req")) , [( Equals(Get_Param("i_req"), Get_Param("j_req")), VBool(true)); (NotEquals(Get_Param("i_req"), Get_Param("j_req")), GetI("want",Get_Param("j_req")))   ] ) 
let req = ("req", [param_i_req], requires_req, body_req)

let param_enter = Dec_param(Proc,"enter") 
let requires_enter = And( Equals(GetI("Want",Get_Param("enter")), VBool(true)), And(  Not(GetI("Crit",VProc("enter"))), Equals(GetI("Turn", VProc("Turn")), Get_Param("i_req"))))
let body_enter = Case(  GetI("Crit",Get_Param("enter")) , [( Equals(Get_Param("i_req"), Get_Param("j_req")), VBool(true)); (NotEquals(Get_Param("i_req"), Get_Param("j_req")), GetI("Crit",Get_Param("enter")))] )
let enter = ("enter", [param_enter], requires_enter, body_enter)

let param_exit = Dec_param(Proc,"exit") 
let param_j_exit = Dec_param(Proc,"j_exit") 
let requires_exit = Not(GetI("Crit",Get_Param("i_req")))
let body_exit = Seq( RandomProcess(VProc("Turn")), Seq(  Case(  GetI("Crit",Get_Param("enter")) , [( Equals(Get_Param("exit"), Get_Param("j_exit")), VBool(true)); (NotEquals(Get_Param("exit"), Get_Param("j_exit")), GetI("Crit",Get_Param("enter")))] ) , Case( GetI("Want",Get_Param("j_exit")) , [( Equals(Get_Param("exit"), Get_Param("j_exit")), VBool(true)); (NotEquals(Get_Param("exit"), Get_Param("j_exit")), GetI("want",Get_Param("j_exit")))   ] ) ) )
let exit = ("exit", [param_exit], requires_exit, body_exit)
(*---------------------------------------------------------------------*)

(*------------------------------simple bank----------------------------*)

let balances = Arr( Proc, Int, "Balances" )
let random_amount = Arr(Proc, Int, "Random_Amounts")
let sender = VProc("Sender")
let sender_Balance = Decl(Int,"Sender_Balance")
let currentRandom =  Decl(Int,"Current_Random")

let param_init = Dec_param(Proc, "param_init")
let init = And(GreaterOrEquals(GetI("Random", Get_Param("param_init")) , VInt(0)), GreaterOrEquals(GetI("Balances", Get_Param("param_init")) , VInt(0)))
let unsafe = LessOrEquals(GetI("Balances", Get_Param("param_init")) , VInt(0))

let param_getBalance = Dec_param(Proc,"i_gb")
let requires_getBalance = Equals(Get_Param("i_gb"), GetVar("Sender"))
let body_getBalance = Assign("Sender_Balance", GetI("Balances",GetVar("Sender")) ) 
let getBalance = ("getBalance", [param_getBalance], requires_getBalance, body_getBalance)

let param_deposit = Dec_param(Proc,"param_deposit")
let requires_deposit = And(Equals(Get_Param("param_deposit"), GetVar("Sender")), Greater(GetVar("Current_Random"), VInt(0)))
let body_deposit = Seq( Assign("Current_Random",GetI("Random_Amounts", Get_Param("param_deposit")) ) , AssignArr("Balances", Get_Param("param_deposit"), Plus(GetVar("CurrentRandom"), GetI("Balances", Get_Param("param_deposit")))))
let deposit = ("deposit", [param_deposit], requires_deposit, body_deposit) 

let param_transfer_i = Dec_param(Proc,"transfer_i")
let param_transfer_j = Dec_param(Proc,"transfer_j")
let requires_transfer = And( Equals(Get_Param("i_gb"), GetVar("Sender")), And( GreaterOrEquals(GetI("Balances",Get_Param("param_transfer_i")), GetVar("Current_Random")), And(GreaterOrEquals(GetI("Balances",Get_Param("param_transfer_j")), GetVar("Current_Random")), Greater(GetVar("Current_Random"), VInt(0)) )) )
let body_transfer = Seq(Assign("Current_Random",GetI("Random_Amounts", Get_Param("param_deposit")) ), Case(GetI("Balances", Get_Param("c")), [(Equals(Get_Param("c"), Get_Param("param_transfer_i")),Minus( GetI("Balances", Get_Param("param_transfer_i")),GetVar("CurrentRandom") )); ((Equals(Get_Param("c"), Get_Param("param_transfer_j")),Plus( GetI("Balances", Get_Param("param_transfer_j")),GetVar("CurrentRandom") )))]))
let transfer = ("transfer", [param_transfer_i;param_transfer_j], requires_transfer, body_transfer)

let param_withdraw = Dec_param(Proc,"param_withdraw")
let requires_withdraw =And( Equals(Get_Param("i_gb"), GetVar("Sender")), And( GreaterOrEquals(GetI("Balances",Get_Param("param_transfer_i")), GetVar("Current_Random")), Greater(GetVar("Current_Random"), VInt(0)) )) 
let body_withdraw = Seq(Assign("Current_Random",GetI("Random_Amounts", Get_Param("param_deposit")) ), AssignArr("Balances", Get_Param("param_deposit"), Plus(GetVar("CurrentRandom"), GetI("Balances", Get_Param("param_deposit")))))
let withdraw = ("withdraw",[param_withdraw], requires_withdraw, body_withdraw)   

(*---------------------------------marketplace-azure-----------------------*)
(*behavioral_types*)
let marketplace_state : behavioral_types = [TS("ItemAvailable"); TS("OfferPlaced"); TS("Accept")]

(* Var Declarations*) 
  
let owner = Decl(Proc, "Owner")
let buyer =  Decl(Proc, "Buyer")

let askingPrice = Decl(Int, "AskingPrice")
let offerPrice = Decl(Int, "OfferPrice")
let description = Decl(Int, "Description")
let currentState = TS("CurrentState")
let random_offers = Arr(Proc, Int, "Random_offers")

(* Initialization *)
let init = (And(Greater( GetI("Random_offers",VProc("i")),VInt(0)), And( Equals(GetVar("CurrentState"), TS("ItemAvailable")), Greater(GetVar("AskingPrice") , VInt(0)))))
(*  unsafe *)
let unsafe = And(LessOrEquals(GetVar("OfferPrice"),VInt(0)), Equals(GetVar("CurrentState"), TS("Accept")))
(*func*)
let param_make_offer_i = Dec_param(Proc,"i")
let param_make_offer_j = Dec_param(Proc,"j")
let requires_make_offer : exp = And(Equals(Get_Param("param_make_offer_i"), GetVar("Buyer")), And(Equals(TS("ItemAvailable"), GetVar("CurrentState")), And(GreaterOrEquals(GetVar("Buyer_balance") , GetI("Random_offers", Get_Param("param_make_offer_i"))), GreaterOrEquals(GetVar("ItemValue") , GetI("Random_offers", Get_Param("param_make_offer_j")))) ))
let params_make_offer = [param_make_offer_i;param_make_offer_j]
let body_make_offer = Seq( Assign("Offer", GetI("Random_offers", Get_Param("param_make_offer_i"))), Assign(" CurrentState", TS("OfferPlaced") ) )
let func_make_offer : func = ("make_offer",params_make_offer, requires_make_offer, body_make_offer ) 

let param_accept_i  = Dec_param(Proc,"i") 
let requires_accept : exp = And(Equals(Get_Param("param_accept_i"), GetVar("Owner")), And(Equals(TS("OfferPlaced"), GetVar("CurrentState")), And(GreaterOrEquals(GetVar("Offer"),VInt(0)), And( Less(GetVar("Offer"), GetVar("Buyer_balance")), Equals(VBool(false), GetVar("IsSold")) ) ) ))
let body_accept = Seq(Assign("OwnerBalance", Plus(GetVar("Owner_balance"), GetVar("Offer")) ), Seq(Assign("BuyerBalance", Minus(GetVar("Buyer_balance"), GetVar("Offer")) ), Seq(Assign("IsSold", VBool(true)), Assign("CurrentState", TS("Accept")) )) )
let params_accept = [param_accept_i]
let func_accept : func = ("accept",params_accept, requires_accept, body_accept)
                         
let param_reject_i = Dec_param(Proc,"i") 
let requires_reject = And(Equals(Get_Param("param_accept_i"), GetVar("owner")), Equals(TS("OfferPlaced"), GetVar("currentState")))
let body_reject  = Seq(Assign("CurrentState", TS("ItemAvailable")), Assign("IsSold", VBool(false)) )
let params_reject = [param_reject_i]
let func_reject : func = ("reject",params_reject, requires_reject, body_reject)

(*------------------------------------telemtry-azure-------------------------------------*)
(*behavioral_types*)
let telemetry_state : behavioral_types = ["Created"; "InTransit"; "OutOfCompliance"; "Completed"]

(* Var Declarations*)  
let owner = Decl(Proc, "Owner")
let device =  Decl(Proc, "Device")
let currentCounterParty =  Decl(Proc, "CurrentCounterParty")
let maxTemp = Decl(Int, "MaxTemp")
let minTemp = Decl(Int, "MinTemp")
let complianceStatus = Decl(Bool, "ComplianceStatus")

let init = And(Greater(GetVar("Max_Temp"),GetVar("Min_Temp")),And(Equals(GetVar("CurrentState"), TS("Created")),Equals(GetVar("ComplianceStatus"), VBool(true))))
let unsafe = And( Equals(GetVar("ComplianceStatus"), VBool(false)), Not(Equals(GetVar("CurrentState"), TS("OutOfCompliance"))))

let param_it = Dec_param(Proc,"param_it") 
let requires_it = And(Equals(Get_Param("i"), GetVar("Device")), Or(Equals(GetVar("ComplianceStatus"), TS("Created")),Equals(GetVar("ComplianceStatus"), TS("InTransit")) ))                                 (*ver como expressar o "_"*)
let body_it = Seq(Case( GetVar("ComplianceStatus"), [( Or(Greater(GetI("RandomTemps",Get_Param("param_it")), GetVar("MaxTemp")),Less(GetI("RandomTemps",Get_Param("param_it")), GetVar("MinTemp")) ),VBool(false)); (VBool(true),VBool(true))]), Case( GetVar("CurrentState"),[ (Or(Greater(GetI("RandomTemps",Get_Param("param_it")), GetVar("MaxTemp")),Less(GetI("RandomTemps",Get_Param("param_it")), GetVar("MinTemp")) ),TS("OutOfCompliance"))]))
let fun_it = ("ingest_telemetry",[param_it], requires_it, body_it)

let param_tr = Dec_param(Proc,"param_tr") 
let requires_tr = And(Equals(Get_Param("i"), GetVar("CurrentCounterParty")), Or(Equals(GetVar("ComplianceStatus"), TS("Created")),Equals(GetVar("ComplianceStatus"), TS("InTransit")) ))                                 (*ver como expressar o "_"*)
let body_tr = Seq(Assign("CurrentCounterParty",Get_Param("param_tr")), Case( GetVar("CurrentState"),[ (Or(Greater(GetI("RandomTemps",Get_Param("param_it")), GetVar("MaxTemp")),Less(GetI("RandomTemps",Get_Param("param_it")), GetVar("MinTemp")) ),TS("OutOfCompliance"))]))
let fun_it = ("transfer_resp",[param_tr], requires_tr, body_tr)

let param_c = Dec_param(Proc,"param_c") 
let requires_tr = And(Equals(GetVar("Owner"), Get_Param("param_c")), Equals(GetVar("currentState"), TS("InTransit")))
let body_tr = Assign("CurrentState", TS("Completed"))
let fun_it = ("transfer_resp",[param_c], requires_tr, body_tr)


