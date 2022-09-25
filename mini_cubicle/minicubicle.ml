(* This is an OCaml editor.
   Enter your program here and send it to the toplevel using the "Eval code"
   button or [Ctrl-e]. *)

(* TYPES *)
type typ =
  | Int 
  | Bool 
  | Proc

type exp =
  | Dec_param of typ * string
  | VInt of int
  | VBool of bool
  | VString of string
  | VProc of string
  | Plus of exp * exp (*  3 + 4 *)
  | Minus of exp * exp (*  3 - 4 *) 
  | Decl of typ * string         (* var x : int *)
  | Arr of typ * typ * string    (* Arr x [Type] : Type *)
  | Assign of string * exp       (* x = 3 *)
  | AssignArr of string * exp * exp (*  arr[i] = 4*)
  | Case of exp * (exp * exp) list  (*  CurrentState := case | CurrentState = Created : InTransit;*) 
  | GetI of string * exp         (* arr[i] *)
  | Equal of exp * exp         (* x == 3 *)
  | NotEquals of exp * exp     (* x != 3 *)
  | Less of exp * exp          (* x < 3*)
  | Greater of exp * exp       (* x > 3*)
  | Not of exp                  (* !x *)
  | And of exp * exp           (* x AND y *)
  | Or of exp * exp            (* x OR y *)
  | LessOrEquals of exp * exp  (* x <= 3*)
  | GreaterOrEquals of exp * exp (* x >= 3*)
  | Seq of exp * exp          (* exp;exp *)


(* meter; como expressao (seq) *) (*separar as operações booleanas*)


type behavioral_types = string list (*mudar typestates*)
type func = string * exp list * exp * exp
    
(* ----------------------------- refrigerated tranportation -------------------------------------*)
let ref_state : behavioral_types = ["Created"; "InTransit"; "OutOfCompliance"; "Completed"]
let device = Decl(Proc, "Device")
let current_party = Decl(Proc, "Current_party")
let owner_rt = Decl(Proc, "Owner_rt") 
let max_temp = Decl(Int, "Max_temp")
let min_temp = Decl(Int, "Min_temp")
let current_temp = Decl(Int, "Current_temp")
let currentState_rt : exp = VString("CurrentState") 
let random_temps = Arr(Proc, Int, "Random_temps") 
    
let param_init_rt : exp = Dec_param(Proc,"i") 
let init : exp = And(Greater( max_temp,min_temp), And(Equal(currentState_rt , VString("Created")), And(Greater( current_temp ,min_temp),Greater( min_temp, current_temp) )))
    
let param_ingest_telemetry_i = Dec_param(Proc,"i") 
let params_it = [param_ingest_telemetry_i]
let requires_it = And( Equal( param_ingest_telemetry_i, device), Or( Equal(currentState_rt , VString("Created")), Equal(currentState_rt , VString("InTransit"))) )
let body_it = Seq(Assign("Current_temp", GetI("Random_temps", param_ingest_telemetry_i)), Case(currentState_rt, [(Or(Greater( GetI("Random_temps", param_ingest_telemetry_i), max_temp), Less( GetI("Random_temps", param_ingest_telemetry_i), min_temp)), Assign("currentState_rt", VString("OutOfCompliance")))]) )
let fun_it = ("ingest_telemetry", params_it, requires_it, body_it)
             
let param_tr_i = Dec_param(Proc,"i") 
let param_tr_j = Dec_param(Proc,"j") 
let params_tr = [param_tr_i; param_tr_j]
let requires_tr = And( Equal( param_ingest_telemetry_i, current_party), Or( Equal(currentState_rt , VString("Created")), Equal(currentState_rt , VString("InTransit"))) )
let body_tr = Seq(Assign("current_party",param_ingest_telemetry_i), Case(currentState_rt, [(Equal( currentState_rt, VString("Created")), Assign("currentState_rt", VString("InTransit")))]) )
let fun_it = ("transfer_responsability", params_tr, requires_tr, body_tr) 
  
let param_c_i = Dec_param(Proc,"i") 
let params_c = [param_ingest_telemetry_i]
let requires_c = And( Equal( param_ingest_telemetry_i, owner),  Equal(currentState_rt , VString("InTransit")) )
let body_c = Assign("currentState_rt",  VString("Completed"))
let fun_c = ("transfer_responsability", params_c, requires_c, body_c) 

    
         
                                   

    
