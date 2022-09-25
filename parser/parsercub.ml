(*
   ocamlopt -c types.ml
   ocamlopt -c parser.ml
   ocamlopt -o parser types.cmx parser.cmx
*)
open Types
open FinalParser

let getType var vars = 
  let result = ref Int in
  List.iter (fun(x,y) -> if(var = x) then result := y) vars;
  !result;;

(*passar a logica dos dois arrays assign para aqui (em cada assign array ver se ja tem e se ja tive meter assim (dentro de cada funcao))*)
let rec parse_exp t2 s f vars =  (*f is a flag that i use to know in the situation of the case, with respect to assign or assignarray, if i should write or not the var*)
  begin match t2 with
  | C_Value(CBool(true)) -> s^" True"
  | C_Value(CBool(false)) -> s^" False"
  | C_Value(CCons(v))  -> s^string_of_int v
  | C_Value(CProc(x)) ->  s^x
  | C_Value(CUnit) ->s 
  | C_Value(CState(a)) -> s^a
  | C_Value(CMapping(l)) -> s
  | C_GetVar(x) -> s^x
  | C_Get_Param(x) ->s^x
  | C_GetState(x) -> s^x
  | C_And(t1, t2) -> s^" "^parse_exp t1 s f vars ^ " &&" ^ parse_exp t2 s f vars
  | C_Or(t1,t2) ->  s^" "^parse_exp t1 s f vars ^ " ||" ^ parse_exp t2 s f vars
  | C_Not(t1)-> s^" not("^ parse_exp t1 s f vars ^")" 
  | C_Address(t) -> s^" "^parse_exp t2 s f vars
  | C_Assign(x, e) -> if f then s ^parse_exp e s false vars else s^" "^x^" := "^parse_exp e s f vars
  | C_Equals(x, e) ->  s^" "^parse_exp x s f vars ^ " = "  ^ parse_exp e s f vars
  | C_Greater(x, e) ->  s^" "^parse_exp x s f vars^ " > " ^ parse_exp e s f vars
  | C_Less(x, e) ->  s^" "^parse_exp x s f vars^ " < " ^ parse_exp e s f vars
  | C_GreaterOrEquals(x, e) ->  s^" "^parse_exp x s f vars ^ " >= " ^ parse_exp e s f vars
  | C_LessOrEquals(x, e) ->  s^" "^parse_exp x s f vars ^ " <= " ^ parse_exp e s f vars
  | C_Plus(x, y) -> s^" "^parse_exp x s f vars ^ " + " ^ parse_exp y s f vars
  | C_Minus(x,y) -> s^" "^parse_exp x s f vars ^ " - " ^ parse_exp y s f vars
  | C_Mult(x,y) ->  s^" "^parse_exp x s f vars^ " * " ^ parse_exp y s f vars
  | C_Div(x,y) ->  s^" "^parse_exp x s f vars ^ " / " ^ parse_exp y s f vars
  | C_Seq(e1, e2) -> let s1 = ref "" in
                     let s2 = ref "" in
                      begin match e1 with
                      | C_Value(CUnit) -> s1 := "" 
                      | _ -> s1 := parse_exp e1 s f vars
                      end;
                      begin match e2 with
                      | C_Value(CUnit) -> s2 := ""
                      | _ -> s2 := parse_exp e2 s f vars
                      end;
                      if ( not(String.equal !s1 "") && not(String.equal !s2 "")) then s^" "^ !s1 ^ ";\n" ^ !s2
                      else if ((String.equal !s1 "") && not(String.equal !s2 "")) then s^ " " ^ !s2
                      else if (not (String.equal !s1 "") && (String.equal !s2 "")) then s ^ " " ^ !s1
                      else s;
                     
  | C_AssignArr(e1, e2, e3) -> if f then s^parse_exp e3 s false vars else s^parse_exp e1 s f vars^"["^parse_exp e2 s f vars^"] := "^parse_exp e3 s f vars
  | C_GetI(e1, e2) -> s^" "^parse_exp e1 s f vars ^"["^parse_exp e2 s f vars ^"] "
  | C_Case(v,c) -> let t = getType (C_GetVar(v)) vars in
                   let x = ref"" in
                   begin match t with
                   | CArr(a,b) -> x:= "[c]"
                   | _ ->  x:= ""
                   end;
                   let case =  s^v^ !x ^" := case\n" in
                   let current = ref"" in
                   List.iter (fun(x,y) -> current := !current ^"|"^(parse_exp x "" false vars) ^ ": " ^(parse_exp y "" true) vars ^"\n" ) c;
                   current := String.sub !current 0 ((String.length !current) -1);
                   (case) ^ (!current); 

end;;

let parse_simple_type t = 
  match t with
  | Int -> "int"
  | Bool ->"bool"
  | Proc ->"proc"
  | _ -> ""
;;

let rec parse_type_vars t s x= 
  match t with
  | Int ->s^"var " ^x^" : int \n"
  | Bool ->s^"var "^x^" : bool \n"
  | Proc ->s^"var "^x^" : proc \n"
  | CArr(a,b) ->s^"array " ^x^"["^(parse_simple_type a)^"] : " ^ (parse_simple_type b) ^" \n"
  | State ->s^"var "^x^ " : state\n"
  | Unit ->s
;;

let rec parse_var_name s var t =
  match var with
  | C_GetVar(x) | C_GetState(x) -> s^parse_type_vars t s x
  | _ -> s
;;

let rec parse_behavioral_types bt s = 
  match bt with
  | [] -> s;
  | h::t -> begin match h with
            | C_GetState(x) ->if t != [] then s ^ x ^" | " ^ parse_behavioral_types t s else  s ^ x ^ parse_behavioral_types t s;
            | _ -> s;
            end;;

let parse_vars cubvars buffer = 
  Printf.printf "Parsing vars... \n";
  let s = "" in
  List.iter (fun(var, var_typ) -> Buffer.add_string (buffer) (parse_var_name s var var_typ) ) cubvars;
  Buffer.add_string buffer ("var Revert : bool \n");
  buffer;;

let begin_parsing_bts bt s = 
  if bt != [] then"type state = " ^ parse_behavioral_types bt s else  "";;


let rec parse_params params = 
  match params with
  | []-> ""
  | h::t -> begin match h with
            | C_Get_Param(x)->  if t != [] then x ^" "^ (parse_params t) else x 
            | _ -> "" 
          end
;;


let parse_init init b vars = 
  let (params, cond) = init in
  let p = parse_params params in
  let s = parse_exp cond "" false vars in
  Buffer.add_string (b) ("init ("^ p ^") {" ^ s ^ "} \n");;


let parse_unsafe init b vars= 
  let (params, cond) = init in
  let p = parse_params params in
  let s = parse_exp cond "" false vars in
  Buffer.add_string (b) ("unsafe ("^ p ^") {" ^ s ^ "} \n");;
  
let write_fun_signature name params = 
  let s = " \n" ^ "transition "^name^"("^ parse_params params ^")" in
  s;;

let parse_body body vars = 
  let s = "{\n"^(parse_exp body "" false vars) ^ "\n}\n" in
  s;;

let parse_requires req vars = 
  begin match req with
  | C_Value(CBool(true)) -> " \nrequires{ true } \n";
  | C_Value(CBool(false)) ->" \nrequires{ false } \n";
  | _ -> " \nrequires{" ^ (parse_exp (req) ("") (false) vars) ^ "} \n";
end;;

let rec parse_fun func buffer_vars vars= 
  Printf.printf "Parsing fun %s \n" func.name_;
  let s_params = write_fun_signature func.name_ func.params_ in
  Buffer.add_string (buffer_vars) (s_params);
  let req = parse_requires func.requires_ vars in
  Printf.printf " -> %s" req;
  Buffer.add_string (buffer_vars) (req);
  let body = parse_body func.body_ vars in
  Buffer.add_string (buffer_vars) (body);;


let rec parse_contract contract= 
  let file = contract.name^"_parsed.cub" in
  let oc = open_out file in
  let buffer_vars = Buffer.create 32 in 
  let s = begin_parsing_bts contract.behavioral_types "" ^ " \n" in
  Buffer.add_string (buffer_vars) (s);
  ignore(parse_vars contract.vars buffer_vars );
  String.iter (fun(x) ->Printf.printf "%c " x) (Buffer.contents buffer_vars);
  parse_init contract.init buffer_vars contract.vars;
  parse_unsafe contract.unsafe buffer_vars contract.vars; 
  List.iter ( fun(x) -> parse_fun x buffer_vars contract.vars) contract.funcs; 
  Buffer.output_buffer oc buffer_vars; 
  close_out oc;
  Printf.printf "Parsing contract...\n";;
          
 parse_contract contractBank_parsed;; (*TRATAR DOS ROLES DE QUEM PODE INVOCAR*) (*basta meter no requires*)
 parse_contract contractMark_parsed;; 
 parse_contract contractTelemtry_parsed;;


         


