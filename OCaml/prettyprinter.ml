open Cbninterp

let str_op op = match op with
    | Add   -> "+"
    | Subtr -> "-"
    | Mult  -> "*"

let rec strpat p = match p with
    | IntExprp n -> string_of_int n
    | Varp x -> x
    | Constrp (name, plist) -> name ^ "(" ^ (patlist plist) ^ ")"

and patlist p = match p with
    | [] -> ""
    | x::[] -> strpat x
    | x::xs -> strpat x ^ ", " ^ patlist xs

let rec prettyprint program = 
    print_string (strdef program ^ "\n")

and strdef p = match p with 
    | IntExpr n -> string_of_int n
    | Var x -> x
    | Constructor (name, elist) -> name ^ "(" ^ (strlist elist) ^ ")"
    | BinOp (operator, (op1, op2)) -> 
        "(" ^ (strdef op1) ^ 
        " " ^ (str_op operator) ^ 
        " " ^ (strdef op2) ^ ")"
    | Abs (vname, body) -> "fun " ^ vname ^ " = " ^ (strdef body)
    | App (e1, e2) -> "(" ^ (strdef e1) ^ ") (" ^ (strdef e2) ^ ")"
    | Case (ex, brlist) -> 
        "(case " ^ (strdef ex) ^ 
        " of " ^ " \n[" ^ (strbranch brlist) ^ 
        "]" ^ ")"
    | Thunk (env, v, expr) -> "fun " ^ v ^ " = " ^ (strdef expr)

and strbranch brl = match brl with
    | [] -> ""
    | Branch (p, ex)::[]  -> (strpat p) ^ " -> " ^ (strdef ex)
    | Branch (p, ex)::brs -> (strpat p) ^ " -> " ^ (strdef ex) ^ "; " ^ (strbranch brs)

and strlist l = match l with 
    | [] -> ""
    | x::[] -> strdef x
    | x::xs -> strdef x ^ ", " ^ strlist xs 
