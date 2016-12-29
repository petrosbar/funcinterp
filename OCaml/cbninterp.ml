type name = string

type operator = Add | Subtr | Mult

type pattern = IntExprp of int
             | Varp of name
             | Constrp of name * (pattern list)

type expr = IntExpr of int
    | Var of (name)
    | BinOp of (operator * (expr * expr))
    | Constructor  of (name * (expr list))
    | Abs of (name * expr)
    | App of (expr * expr)
    | Case of (expr * (branch list))
    | Thunk of (env * name * expr)

and  branch = Branch of (pattern * expr)

and env = Env of ((name * expr) list)


let rec eval env = function
    | IntExpr n -> IntExpr n
    | Var x -> eval env (List.assoc x env)
    | Abs (n, ex) -> Thunk ((Env env), n, ex)
    | App (ex1, ex2) -> match eval env ex1 with
        | Thunk (Env en, n, ex) -> eval ((n, ex2) :: en) ex
	| _ -> failwith "Invalid function application"
    | Constructor (cname, explist) -> Constructor (cname, explist)
    | Case (ex, (brlist)) -> let evex = eval env ex in
                             matchPattern env evex brlist
    | BinOp (operator, (op1, op2)) -> 
        let x = eval env op1 in
	let y = eval env op2 in
            match (x, y) with 
                (IntExpr o1, IntExpr o2) -> IntExpr (binOp operator o1 o2)
    | _ -> failwith "Unmatched" 

and binOp oprtr op1 op2 =
    (match oprtr with
        | Add   -> op1 + op2
        | Subtr -> op1 - op2
        | Mult  -> op1 * op2)

and matchPattern env exp (br::brlist) = match exp with
    Constructor (name, explist) ->
        match br with
            Branch ((IntExprp n), _) -> matchPattern env (Constructor (name, explist)) brlist  
(*            Branch (Constructor (cname, clist), cexpr ->
	        if cname = name then 
                    let varlist = zip (extractFromList clist) explist in
		    let env1 = *)

let rec zip xs ys = match xs, ys with
    | [], _ -> []
    | _, [] -> []
    | (x :: xs), (y :: ys) -> (x, y) :: zip xs ys

let rec extractFromList xs = match xs with
    | (Varp x::xs) -> x :: extractFromList xs
    | _ -> []

