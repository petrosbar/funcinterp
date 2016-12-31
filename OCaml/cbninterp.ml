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

let rec zip xs ys = match xs, ys with
    | [], _ -> []
    | _, [] -> []
    | (x :: xs), (y :: ys) -> (x, y) :: zip xs ys

let rec extractFromList xs = match xs with
    | (Varp x::xs) -> x :: extractFromList xs
    | _ -> []


let rec eval env = function
    | IntExpr n -> IntExpr n
    | Var x -> eval env (List.assoc x env)
    | Abs (n, ex) -> Thunk ((Env env), n, ex)
    | App (ex1, ex2) -> 
        begin match eval env ex1 with
            | Thunk (Env en, n, ex) -> eval ((n, ex2) :: en) ex
            | _ -> failwith "Invalid function application"
        end
    | Constructor (cname, explist) -> Constructor (cname, explist)
    | Case (ex, (brlist)) -> let evex = eval env ex in
                             matchPattern env evex brlist
    | BinOp (operator, (op1, op2)) -> 
        let x = eval env op1 in
        let y = eval env op2 in
            (match (x, y) with 
                (IntExpr o1, IntExpr o2) -> IntExpr (binOp operator o1 o2)
                | _ -> failwith "das")
    | _ -> failwith "Unmatched" 

and binOp oprtr op1 op2 =
    match oprtr with
        | Add   -> op1 + op2
        | Subtr -> op1 - op2
        | Mult  -> op1 * op2

and matchPattern env exp blist = match blist with
    | br::brlist -> 
        begin match exp with
            | Constructor (name, explist) as constr->
                begin match br with
                    | Branch (IntExprp n, _) -> matchPattern env constr brlist
                    | Branch (Constrp (cname, clist), cexpr) ->
	                    if cname = name then 
                            let varlist = zip (extractFromList clist) explist in
		                    let env1 = List.append env varlist in
                            eval env1 cexpr
                        else 
                            matchPattern env constr brlist
                    | Branch (Varp vname, vexpr) -> eval ((vname, constr) :: env) vexpr      
                end
            | IntExpr n as intexpr ->
                begin match br with
                    | Branch (IntExprp p, expr) -> 
                        if n = p then
                            eval env expr
                        else 
                            matchPattern env intexpr brlist
                    | Branch (Varp p, expr) ->
                        let env1 = (p, intexpr) :: env in
                        eval env1 expr
                    | Branch (Constrp (_, _), _) -> matchPattern env intexpr brlist
                end
            | v -> matchPattern env v brlist
        end
    | [] -> failwith "Unmatched"


let test1 = 
    eval [] (BinOp (Add, (IntExpr 4, IntExpr 2)));;

let test2 = 
    eval [] (Abs ("x", (BinOp (Add, (IntExpr 1, IntExpr 2)))));;

let test3 = 
    eval [("x", IntExpr 2)] (Abs ("x", (BinOp (Add, (Var "x", IntExpr 2)))));;

let test4 = 
    eval [("y", IntExpr 2)] 
        (App  (Abs ("x", BinOp (Add, (Var "x", IntExpr 2))), IntExpr 10));;

(*
 * (λx.x x) (λx.x x) (Omega)
 *
 *let test5 = 
 *  eval []
 *       (App (Abs ("x", App (Var "x", Var "x")), Abs ("x", App (Var "x", Var "x"))));;
 *)

let test6 = 
    eval []
        (Case (App (Abs ("x", Var "x"), (IntExpr 5)), [
            Branch ((IntExprp 5), (BinOp (Add, (IntExpr 1, IntExpr 1))));
            Branch (Constrp ("List", [Varp "x"; Varp "y"]), (Var "x"))])
        );;

let test7 = 
    eval []
        (Case (Constructor ("List", [App (Abs ("x", (Var "x")), (IntExpr 5))]), [
            Branch (Constrp ("List", [Varp "y"]), (Var "y"));
            Branch (IntExprp 5, BinOp (Add, (IntExpr 1, IntExpr 1)))])
        );;

let test8 = 
    eval []
        (Case (Constructor ("List", [((App (Abs ("x", App (Var "x", Var "x")), Abs ("x", App (Var "x", Var "x")))))]), [
            Branch (Constrp ("List", [Varp "y"]), (IntExpr 2));
            Branch (IntExprp 5, BinOp (Add, (IntExpr 1, IntExpr 1)))])
        );;

let test9 = 
    eval []
        (Case (Constructor ("List", [((App (Abs ("x", App (Var "x", Var "x")), Abs ("x", App (Var "x", Var "x")))))]), [
            Branch (Constrp ("List", [Varp "y"]), (Var "y"));
            Branch (IntExprp 5, BinOp (Add, (IntExpr 1, IntExpr 1)))])
        );;