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

and  branch = Branch of (pattern * expr)

type value = IntVal of int
           | Thunk of (env * name * expr)
           | ConstrVal of (name * (expr list))

and env = Env of ((name * value) list)


(* TODO: Use List.combine *)
let rec zip xs ys = match xs, ys with
    | [], _ -> []
    | _, [] -> []
    | (x :: xs), (y :: ys) -> (x, y) :: zip xs ys

let rec extractFromList xs = match xs with
    | (Varp x::xs) -> x :: extractFromList xs
    | _ -> []


(* val eval : env -> expr -> value *)
let rec eval env = function
    | IntExpr n -> IntVal n
    | Var x -> List.assoc x env
    | Abs (n, ex) -> Thunk ((Env env), n, ex)
    | App (ex1, ex2) -> 
        begin match eval env ex1 with
            | Thunk (Env en, n, ex) ->
                (* Insert ex2 as a (unevaluated) thunk into the environment... *)
                let thunk = Thunk ((Env env), n, ex2)
                (* ... and evaluate ex2. *)
                in eval ((n, thunk) :: en) ex
            | _ -> failwith "Invalid function application"
        end 
    | Constructor (cname, explist) -> ConstrVal (cname, explist)
    | Case (ex, (brlist)) -> let evex = eval env ex in
                             matchPattern env evex brlist
    | BinOp (operator, (op1, op2)) -> 
        let x = eval env op1 in
        let y = eval env op2 in
            begin match (x, y) with 
                (IntVal o1, IntVal o2) -> IntVal (binOp operator o1 o2)
                | _ -> failwith "Invalid binary operands"
            end
    | _ -> failwith "Unmatched" 

(* val binOp : operator -> int -> int -> int *)
and binOp oprtr op1 op2 = match oprtr with
    | Add   -> op1 + op2
    | Subtr -> op1 - op2
    | Mult  -> op1 * op2

(* val matchPattern : env -> expr -> branch list -> value *)
and matchPattern env exp blist = match blist with
    | br::brlist -> 
        begin match exp with
            | ConstrVal (name, explist) as constr->
                begin match br with
                    | Branch (IntExprp n, _) -> matchPattern env constr brlist
                    | Branch (Constrp (cname, clist), cexpr) ->
	                    if cname = name then 
                            let varlist = List.combine (extractFromList clist) (evalListExpr env explist) in
		                    let env1 = List.append env varlist in
                            eval env1 cexpr
                        else 
                            matchPattern env constr brlist
                    | Branch (Varp vname, vexpr) -> eval ((vname, constr) :: env) vexpr      
                end
            | IntVal n as intexpr ->
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

(* 
 * XXX: This should not be here. Add an interface file and put function
 * signatures in it.
 *)
and evalListExpr env exprlist = match exprlist with
    | (x::xs) -> eval env x :: evalListExpr env xs
    | []      -> []


let test1 = 
    eval [] (BinOp (Add, (IntExpr 4, IntExpr 2)));;

let test2 = 
    eval [] (Abs ("x", (BinOp (Add, (IntExpr 1, IntExpr 2)))));;

let test3 = 
    eval [("x", IntVal 2)] (Abs ("x", (BinOp (Add, (Var "x", IntExpr 2)))));;

let test4 = 
    eval [("y", IntVal 2)] 
        (App  (Abs ("x", BinOp (Add, (Var "x", IntExpr 2))), IntExpr 10));;

(*
 * (λx.x x) (λx.x x) [Omega]
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
