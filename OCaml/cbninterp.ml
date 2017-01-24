(*
 * An abstract machine, i.e., a call-by-name interpreter for the defined language.
 *)

type name = string

type operator = Add | Subtr | Mult

(*
 * This is the pattern of a case expression, i.e., the part
 * of the branch which case's argument is matched against.
 *)
type pattern = IntExprp of int
             | Varp of name
             | Constrp of name * (pattern list)

(*
 * Language's terms (expressions).
 *)
type expr = IntExpr of int                        (* Integer expression *)
          | Var of (name)                         (* Variable *)
          | BinOp of (operator * (expr * expr))   (* Binary operation *)
          | Constructor  of (name * (expr list))  (* Constructor, e.g., (cons (x nil)) *)
          | Abs of (name * expr)                  (* Lambda abstraction *)
          | App of (expr * expr)                  (* Function application *)
          | Case of (expr * (branch list))        (* Case expression *)


and  branch = Branch of (pattern * expr)

(*
 * A value is an integer, or constructor, or a thunk.
 *)
type value = IntVal of int
           | Thunk of (env * name * expr)
           | ConstrVal of (name * (value list))

(*
 * The environment where variables and thunks are stored.
 *)
and env = Env of ((name * value) list)


(* val : extractFromList : pattern list -> string *)
let rec extractFromList xs = match xs with
    | (Varp x::xs) -> x :: extractFromList xs
    | _ -> []

(* 
 * Take an environment and a list of expressions and store each one 
 * in its own thunk.
 *)
(* val listOfThunks : env -> expr list -> value list *)
let rec listOfThunks env exprlist = match exprlist with
    | (x::xs) -> Thunk ((Env env), "dummy", x) :: listOfThunks env xs
    | []      -> []

(*
 * Evaluation function.
 *)
(* val eval : env -> expr -> value *)
let rec eval env = function
    | IntExpr n -> IntVal n
    | Var x -> evalThunk env (List.assoc x env)
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
    | Constructor (cname, explist) ->
        (* Return the constructor with its arguments evaluated. XXX do we really need to fully evaluate it?*)
        let vallist = listEval env explist in
            ConstrVal (cname, vallist)
    | Case (ex, (brlist)) -> let evex = eval env ex in (* XXX ex should not be fully evaluated. *)
                             matchPattern env evex brlist
    | BinOp (operator, (op1, op2)) -> 
        let x = eval env op1 in
        let y = eval env op2 in
            begin match (x, y) with 
                (IntVal o1, IntVal o2) -> IntVal (binOp operator o1 o2)
                | _ -> failwith "Invalid binary operands"
            end

(* val : listEval -> env -> expr list -> value list *)
and listEval env exprlist =
    match exprlist with
        | (x::xs) -> eval env x :: listEval env xs
        | []      -> []

(* val evalThunk : env -> value -> value *)
and evalThunk env value = 
    match value with
        | IntVal n -> IntVal n
        | Thunk ((Env env'), n, exp) -> eval env' exp
        | ConstrVal (cname, exprlist) as constr -> constr
        

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
                            (* 
                             * Associate variables contained in the pattern of the matched branch
                             * with the unevaluated expressions which are turned into thunks.
                             *)
                            let varlist = List.combine (extractFromList clist) (listOfThunks env explist) in
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
