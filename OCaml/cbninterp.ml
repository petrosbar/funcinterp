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
type expr = IntExpr of int                          (* Integer expression *)
          | Var of (name)                           (* Variable *)
          | BinOp of (operator * (expr * expr))     (* Binary operation *)
          | Constructor  of (name * (expr list))    (* Constructor, e.g., (cons (x nil)) *)
          | Abs of (name * expr)                    (* Lambda abstraction *)
          | App of (expr * expr)                    (* Function application *)
          | Case of (expr * (branch list))          (* Case expression *)


and  branch = Branch of (pattern * expr)

(*
 * A value is an integer, a constructor, or a thunk.
 *)
type value = IntVal of int
           | Thunk of (env * name * expr)
           | ConstrVal of (name * (value list))

(*
 * The environment, where values are stored.
 *)
and env = Env of ((name * value) list)


(* val : extractFromList : pattern list -> string list *)
let rec extractFromList xs = match xs with
    | (Varp x::xs) -> x :: extractFromList xs
    | _ -> []

(* 
 * Take an environment and a list of expressions and store each one 
 * in its own thunk.
 *)
(* val listOfThunks : env -> expr list -> value list *)
let rec listOfThunks env exprlist = match exprlist with
    | (x::xs) -> Thunk ((Env env), "_", x) :: listOfThunks env xs
    | []      -> []


(*
 * Evaluation function.
 *)
(* val eval : env -> expr -> value *)
let rec eval env = function
    | IntExpr n -> IntVal n
    (* 
     * A variable is bound to either an integer value or a thunk (i.e., a λ_.e).
     * In the first case, just return the value while in the second
     * return the evaluated expression of the thunk.
     *)
    | Var x -> 
        begin match List.assoc x env with
            (* 
             * If x is either an integer or a constructor, just return it. Otherwise, 
             * if it's a thunk, evaluate its body.
             *)
            | IntVal n as intv -> intv
            | ConstrVal (name, explist) as const -> const
            | Thunk (Env env, str, expr) -> eval env expr
        end
    (* The evaluation of an abstraction is a thunk. *)
    | Abs (n, ex) -> Thunk ((Env env), n, ex)
    (* Function application. *)
    | App (ex1, ex2) ->
        begin match eval env ex1 with
            (* Make sure ex1 evaluates to a thunk... *)
            | Thunk (Env en, n, ex) ->
                (* ...and build a second one with ex2. *)
                let thunk = Thunk ((Env env), "_", ex2)
                (* 
                 * Finally, insert the second thunk into the environment and evaluate ex1. 
                 * If during ex1's evaluation ex2's value is needed, then (and only then) evaluate it.
                 *)
                in eval ((n, thunk) :: en) ex
            | _ -> failwith "Invalid function application"
        end
    (* Constructor evaluation. *)
    | Constructor (cname, explist) ->
        (* Return the constructor with its arguments evaluated. *)
        let vallist = listEval env explist
        in ConstrVal (cname, vallist)
    (* Case expression evaluation. *)
    | Case (ex, (brlist)) ->
        matchPattern env ex brlist
    (* Binary operation evaluation. *)
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


(* val binOp : operator -> int -> int -> int *)
and binOp oprtr op1 op2 = match oprtr with
    | Add   -> op1 + op2
    | Subtr -> op1 - op2
    | Mult  -> op1 * op2


(*
 * matchPattern evaluates the expression part of the branch whose pattern matches the case argument.
 *
 *) 
(* val matchPattern : env -> expr -> branch list -> value *)
and matchPattern env casexp blist = match blist with
    | br::brlist ->
        begin match br with
            (* Case analysis on the patterns. *)
            | Branch (IntExprp n, pexp) ->
                (* If pattern is an integer value then we're forced to evaluate case's argument eagerly. *)
                let evex = eval env casexp in
                begin match evex with
                    | IntVal m -> 
                        if n = m then
                            (* If match succeeded, evaluate the associated expression. *)
                            eval env pexp
                        else
                            (* Otherwise, move to the next branch. *)
                            matchPattern env casexp brlist
                    (* Likewise, if the evaluated expression isn't an integer, then move to the next branch. *)
                    | _ -> matchPattern env casexp brlist
                end
            (* Pattern is constructor. *)
            | Branch (Constrp (pname, plist), cexpr) ->
                begin match casexp with
                    (* 
                     * If case's argument is a constructor and its name equals that of the pattern,
                     * insert its arguments in a list of thunks, append the list to env 
                     * and evaluate the associated expression.
                     *)
                    | Constructor (cname, clist) ->
                        if pname = cname then
                            let thunklist = listOfThunks env clist in
                            let env' = List.combine (extractFromList plist) thunklist in
                            eval (List.append env env') cexpr
                        else
                            matchPattern env casexp brlist
                    (*
                     * If it's an application, then make its argument a thunk
                     * and call matchPattern again with the body of the abstraction.
                     * This way, we bring the first argument to weak head normal form.
                     *)
                    | App (ex1, ex2) -> 
                        begin match  ex1 with
                            | Abs (str, expr1) -> 
                                let expr2 = (str, Thunk (Env [], "_", ex2)) in
                                matchPattern (expr2::env) expr1 blist
                            | _ -> failwith "Invalid case expression"
                        end
                    | _ -> matchPattern env casexp brlist
                end
            (* Pattern is variable. Matching is irrefutable. *)
            | Branch (Varp x, vexp) ->
                let thunk = Thunk ((Env env), "_", casexp) in 
                let env' = (x, thunk) :: env in
                    eval env' vexp
        end
    | [] -> failwith "Unmatched"


(* Test Cases (TODO: They should be in a separate file) *)

(* 4 + 2 *)
let test1 = 
    eval [] (BinOp (Add, (IntExpr 4, IntExpr 2)));;

(* λx.1 + 2 *)
let test2 = 
    eval [] (Abs ("x", (BinOp (Add, (IntExpr 1, IntExpr 2)))));;

(* λx.x + 2 *)
let test3 = 
    eval [("x", IntVal 2)] (Abs ("x", (BinOp (Add, (Var "x", IntExpr 2)))));;

(* (λx.x + 2) 10 *)
let test4 = 
    eval [("y", IntVal 2)] 
        (App  (Abs ("x", BinOp (Add, (Var "x", IntExpr 2))), IntExpr 10));;


(*
 * Omega, DOES NOT HALT. (λx.x x) (λx.x x)
 *
 *let test5 = 
 *  eval []
 *       (App (Abs ("x", App (Var "x", Var "x")), Abs ("x", App (Var "x", Var "x"))));;
 *)

(*
 * case (λx.x) 5 of
 *   5          -> 1 + 1
 *   List(x, y) -> x
 *)
let test6 = 
    eval []
        (Case (App (Abs ("x", Var "x"), (IntExpr 5)), [
            Branch ((IntExprp 5), (BinOp (Add, (IntExpr 1, IntExpr 1))));
            Branch (Constrp ("List", [Varp "x"; Varp "y"]), (Var "x"))])
        );;

(*
 * case List((λx.x) 5) of
 *   List(y)    -> y
 *   5          -> 1 + 1
 *)
let test7 = 
    eval []
        (Case (Constructor ("List", [App (Abs ("x", (Var "x")), (IntExpr 5))]), [
            Branch (Constrp ("List", [Varp "y"]), (Var "y"));
            Branch (IntExprp 5, BinOp (Add, (IntExpr 1, IntExpr 1)))])
        );;

(* 
 * case Cons1 omega of
 *   Cons1 y -> 2
 *   Cons2 y -> 1 + 2
 *)
let test8 = 
    eval []
        (Case (Constructor 
                ("Cons1", [((App ( 
                    Abs ("x", App (Var "x", Var "x")), 
                    Abs ("x", App (Var "x", Var "x")))))]), [
            Branch (Constrp ("Cons1", [Varp "y"]), (IntExpr 2));
            Branch (Constrp ("Cons2", [Varp "y"]), BinOp (Add, (IntExpr 1, IntExpr 2)))])
        );;

(* 
 * DOES NOT HALT!
 *
 * case List omega of
 *   List y -> y
 *   5      -> 1 + 1
 *)
(*
let test9 = 
    eval []
        (Case 
            (Constructor ("List", [((App 
                (Abs ("x", App (Var "x", Var "x")), 
                 Abs ("x", App (Var "x", Var "x")))))]), 
           [Branch (Constrp ("List", [Varp "y"]), (Var "y"));
            Branch (IntExprp 5, BinOp (Add, (IntExpr 1, IntExpr 1)))])
        );;
*)

let test10 = 
    eval []
        (Case (App (Abs ("x", (Constructor ("Cons1", [Var "x"]))), (IntExpr 51)), [
            Branch (Constrp ("Cons1", [Varp "y"]), (IntExpr 100))])
        );;
            

(* 
 * case (λx.Cons1[x]) Ω of
 *   Cons1[y] -> y
 *)
let test11 = 
    eval []
        (Case (App (Abs ("x", (Constructor ("Cons1", [Var "x"]))), (App 
                (Abs ("x", App (Var "x", Var "x")), 
                 Abs ("x", App (Var "x", Var "x"))))), [
            Branch (Constrp ("Cons1", [Varp "y"]), (IntExpr 1))])
        );;
