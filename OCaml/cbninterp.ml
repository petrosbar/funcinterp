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
            | IntVal n -> IntVal n
            | Thunk (Env env, str, expr) -> eval env expr
            | ConstrVal (name, explist) as const -> const
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
        (*
         * The argument of a case expression must be brought into Weak Head Normal Form 
         * before calling matchPattern. Thus, if it is a constructor turn its enclosed list
         * of arguments/expressions into a list of thunks but do not evaluate any of them,
         * and call matchPattern on it. Anything else follows the usual reduction rules.
         *)
        begin match ex with
            | Constructor (cname, explist) -> 
                let thunklist = listOfThunks env explist in
                let ex' = ConstrVal (cname, thunklist) in
                matchPattern env ex' brlist
            | _ -> 
                let evex = eval env ex in
                matchPattern env evex brlist
        end
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
(* val matchPattern : env -> value -> branch list -> value *)
and matchPattern env casexp blist = match blist with
    | br::brlist -> 
        begin match casexp with
            | ConstrVal (name, tlist) ->
                begin match br with
                    | Branch (IntExprp n, _) -> matchPattern env casexp brlist  (* This should not be allowed by the type checker. *)
                    | Branch (Constrp (cname, clist), cexpr) ->
	                    if cname = name then
                            (* 
                             * Associate variables contained in the pattern of the matched branch
                             * with the unevaluated expressions which are turned into thunks.
                             *)
                            let varlist = List.combine (extractFromList clist) tlist in
                            let env1 = List.append env varlist in
                            eval env1 cexpr
                        else 
                            matchPattern env casexp brlist
                    | Branch (Varp vname, vexpr) ->
                        (* A variable always succeeds, i.e., it is an irrefutable pattern. *)
                        eval ((vname, casexp) :: env) vexpr      
                end
            | IntVal n ->
                begin match br with
                    | Branch (IntExprp p, expr) -> 
                        if n = p then
                            eval env expr
                        else 
                            matchPattern env casexp brlist
                    | Branch (Varp p, expr) ->
                        (* A variable always succeeds, i.e., it is an irrefutable pattern. *)
                        let env1 = (p, casexp) :: env in
                        eval env1 expr
                    | Branch (Constrp (_, _), _) -> matchPattern env casexp brlist
                end
            | v -> matchPattern env v brlist
        end
    | [] -> failwith "Unmatched"


(* Test Case (TODO: They should be in a separate file) *)

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
 * case List omega of
 *   List y -> 2
 *   5      -> 1 + 1
 *)
let test8 = 
    eval []
        (Case (Constructor 
                ("List", [((App ( 
                    Abs ("x", App (Var "x", Var "x")), 
                    Abs ("x", App (Var "x", Var "x")))))]), [
            Branch (Constrp ("List", [Varp "y"]), (IntExpr 2));
            Branch (IntExprp 5, BinOp (Add, (IntExpr 1, IntExpr 1)))])
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
