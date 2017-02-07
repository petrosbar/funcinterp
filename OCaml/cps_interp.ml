(*
 * Our call-by-name interpreter transformed into CPS. 
 * For completeness, we wrote our own versions of List.append and List.combine so that they too follow
 * the style of the rest of the program.
 *
 * Every function is written so that it takes an extra argument, its continuation, in which the function's result is
 * passed. In addition, we converted all recursive functions to tail recursive.
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


(*
 * The identity function.
 *)
(* val id : 'a -> 'a *)
let id x = x


(* val : extractFromList : pattern list -> string list *)
let rec extractFromList xlist k = match xlist with
    | (Varp x::xs) -> extractFromList xs (fun a -> x :: a)
    | _            -> k []


let rec listOfThunks env exprlist k = match exprlist with
    | (x::xs) -> listOfThunks env xs (fun a -> (Thunk ((Env env), "_", x)) :: a) 
    | []      -> k []


let rec eval env expr k =
  begin match expr with
    | IntExpr n -> k (IntVal n)
    | Var x -> 
        begin match List.assoc x env with
            | IntVal n as intv -> k intv
            | ConstrVal (name, explist) as const -> k const
            | Thunk (Env env, str, expr) -> eval env expr k
        end
    | BinOp (operator, (op1, op2)) ->
        let kont = (fun x -> eval env op2 (fun y -> binOp operator x y k)) in
        eval env op1 kont
    | Abs (n, ex) -> k (Thunk ((Env env), n, ex))
    | App (ex1, ex2) ->
        begin match eval env ex1 k with
            | Thunk (Env en, n, ex) ->
                let thunk = Thunk ((Env env), "_", ex2)
                in eval ((n, thunk) :: en) ex k
            | _ -> k (failwith "Invalid function application")
        end
    | Constructor (cname, explist) ->
        let vallist = listEval env explist id
        in k (ConstrVal (cname, vallist))
    | Case (ex, (brlist)) ->
        matchPattern env ex brlist k
  end


and listEval env exprlist k =
    match exprlist with
        | []      -> k []
        | (x::xs) -> listEval env xs (fun a -> eval env x id :: a)


and binOp oprtr op1 op2 k = 
    begin match (op1, op2) with
        | (IntVal n, IntVal m) ->
            begin match oprtr with
                | Add   -> k (IntVal (n + m))
                | Subtr -> k (IntVal (n - m))
                | Mult  -> k (IntVal (n * m))
            end
    end

and matchPattern env casexp blist k = match blist with
    | br::brlist ->
        begin match br with
            | Branch (IntExprp n, pexp) ->
                (* If pattern is an integer value then we're forced to evaluate case's argument eagerly. *)
                let evex = eval env casexp k in
                begin match evex with
                    | IntVal m -> 
                        if n = m then
                            (* If match succeeded, evaluate the associated expression. *)
                            eval env pexp k
                        else
                            (* Otherwise, move to the next branch. *)
                            matchPattern env casexp brlist k
                    (* Likewise, if the evaluated expression isn't an integer, then move to the next branch. *)
                    | _ -> matchPattern env casexp brlist k
                end
            (* Pattern is a constructor. *)
            | Branch (Constrp (pname, plist), cexpr) ->
                begin match casexp with
                    (* 
                     * If case's argument is a constructor and its name equals that of the pattern,
                     * insert its arguments in a list of thunks, append the list to env 
                     * and evaluate the associated expression.
                     *)
                    | Constructor (cname, clist) ->
                        if pname = cname then
                            let thunklist = listOfThunks env clist id in
                            let env' = List.combine (extractFromList plist id) thunklist in
                            eval (List.append env env') cexpr k
                        else
                            matchPattern env casexp brlist k
                    (*
                     * If it's an application, then make the operator part a thunk
                     * and call matchPattern again, but this time its argument is the body of 
                     * the operand (if it's an abstraction) itself.
                     * This way, we bring the first argument into weak head normal form.
                     *)
                    | App (ex1, ex2) -> 
                        begin match  ex1 with
                            | Abs (str, expr1) -> 
                                let expr2 = (str, Thunk (Env [], "_", ex2)) in
                                matchPattern (expr2::env) expr1 blist k
                            | _ -> k (failwith "Invalid case expression")
                        end
                    | _ -> matchPattern env casexp brlist k
                end
            (* Pattern is a variable, thus, matching is irrefutable. *)
            | Branch (Varp x, vexp) ->
                let thunk = Thunk ((Env env), "_", casexp) in 
                let env' = (x, thunk) :: env in
                    eval env' vexp k
        end
    | [] -> k (failwith "Unmatched")



(* 4 + 2 *)
let test1 = 
    eval [] (BinOp (Add, (IntExpr 4, IntExpr 2))) id

(* λx.1 + 2 *)
let test2 = 
    eval [] (Abs ("x", (BinOp (Add, (IntExpr 1, IntExpr 2))))) id

(* λx.x + 2 *)
let test3 = 
    eval [("x", IntVal 2)] (Abs ("x", (BinOp (Add, (Var "x", IntExpr 2))))) id

(* (λx.x + 2) 10 *)
let test4 = 
    eval [("y", IntVal 2)] 
        (App  (Abs ("x", BinOp (Add, (Var "x", IntExpr 2))), IntExpr 10)) id


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
        ) id

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
        ) id

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
        ) id

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
        ) id
            

(* 
 * case (λx.Cons1[x]) Ω of
 *   Cons1[y] -> y
 *)
let test11 = 
    eval []
        (Case (App (Abs ("x", (Constructor ("Cons1", [Var "x"]))), (App 
                (Abs ("x", App (Var "x", Var "x")), 
                 Abs ("x", App (Var "x", Var "x"))))), [
            Branch (Constrp ("Cons1", [Varp "y"]), (IntExpr 1))])) id
 
