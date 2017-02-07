(*
 * An attempt to transform our call-by-name interpreter into CPS. 
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


(* val extractFromList : pattern list -> (name list -> name list) -> name list *)
let rec extractFromList xlist k = match xlist with
    | (Varp x::xs) -> extractFromList xs (fun a -> x :: a)
    | _            -> k []


(* val listOfThunks : env -> expr list -> (value list -> value list) -> value list *)
let rec listOfThunks env exprlist k = match exprlist with
    | (x::xs) -> listOfThunks env xs (fun a -> (Thunk ((Env env), "_", x)) :: a) 
    | []      -> k []


(* val combine : 'a list -> 'b list -> (('a * 'b) list -> ('a * 'b) list) -> ('a * 'b) list *)
let rec combine x y k = match (x, y) with
    | (x::xs, y::ys) -> combine xs ys (fun a -> (x, y) :: a)
    | ([], [])       -> k []
    | (_, _)         -> k (failwith "Length of lists not equal")


(* val append : 'a list list -> 'a list list -> ('a list -> 'a list list) -> 'a list list *)
let rec append l1 l2 k = match l1 with
    | (x::xs) -> append xs l2 (fun a -> k (x :: a))
    | []      -> k l2


(* val eval : env -> expr -> (value -> value) -> value *)
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


(* val listEval : env -> expr list -> (value list -> value list) -> value list *)
and listEval env exprlist k =
    match exprlist with
        | []      -> k []
        | (x::xs) -> listEval env xs (fun a -> eval env x id :: a)


(* val binOp : operator -> value -> value -> (value -> value) -> value *)
and binOp oprtr op1 op2 k = 
    begin match (op1, op2) with
        | (IntVal n, IntVal m) ->
            begin match oprtr with
                | Add   -> k (IntVal (n + m))
                | Subtr -> k (IntVal (n - m))
                | Mult  -> k (IntVal (n * m))
            end
    end


(* val matchPattern : env -> expr -> branch list -> (value -> value) -> value *)
and matchPattern env casexp blist k = match blist with
    | br::brlist ->
        begin match br with
            | Branch (IntExprp n, pexp) ->
                let evex = eval env casexp k in
                begin match evex with
                    | IntVal m -> 
                        if n = m then
                            eval env pexp k
                        else
                            matchPattern env casexp brlist k
                    | _ -> matchPattern env casexp brlist k
                end
            | Branch (Constrp (pname, plist), cexpr) ->
                begin match casexp with
                    | Constructor (cname, clist) ->
                        if pname = cname then
                            let thunklist = listOfThunks env clist id in
                            let env' = combine (extractFromList plist id) thunklist id in
                            eval (append env env' id) cexpr k
                        else
                            matchPattern env casexp brlist k
                    | App (ex1, ex2) -> 
                        begin match  ex1 with
                            | Abs (str, expr1) -> 
                                let expr2 = (str, Thunk (Env [], "_", ex2)) in
                                matchPattern (expr2::env) expr1 blist k
                            | _ -> k (failwith "Invalid case expression")
                        end
                    | _ -> matchPattern env casexp brlist k
                end
            | Branch (Varp x, vexp) ->
                let thunk = Thunk ((Env env), "_", casexp) in 
                let env' = (x, thunk) :: env in
                    eval env' vexp k
        end
    | [] -> k (failwith "Unmatched")

