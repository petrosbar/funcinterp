---------------------------------
-- A call-by-value interpreter 
---------------------------------

module CBVInterpreter where

import qualified Data.Map as Map

type VarName = String
type FunName = String
type ConName = String

-- Data structure for the environment.
-- It contains pairs of String/Value's. 
type Env = Map.Map String Value


-- Binary operator constructors
data OprName = Add | Subtr | Mult
            deriving (Show)

            
-- Expression representation
data Expr = IntExpr Integer
          | Var VarName 
          | Op OprName (Expr, Expr)
          | Call FunName [Expr]
          | Constr ConName [Expr]
          | Case Expr [Branch]
          deriving (Show)

            
data Branch = Branch Pattern Expr 
            deriving (Show)

              
data Pattern = Varp VarName
             | IntValp Integer
             | Constrp ConName [Pattern]
             deriving Show

                
-- A Value is either a function, or a data constructor with all its 
-- arguments evaluated, or an integer value.
data Value = Def FunName [VarName] Expr -- TODO: Should the expression within the function's body be also evaluated?
           | Constructor ConName [Value] 
           | IntVal Integer
           deriving (Show)

           
-- Environment lookup function. If the value associated 
-- with the string is an integer value, then unpack and return it.
-- If it's not, then it must be a function, i.e., a λ-abstraction.
lookupEnv :: Env -> String -> Value
lookupEnv env x = case Map.lookup x env of
    Just (IntVal n) -> IntVal n
    Just func -> func
    Nothing -> error "unbound"

    
-- Insert a list of pairs (bindings) into an existing map.
updateEnv :: Env -> [(String, Value)] -> Env
updateEnv env [] = env
updateEnv env (x:xs) = updateEnv (Map.insert (fst x) (snd x) env) xs


-- Take a list of variables and store their IDs in a list 
extractFromList :: [Pattern] -> [String]
extractFromList (Varp x:exs) = x : extractFromList exs
extractFromList [] = []


-- Evaluate a list of expressions.
exprListEval :: Env -> [Expr] -> [Value]
exprListEval env [] = []
exprListEval env (x:xs) = exprEval env x : exprListEval env xs


-- Binary operators
addv :: Value -> Value -> Value
addv (IntVal x) (IntVal y) = IntVal (x + y)
subtrv :: Value -> Value -> Value
subtrv (IntVal x) (IntVal y) = IntVal (x - y)
multv :: Value -> Value -> Value
multv (IntVal x) (IntVal y) = IntVal (x * y)


-- Pattern match a value against a list of branches and save the
-- pattern that succeeded in the environment.
selectBranch :: Env -> Value -> [Branch] -> (Env, Expr)
selectBranch env c1@(Constructor cname clist) (br:brs) = 
    case br of
        Branch (IntValp _) _ -> selectBranch env c1 brs
        Branch (Constrp pcname plist) expr -> 
            if cname == pcname then
                (updateEnv env $ zip (extractFromList plist) clist, expr) 
            else 
                selectBranch env c1 brs
        Branch p@(Varp vname) expr -> (updateEnv env [(vname, c1)], expr)
selectBranch env c1@(IntVal n) (br:brs) = 
    case br of
        Branch (IntValp p) expr -> 
            if n == p then
                (env, expr)
            else
                selectBranch env c1 brs
        Branch (Varp p) expr ->
            (updateEnv env [(p, c1)], expr)
        _ -> selectBranch env c1 brs
selectBranch env v (br:brs) = selectBranch env v brs
selectBranch env v [] = error "Unmatched"



----- *** Eval function *** -----
---------------------------------
exprEval :: Env -> Expr -> Value
-- Value
exprEval env (IntExpr n) = IntVal n
-- Variable
exprEval env (Var x) = lookupEnv env x
-- Binop
exprEval env (Op oprname (x, y)) = case oprname of
    Add -> addv (exprEval env x) (exprEval env y)
    Subtr -> subtrv (exprEval env x) (exprEval env y)
    Mult -> multv (exprEval env x) (exprEval env y)
-- Function Call
exprEval env (Call fname arglist) = 
    case lookupEnv env fname of
        Def name vname e ->
            let evalarglist = exprListEval env arglist       -- Evaluate the arguments list
                boundvar = zip vname evalarglist             -- Bind variables to the arguments
                newenv = updateEnv env boundvar              -- Store them in the environment
            in exprEval newenv e
        _ -> error "Undefined function"
exprEval env (Constr conname list) = Constructor conname $ exprListEval env list
-- Case expression
exprEval env (Case cexpr brlist) = 
    let evexpr' = exprEval env cexpr
        (env', expr') = selectBranch env evexpr' brlist
    in exprEval env' expr'



------  Test Cases -------

test1 = print $ 
	exprEval (Map.fromList [("x", IntVal 3), ("y", IntVal 4), ("fun1",  Def "fun1" ["ar"] (Op Subtr (Var "ar", Var "y")))])
	(Op Subtr (IntExpr 3, Call "fun1" [IntExpr 10]))

    
test2 = print $ 
	exprEval (Map.fromList [("x", IntVal 3), ("y", IntVal 4), ("fun1",  Def "fun1" ["ar"] (Op Subtr (Var "ar", Var "y")))])
    (Case (IntExpr 2) [
        Branch (Varp "p") (Op Add (Var "p", IntExpr 3)), 
        Branch (IntValp 5) (IntExpr 4)]
    )


-- fun1 ar1 ar2 = ar1 * ar2
-- fun2 ar3 = ar3 + 5
-- test = case fun2 10 of
--            1 -> 1 + 1
--            p -> (fun1 5 6) + p
test3 = print $
    exprEval (Map.fromList [
                    ("fun1", Def "fun1" ["ar1", "ar2"] (Op Mult (Var "ar1", Var "ar2"))), 
                    ("fun2", Def "fun2" ["ar3"] (Op Add (Var "ar3", IntExpr 5)))
             ])
            (Case (Constr "Cons1" [IntExpr 1])[
                Branch (IntValp 1) (Op Add (IntExpr 1, IntExpr 1)),
                Branch (IntValp 2) (Op Add (Call "fun1" [IntExpr 5, IntExpr 6], Var "p")),
                Branch (Varp "p") (Constr "Cons1" [Var "p", IntExpr 3])]
            )

test4 = print $
    exprEval (Map.fromList [
                    ("fun1", Def "fun1" ["ar1", "ar2"] (Op Mult (Var "ar1", Var "ar2"))), 
                    ("fun2", Def "fun2" ["ar3"] (Op Add (Var "ar3", IntExpr 5)))
             ])
            (Constr "Cons1" [IntExpr 1, Call "fun1" [IntExpr 2, IntExpr 3]])

    
test5 = print $
    exprEval (Map.fromList [
                ("fun1", Def "fun1" ["ar1", "ar2"] (Op Mult (Var "ar1", Var "ar2"))), 
                ("fun2", Def "fun2" ["ar3"] (Op Add (Var "ar3", IntExpr 5)))])
                (Case (Call "fun2" [IntExpr 10]) [
                    Branch (IntValp 15) (Op Add (IntExpr 1, IntExpr 1)),
                    Branch (Constrp "cp" [Varp "x", Varp "y", Varp "z"]) (IntExpr 5)]
                )

test6 = print $
    exprEval (Map.fromList [
                ("head", Def "head" ["list1"] 
                    (Case (Constr "List" [IntExpr 3, Constr "List" [IntExpr 2]]) [
                        Branch (IntValp 15) (Op Add (IntExpr 1, IntExpr 1)),
                        Branch (Constrp "List" [Varp "x", Varp "y"]) (Var "x")]
                    )
                )
            ]) 
            (Call "head" []) 


-- head $ Cons 5 (Cons 2 (Cons 6 Nil))
myHead = print $
    exprEval (Map.fromList [
                ("head", Def "head" ["list1"] 
                    (Case (Var "list1") [
                        Branch (IntValp 15) (Op Add (IntExpr 1, IntExpr 1)),
                        Branch (Constrp "List" [Varp "x", Varp "y"]) (Var "x")]
                    )
                )
            ]) 
            (Call "head" [Constr "List" [IntExpr 5, Constr "List" [IntExpr 2, Constr "List" [IntExpr 6]]]]) 
