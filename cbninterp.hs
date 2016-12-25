---------------------------------------------------------------------------------------------------------
-- A monadic, higher-order, call-by-name interpreter based on [1] 
-- extended with case expressions.
--
-- [1] Monad Transformers Step by Step
-- [https://page.mi.fu-berlin.de/scravy/realworldhaskell/materialien/monad-transformers-step-by-step.pdf]
---------------------------------------------------------------------------------------------------------

module CBNMonadicInterp where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Maybe

type Name = String
 
type Env = Map.Map Name Expr

-- The result type of the eval function defined with monad transformers.
type Eval a = ReaderT Env (ExceptT String Identity) a

-- Binary operator constructors.
data OprName = Add | Subtr | Mult
             deriving Show

            
-- Expression representation
data Expr = IntExpr Integer
          | Var Name 
          | BinOp OprName (Expr, Expr)
          | Constr Name [Expr]
          | Case Expr [Branch]
          | Abs Name Expr
          | App Expr Expr
          | Thunk Env Name Expr
          deriving Show


-- Branch type consisting of a pattern and an associated 
-- expression which is evaluated in case pattern matches.          
data Branch = Branch Pattern Expr 
            deriving Show


-- A pattern is an expression that is an integer literal (constant), a variable, or a constructor. 
data Pattern = IntExprp Integer
             | Varp Name
             | Constrp Name [Pattern]
             deriving Show


---------- Helper functions ------------

-- Binary operators.
binOp :: OprName -> Expr -> Expr -> Integer
binOp opr (IntExpr x) (IntExpr y) = 
    case opr of
        Add   -> x + y
        Subtr -> x - y
        Mult  -> x * y


-- Insert a list of pairs (bindings) into an existing env.
updateEnv :: Env -> [(String, Expr)] -> Env
updateEnv env [] = env
updateEnv env (x:xs) = updateEnv (Map.insert (fst x) (snd x) env) xs


-- Take a list of variables and store their IDs in a list 
extractFromList :: [Pattern] -> [String]
extractFromList (Varp x:exs) = x : extractFromList exs
extractFromList [] = []


-- Evaluate the expression from the first branch whose pattern matches the 
-- case argument expression. If such a branch does not exist throw an error.
selectBranch :: Expr -> [Branch] -> Eval Expr
selectBranch c1@(Constr cname clist) (br:brs) = do
    env <- ask
    case br of
        Branch (IntExprp _) _ -> selectBranch c1 brs
        Branch (Constrp pcname plist) expr 
            | cname == pcname -> 
                let varlist = zip (extractFromList plist) clist
                    env' = const $ updateEnv env varlist
                in local env' (eval expr)
            | otherwise       -> 
                selectBranch c1 brs
        Branch p@(Varp vname) expr -> 
            local (const (updateEnv env [(vname, c1)])) (eval expr)
selectBranch c1@(IntExpr n) (br:brs) = do
    env <- ask
    case br of
        Branch (IntExprp p) expr 
            | n == p -> eval expr
            | otherwise -> selectBranch c1 brs
        Branch (Varp p) expr ->
            let env' = const $ updateEnv env [(p, c1)]
            in local env' (eval expr) 
        _ -> selectBranch c1 brs
selectBranch v (br:brs) = selectBranch v brs
selectBranch v [] = error "Unmatched"


-------------------- Eval function ---------------------------
--------------------------------------------------------------
eval :: Expr -> Eval Expr
-- Integer expression
eval (IntExpr n) = return $ IntExpr n
-- Variables now hold expressions, not just values. 
-- Thus, always evaluate the content of a variable.
eval (Var n) = do
    env <- ask
    case Map.lookup n env of
        Nothing -> throwError $ "Unbound Variable" ++ n
        Just val -> eval val
-- Binary operators
eval (BinOp operator (x, y)) = do
    e1 <- eval x
    e2 <- eval y
    case (e1, e2) of
        (IntExpr i, IntExpr j) ->         
            return $ IntExpr (binOp operator e1 e2)
        _ -> throwError "Invalid operands in binop"
-- Constructors. Do not change anything. 
eval (Constr cname exlist) = return $ Constr cname exlist
-- Abstractions. Return a thunk.
eval (Abs n e) = do
    env <- ask
    return $ Thunk env n e
-- Function application.
eval (App e1 e2) = do 
    val1 <- eval e1
    case val1 of
        Thunk env' n fbody -> 
            local (const (Map.insert n e2 env')) (eval fbody)
        _ -> throwError "Invalid function application"
-- Case expressions.
eval (Case expr brlist) = do
    evexpr' <- eval expr
    selectBranch evexpr' brlist


runEval :: Env -> Eval a -> Either String a
runEval env ev = runIdentity (runExceptT (runReaderT ev env))


----------- Test Cases -----------

-- (λx.λy.x + y) 2 10
test = runEval Map.empty
    (eval 
        (App
            (App        
                (Abs "x" 
                    (Abs "y" 
                        (BinOp Add (Var "x", Var "y")))) (IntExpr 2)) (IntExpr 10)))


-- x + y                        
test1 = runEval (Map.fromList [("x", IntExpr 1), ("y", IntExpr 2)])
    (eval
        (BinOp Add (Var "x", Var "y")))


-- λx.x+3
test2 = runEval (Map.fromList [])
    (eval  
        (Abs "x" 
            (BinOp Add (Var "x", (IntExpr 3)))))


-- (λx.λy.x+y) 2 bot
test3 = runEval (Map.fromList [])
    (eval 
        (App      
            (App
                (Abs "x" 
                    (Abs "y" 
                        (BinOp Add (Var "x", Var "y")))) (IntExpr 2)) (undefined)))


-- (λx.λy.x+1) 2 bot
test4 = runEval (Map.fromList [])
    (eval
        (App      
            (App
                (Abs "x" 
                    (Abs "y" 
                        (BinOp Add (Var "x", IntExpr 1)))) (IntExpr 2)) (undefined)))


-- case λx.x 5 of 
--   5          -> 1 + 1
--   List(x, y) -> x
test5 = runEval (Map.fromList []) 
    (eval  
        (Case (App (Abs "x" (Var "x")) (IntExpr 5)) [
            Branch (IntExprp 5) (BinOp Add (IntExpr 1, IntExpr 1)),
            Branch (Constrp "List" [Varp "x", Varp "y"]) (Var "x")]
        )
    )


-- case List(λx.x 5) of
--   List(y) -> y
--   5       -> 1 + 1
test6 = runEval (Map.fromList [])
    (eval 
        (Case (Constr "List" [(App (Abs "x" (Var "x")) (IntExpr 5))]) [
            Branch (Constrp "List" [Varp "y"]) (Var "y"),
            Branch (IntExprp 5) (BinOp Add (IntExpr 1, IntExpr 1))]
        )
    )


-- case List(λx.x bot) of
--   List(y) -> 1
--   5       -> 1 + 1
test7 = runEval (Map.fromList []) 
    (eval  
        (Case (Constr "List" [(App (Abs "x" (Var "x")) (undefined))]) [
            Branch (Constrp "List" [Varp "y"]) (IntExpr 1),
            Branch (IntExprp 5) (BinOp Add (IntExpr 1, IntExpr 1))]
        )
    )


-- case List(bot) of
--   List(y) -> 2
--   5       -> 
test8 = runEval (Map.fromList [])
    (eval 
        (Case (Constr "List" [(undefined)]) [
            Branch (Constrp "List" [Varp "y"]) (IntExpr 2),
            Branch (IntExprp 5) (BinOp Add (IntExpr 1, IntExpr 1))]
        )
    )


-- case List(λx.x 5) of
--   List(y) -> y
--   5       -> 1 + 1
test9 = runEval (Map.fromList [])
    (eval 
        (Case (Constr "List" [(App (Abs "x" (Var "x")) (IntExpr 5))]) [
            Branch (Constrp "List" [Varp "y"]) (Var "y"),
            Branch (IntExprp 5) (BinOp Add (IntExpr 1, IntExpr 1))]
        )
    )


-- case List(λx.x 5) of
--   List(y) -> d + 4
--   5       -> 1 + 1
test10 = runEval (Map.fromList [("d", IntExpr 3)])
    (eval 
        (Case (Constr "List" [(App (Abs "x" (Var "x")) (IntExpr 5))]) [
            Branch (Constrp "List" [Varp "y"]) (BinOp Add (Var "d", IntExpr 4)),
            Branch (IntExprp 5) (BinOp Add (IntExpr 1, IntExpr 1))]
        )
    )


-- 4 + ((λx.x + 3) 2)
test11 = runEval (Map.fromList [])
    (eval 
        (BinOp Add (IntExpr 4, 
            App
                (Abs "x" 
                    (BinOp Add (Var "x", (IntExpr 3)))) (IntExpr 2)
            )
        )
    )


-- case List(λx.x 5) of
--   List(y) -> λz.z 0
--   5       -> 1 + 1           
test12 = runEval (Map.fromList [("d", IntExpr 3)])
    (eval 
        (Case (Constr "List" [(App (Abs "x" (Var "x")) (IntExpr 5))]) [
            Branch (Constrp "List" [Varp "y"]) (App (Abs "z" (Var "z")) (IntExpr 0)),
            Branch (IntExprp 5) (BinOp Add (IntExpr 1, IntExpr 1))]
        )
    )
