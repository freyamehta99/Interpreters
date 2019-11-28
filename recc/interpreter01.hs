import ASTParser
import Data.Char
import Data.List as List
import qualified Data.Map as M
import Data.Maybe
import Data.Array
import Data.List.Split
import Debug.Trace

data Value =
    Numeric Int
  | Booleric Bool
  | Proc [ID] AST Environment
  | RecProc [ID] AST Environment deriving (Show)

type Environment = M.Map ID Value

evaluate :: Environment -> AST -> Value
evaluate env  ast =
  case ast of (Number n) -> (Numeric n)
	      (Boolean b) -> (Booleric b)
	      (Reference id) -> lookFor env id
	      (Assume bindings ast) -> evaluate (extendEnv env  bindings)  ast
	      (If i t e) -> evalITE env  i t e
	      (App alist) ->  evalApp env  alist
	      (RecFun fbinds app) ->  let alp = extendFuncEnv env fbinds
				      in evaluate alp app
              (Function params ast) -> (Proc params ast env)
	      
lookFor :: Environment -> ID -> Value
lookFor env id = case v of
    Just x ->  x
    Nothing  -> error $ "id " ++ id ++ " not set!" ++ "in environment" ++ (show env) ++" \n"
  where v = M.lookup id env

extendEnv :: Environment ->[Binding] -> Environment
extendEnv env =   M.fromList . map f
  where f (Bind id tree) = (id, evaluate env tree)

extendFuncEnv:: Environment ->[FBind]->Environment
extendFuncEnv env  =  M.fromList . map f
  where f (FBind id formals body) = (id, RecProc formals body env)

evalOp :: Environment -> ID -> [AST] -> Value
evalOp env  op args
  | elem op ["+", "-", "*", "/"] = applyNumBinOp env  op (args!!0) (args!!1)
  | elem op ["|", "&"] = applyBoolBinOp env  op (args!!0) (args!!1)
  | op == "~" = applyBoolUnOp env  op (args!!0)
  | op == "=" = applyNumBinOp env  op (args!!0) (args!!1)
  | op == "zero?" = applyNumUnOp env  op (args!!0)
  | otherwise = error "Operator Not Found!"

evalApp :: Environment ->  [AST] -> Value
evalApp env  ((Reference id):args) =
  if elem id ["+", "-", "*", "/", "|", "&", "~", "zero?","="] then
    evalOp env id args
  else
    let applicable = lookFor env id
    in
      --applicable
      case applicable of 
	(Proc ids ast savedEnv) ->
			   let
			     
			     alpha =  (List.zipWith (\i a -> (Bind i a)) ids args)  
			     gamma = (M.union (extendEnv savedEnv alpha) env) -- bindings for formals
			   in
			     evaluate gamma ast 
        (RecProc ids ast savedEnv) ->
			   let
			     alpha =  [FBind id ids ast]
			     beta = (List.zipWith (\i a -> (Bind i a)) ids args) 
			     delta = (extendFuncEnv savedEnv alpha)
	                     zetta = (extendEnv env beta)
			     gamma = M.union  delta zetta  -- bindings for formals
			   in
			     evaluate gamma ast 
     			     
      	_ -> error "Error"

evalITE :: Environment -> AST -> AST -> AST -> Value
evalITE env  ia ta ea =
  let t = evaluate env  ia
  in
    case t of (Booleric b) ->
		if  b then  (evaluate env ta) else (evaluate env  ea)
	      _ -> error "Unexpected value!"

gnum ast =
  case ast of (Numeric n) -> n
              _ -> error (show ast)

applyNumBinOp :: Environment -> ID -> AST -> AST -> Value
applyNumBinOp env  op a a'
  | op == "+" = Numeric ( ((gnum . (evaluate env )) a) + ((gnum . (evaluate env )) a') )
  | op == "-" = Numeric ( ((gnum . (evaluate env )) a) - ((gnum . (evaluate env )) a') )
  | op == "*" = Numeric ( ((gnum . (evaluate env )) a) * ((gnum . (evaluate env )) a') )
  | op == "/" = Numeric ( div ((gnum . (evaluate env )) a) ((gnum . (evaluate env )) a') )
  | op == "=" = Booleric ( ((gnum . (evaluate env )) a) == ((gnum . (evaluate env )) a') )

gbool ast =
  case ast of (Booleric n) -> n
              _ -> error (show ast)

applyBoolBinOp :: Environment -> ID -> AST -> AST -> Value
applyBoolBinOp env  op a a'
  | op == "|" = Booleric ( ((gbool . (evaluate env )) a) || ((gbool . (evaluate env )) a') )
  | op == "&" = Booleric ( ((gbool . (evaluate env )) a) && ((gbool . (evaluate env )) a') )

applyBoolUnOp :: Environment -> ID -> AST -> Value
applyBoolUnOp env  op a
  | op == "~" = Booleric (not ((gbool . (evaluate env )) a))

applyNumUnOp :: Environment -> ID -> AST -> Value
applyNumUnOp env  op a
  | op == "zero?" = Booleric $ if ((gnum . (evaluate env )) a) == 0 then True else False


run = (evaluate M.empty . parseString)

sample1 = "(+ 3 4)"
sample2 = "(assume ((x 3)) (+ x x))"
sample3 = "(if True 3 4)"  
sample4 = "(assume ((f (function (a) (+ a 2)))) (f 7))"
sample5 = "(assume ((x (+ 1 2)) . (y 3)) (+ x y))"
sample6 = "(recfun ((isEven (x) (if (= 0 x) True (isOdd (- x 1)))) . (isOdd (x) ( if(= 1 x) False (isEven (- x 1))))) (isEven 3))"
sample7 = "(recfun ((isEven (x) (if (= 0 x) True (isEven (- x 1))))) (isEven 2))"
main :: IO ()
main = (putStrLn . show . run) sample6
