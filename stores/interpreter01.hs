import ASTParser
import Data.List as List
import qualified Data.Map as Map
data Value = NullVal
  | Numeric Int
  | Booleric Bool
  | Proc [ID] AST [VBind]
  deriving (Show)
type StoreRef = Int  
type Store = Map.Map StoreRef Value
newStore :: Store
newStore = Map.empty
newRef :: Store -> StoreRef -> Store
newRef store ref = Map.insert ref NullVal store
setRef :: Store -> StoreRef -> Value -> Store
setRef store ref val = Map.insert ref val store
deRef :: Store -> StoreRef -> Value
deRef store ref =
  let v = Map.lookup ref store
  in case v of Just n -> n
               Nothing -> error "variable not found"
data VBind = VBind ID Value deriving (Show)

b2vb :: Binding -> [VBind] -> Store -> (VBind, Store)
b2vb bind env store =
  case bind of (Bind id (Boolean b)) -> ((VBind id (Booleric b)), store)
	       (Bind id (Number n)) -> ((VBind id (Numeric n)), store)
	       (Bind id (Function formals body)) -> ((VBind id (Proc formals body env)), store)
               (Bind id ast) -> 
		 let (v, store') = eval env store ast
		 in ((VBind id v), store')
evalSeq :: [AST] -> [VBind] -> Store -> (Value, Store)
evalSeq [ast] env store =
  eval env store ast
evalSeq (ast:alist') env store =  
  let (v, store') = eval env store ast
  in
    evalSeq alist' env store'
eval :: [VBind] -> Store -> AST -> (Value, Store)
eval env store ast =
  case ast of (Number n) ->
		((Numeric n), store)
	      (Boolean b) ->
		((Booleric b), store)
	      (Reference id) ->
		(lookupEnv env id, store)
	      (Assume bindings ast) ->
		let (env', store')  = extendEnv env bindings store
		in eval env' store' ast
	      (If i t e) -> evalifexp env store i t e
	      (App ((Reference id): args)) -> apply env store id args
	      (NewRef id) -> 
		let (id', store') = eval env store id
		in
		  (NullVal, newRef store' (valueOfn id'))
	      (SetRef id val) -> 
		let (val', store') = eval env store val
		in
		    let (id', store'') = eval env store' id
		    in  (val', setRef store'' (valueOfn id') val')
	      (DeRef id) ->
		let (id', store') = eval env store id
		in
		  let v = deRef store (valueOfn id')
		  in (v, store')
	      (Sequence alist) ->
		evalSeq alist env store

	      _ -> error "unexpected!"

eval' :: [Binding] -> AST -> Value
eval' env ast =
  let
    store = newStore
  in
    let 
      (env', store') = extendEnv [] env store
    in
      let (v,s) = eval env' store' ast
      in v
evalifexp :: [VBind] -> Store -> AST -> AST -> AST -> (Value, Store)
evalifexp env store ia ta ea =
  let (t, store') = eval env store ia
  in
    case t of (Booleric b) ->
		if b then (eval env store' ta) else (eval env store' ea)
	      _ -> error "Unexpected value!"


valueOfn (Numeric n) = n
valueOfb (Booleric b) = b

numBop :: ID -> Int -> Int -> Value
numBop op v v'
  | op == "+" = Numeric (v + v')
  | op == "-" = Numeric (v - v')
  | op == "*" = Numeric (v * v')
  | op == "/" = Numeric (div v v')


boolBop :: ID -> Bool -> Bool -> Value
boolBop op v v'
  | op == "|" = Booleric (v || v')
  | op == "&" = Booleric (v && v')

boolUop :: ID -> Bool -> Value
boolUop op v
  | op == "~" = Booleric (not v)

numUop :: ID -> Int -> Value
numUop op v
  | op == "zero?" = Booleric $ if v == 0 then True else False

evalOp :: [VBind] -> Store -> ID -> [AST] -> (Value, Store)
evalOp env store op args
  | elem op ["+", "-", "*", "/"] =
      let (v1, store') = eval env store (args!!0)
      in
	let v1' = valueOfn v1
	    (v2, store'') = eval env store' (args!!1)
	in
	    let v2' = valueOfn v2
	    in (numBop op v1' v2', store'')
  | elem op ["|", "&"] = 
      let (v1, store') = eval env store (args!!0)
      in
	let v1' = valueOfb v1
	    (v2, store'') = eval env store' (args!!1)
	in
	    let v2' = valueOfb v2
	    in (boolBop op v1' v2', store'')
  | op == "~" = 
      let (v, store') = eval env store (args!!0)
      in
	  (boolUop op (valueOfb v), store')
  | op == "zero?" = 
      let (v, store') = eval env store (args!!0)
      in
	  (numUop op (valueOfn v), store')
  | otherwise = error "op error."

lookupEnv :: [VBind] -> ID -> Value
lookupEnv env id =
  (\(VBind i v) -> v) $ head $ filter (\(VBind i v) -> i == id) env


-- evaluate each value in the bindings, and return the simplified
-- bindings along with the new store
elaborate :: [Binding] -> [VBind] -> Store -> ([VBind], Store)
elaborate [] env store = (env, store)
elaborate [b] env store = 
  let (vb, store') = b2vb b env store
  in  ([vb], store')
elaborate (b:b') env store = 
  let (vb, store') = b2vb b env store
  in
    let (vb', store'') = elaborate b' env store'
    in ((vb:vb'), store'')


extendEnv :: [VBind] -> [Binding] -> Store -> ([VBind], Store)
extendEnv env binds store =
    -- take a binding, convert it to vbind
    let (vbinds, store') = elaborate binds env store
    in 
      let vb' = List.unionBy (\(VBind i v) (VBind j v') -> i == j) env vbinds
      in (vb', store')

isop :: ID -> Bool
isop id = elem id ["+", "-", "*", "/", "|", "&", "~"]

isufun :: [VBind] -> ID -> Bool
isufun env id =
  case (lookupEnv env id) of
      (Proc i a e) -> True
      _ -> False


applyufun :: [VBind] -> Store -> ID -> [AST] -> (Value, Store)
applyufun env store id args =
  let (Proc formals body senv) = lookupEnv env id
  in
    let minienv = (List.zipWith (\i a -> (Bind i a)) formals args)
    in 
      let (env', store') = extendEnv senv minienv store
      in 
	  eval env' store' body


apply :: [VBind] -> Store -> ID -> [AST] -> (Value, Store)
apply env store id args
  | isop id = evalOp env store id args
  | (isufun env id) = applyufun env store id args
  | otherwise = error "invalid application."


run = ((eval' []) . parseString)
