-- import ASTParser
import Data.Char
import Data.List
import qualified Data.Map
import Data.Maybe
import Data.Array
import Data.List.Split

data Value = IntVal Integer | BoolVal Bool

instance Show Value where
   show (IntVal int) = show int
   show (BoolVal bool) = show bool

type Ident = String

data BinOp = Add | Sub | Mul | Div | And | Or deriving
    (Show, Eq)

data UnOp = Not | IsZero deriving (Show, Eq)

data Token = TokBinOp BinOp
           | TokUnOp UnOp
           | TokLParen
           | TokRParen
           | TokNum Integer
           | TokBool Bool
           | TokIdent Ident
           | TokAssume
           | TokIF
    deriving (Show, Eq)

binoperator :: String -> BinOp
binoperator c | c == "+" = Add
           | c == "-" = Sub
           | c == "*" = Mul
           | c == "/" = Div
           | c == "&" = And
           | c == "|" = Or

unoperator :: String -> UnOp
unoperator c | c == "zero?" = IsZero
             | c == "~" = Not

repl :: String -> String -> String -> String 
repl old new = intercalate new . splitOn old

arranize :: String -> [String]
arranize "" = []
arranize str =  words (repl "(" " ( " (repl ")" " ) " (repl "[" " [ " (repl "]" " ] " str))))

tokenize :: [String] -> [Token]
tokenize [] = []
tokenize (c : cs) 
    | elem c  ["+","-","*","/","&","|"] = TokBinOp (binoperator c) : tokenize cs
    | elem c ["zero?", "~"] = TokUnOp (unoperator c) : tokenize cs 
    | c == "("  = TokLParen : tokenize cs
    | c == ")"  = TokRParen : tokenize cs
    | all isDigit c = TokNum (read c::Integer)  : tokenize cs
    | elem c ["True","False"] = TokBool (read c::Bool) : tokenize cs
    | c == "assume" = TokAssume : tokenize cs
    | c == "if" = TokIF : tokenize cs
    | all isAlpha c = TokIdent (c::Ident)  : tokenize cs
    | c == " " = tokenize cs
    | otherwise = error $ "Cannot tokenize" ++ c

data Tree =       
           BinExp BinOp Tree Tree
          | UnExp UnOp Tree
          | NumExp Integer
          | IdentExp Ident
          | BoolExp Bool
          | AssumeExp [Binding] Tree 
          | IFExp Tree Tree Tree
          | Empty             
    deriving Show

data Binding = Bind Ident Tree
               deriving Show

type Environment = Data.Map.Map Ident Value

bindsequencer :: [Token] -> [Binding]
bindsequencer [] = []
bindsequencer (token : token_list) =
              case token of
                   TokLParen ->  bindsequencer token_list
                   TokRParen ->  bindsequencer token_list
                   TokIdent id -> Bind id (parser [head token_list]) : bindsequencer (tail token_list)

parenPairs :: [Token] -> [(Int, Int)]
parenPairs = go 0 []
  where
    go _ _ [] = []
    go j acc (TokLParen : cs) = go (j + 1) (j : acc) cs
    go j (i : is) (TokRParen : cs) = (i, j) : go (j + 1) is cs
    go j acc (c : cs) = go (j + 1) acc cs

bindendindex :: [Token]->Int
bindendindex [] = error "unbalanced parentheses!"
bindendindex token_list = fromMaybe 0 (Data.Map.lookup 0 (Data.Map.fromList  (parenPairs token_list)))

parser :: [Token] -> Tree
parser [] = Empty
parser (token : token_list) =
        case token of 
                TokLParen ->  parser token_list
                TokRParen ->  parser token_list
                TokBinOp binop -> BinExp binop (parser [head token_list]) (parser (tail token_list))
                TokAssume -> AssumeExp  (bindsequencer firstlist) (parser secondlist)
                TokIF ->  IFExp (parser firstlist) (parser thirdlist) (parser fourthlist)
                TokUnOp unop -> UnExp unop (parser token_list)
                TokNum int -> NumExp int 
                TokBool bool -> BoolExp bool
                TokIdent id -> IdentExp id
        where idx = bindendindex token_list
              firstlist = take (idx+1) $ token_list
              secondlist = drop (idx+1) $ token_list
              idx' = bindendindex secondlist
              thirdlist = take idx' $ secondlist
              fourthlist = drop idx' $ secondlist

-- data ParseTree =
--     LBracket
--   | RBracket                             
--   | Operator Op                          
--   | Numeric Int                          
--   | Booleric Bool                        
--   | Symbol Ident                         
--   | IfKeyw                               
--   | AssumeKeyw                           
--   | BindAppl ParseTree ParseTree
--   | BindSeq [ParseTree]
--   | Appl Op [ParseTree]                  
--   | IfAppl ParseTree ParseTree ParseTree 
--   | AssumeAppl ParseTree ParseTree     
--   deriving (Show)

-- toAST :: ParseTree -> Tree
-- toAST (Numeric a) = NumExp a
-- toAST (Symbol a) = IdentExp a
-- toAST (Booleric b) = BoolExp b
-- toAST (BindAppl (Symbol id) b) = Binding id (toAST b)
-- toAST (AssumeAppl (BindSeq ls) c) = AssumeExp (BindExp (map toAST ls) (toAST c))
-- toAST (Appl Add ls) = BinExp Add (toAST (ls !! 0)) (toAST (ls !! 1))
-- toAST (Appl Sub ls) = BinExp Sub (toAST (ls !! 0)) (toAST (ls !! 1))
-- toAST (Appl Mul ls) = BinExp Mul (toAST (ls !! 0)) (toAST (ls !! 1))
-- toAST (Appl Div ls) = BinExp Div (toAST (ls !! 0)) (toAST (ls !! 1))
-- toAST (Appl And ls) = BinExp And (toAST (ls !! 0)) (toAST (ls !! 1))
-- toAST (Appl Or ls) = BinExp Or (toAST (ls !! 0)) (toAST (ls !! 1))
-- toAST (Appl Not ls) = UnExp Not (toAST (ls !! 0))
-- toAST (Appl IsZero ls) = UnExp IsZero (toAST (ls !! 0))
-- toAST _ = error "not part of parsing"


valuetoint:: Value -> Integer
valuetoint v = case v of 
                  IntVal i -> i

valuetobool:: Value -> Bool
valuetobool v = case v of 
                    BoolVal b -> b

getvalue :: Environment -> Ident -> Value
getvalue environ id = case v of
    Just x -> x
    Nothing  -> error $ "id " ++ id ++ " not set!"
  where v = Data.Map.lookup id environ

expandenviron :: Environment -> [Binding] -> Environment
expandenviron environ =  Data.Map.fromList . map f
  where f (Bind id tree) = (id, eval environ tree)

eval :: Environment -> Tree -> Value
eval environ (NumExp x) = IntVal x
eval environ (BoolExp x) = BoolVal x
eval environ (IdentExp x) = getvalue environ x

eval environ (BinExp op lefttree righttree) = 
    let left = eval environ lefttree
        right = eval environ righttree
    in  case op of
          Add -> IntVal ((valuetoint left) + (valuetoint right))
          Sub -> IntVal ((valuetoint left) - (valuetoint right))
          Mul -> IntVal ((valuetoint left) * (valuetoint right))
          Div -> IntVal (quot (valuetoint left) (valuetoint right))
          And -> BoolVal ((valuetobool left) && (valuetobool right))
          Or -> BoolVal ((valuetobool left) || (valuetobool right))

eval environ (UnExp op tree) =
    let x = eval environ tree 
    in case op of
         Not  -> if ((valuetobool x)) then (BoolVal False) else (BoolVal True)
         IsZero  -> if ((valuetoint x)==0) then (BoolVal True) else (BoolVal False)

eval environ (IFExp conditionpart thenpart elsepart) =
         if (valuetobool (eval environ conditionpart)) then (eval environ thenpart) else (eval environ elsepart)

eval environ (AssumeExp bindings boundedexp) = eval environ' boundedexp
  where environ' = Data.Map.union p environ
        p = expandenviron environ bindings

run :: String -> Value
run str = ((eval $ Data.Map.empty) ( parser (tokenize (arranize str) )))