
import Data.Char
import Data.List
import qualified Data.Map
import Data.Maybe
import Data.Array
import Data.List.Split

data Value = IntVal Integer | BoolVal Bool

-- data Value = IntVal Integer |
--              BoolVal Bool
--              deriving Show

instance Show Value where
   show (IntVal int) = show int
   show (BoolVal bool) = show bool

type ID = String

data BinOp = Plus | Minus | Times | Div | Eqv | And | Or deriving
    (Show, Eq)

data UnOp = Not | IsZero deriving (Show, Eq)

data Token = TokBinOp BinOp
           | TokUnOp UnOp
           | TokLParen
           | TokRParen
           | TokSLParen
           | TokSRParen
           | TokNum Integer
           | TokBool Bool
           | TokID ID
           | TokAssume
           | TokIF
    deriving (Show, Eq)

binoperator :: String -> BinOp
binoperator c | c == "+" = Plus
           | c == "-" = Minus
           | c == "*" = Times
           | c == "/" = Div
           | c == "=" = Eqv
           | c == "&" = And
           | c == "|" = Or

unoperator :: String -> UnOp
unoperator c | c == "zero?" = IsZero
             | c == "~" = Not

replacefun :: String -> String -> String -> String 
replacefun old new = intercalate new . splitOn old

arranize :: String -> [String]
arranize "" = []
arranize str =  words (replacefun "(" " ( " (replacefun ")" " ) " (replacefun "[" " [ " (replacefun "]" " ] " str))))

tokenize :: [String] -> [Token]
tokenize [] = []
tokenize (c : cs) 
    | elem c  ["+","-","*","/","&","|"] = TokBinOp (binoperator c) : tokenize cs
    | elem c ["zero?", "~"] = TokUnOp (unoperator c) : tokenize cs 
    | c == "("  = TokLParen : tokenize cs
    | c == ")"  = TokRParen : tokenize cs
    | c == "["  = TokSLParen : tokenize cs
    | c == "]"  = TokSRParen : tokenize cs
    | all isDigit c = TokNum (read c::Integer)  : tokenize cs
    | elem c ["True","False"] = TokBool (read c::Bool) : tokenize cs
    | c == "assume" = TokAssume : tokenize cs
    | c == "if" = TokIF : tokenize cs
    | all isAlpha c = TokID (c::ID)  : tokenize cs
    | c == " " = tokenize cs
    | otherwise = error $ "Cannot tokenize" ++ c

data Tree =       
           BinExp BinOp Tree Tree
          | UnExp UnOp Tree
          | NumExp Integer
          | IdentExp ID
          | BoolExp Bool
          | BindExp [Binding] Tree
          | AssumeExp Tree 
          | IFExp Tree Tree Tree
          | Empty
                
    deriving Show

data Binding = Bind ID Tree
               deriving Show

type Environment = Data.Map.Map ID Value

getvalue :: Environment -> ID -> Value
getvalue env id = case v of
    Just x -> x
    Nothing  -> error $ "id " ++ id ++ " not set!"
  where v = Data.Map.lookup id env

envexpand :: Environment -> [Binding] -> Environment
envexpand env =  Data.Map.fromList . map f
  where f (Bind id tree) = (id, eval env tree)

bindsequencer :: [Token] -> [Binding]
bindsequencer [] = []
bindsequencer (token : token_list) =
              case token of
                   TokID id -> Bind id (parser [head token_list]) : bindsequencer (tail token_list)
                   TokLParen -> bindsequencer token_list
                   TokRParen -> bindsequencer token_list
                   TokSRParen -> []

sendbindingtokens :: [Token] -> [Token]
sendbindingtokens [] = []
sendbindingtokens tokens = 
        take (fromJust $ elemIndex TokSRParen tokens) $ tokens     


sendunbindingtokens :: [Token] -> [Token]
sendunbindingtokens [] = []
sendunbindingtokens tokens =
         drop (fromJust $ elemIndex TokSRParen tokens)  $ tokens 




parser :: [Token] -> Tree
parser [] = Empty
parser (token : token_list) =
        case token of 
                TokLParen ->  parser token_list
                TokRParen ->  parser token_list
                TokSLParen -> BindExp (bindsequencer (sendbindingtokens token_list)) (parser (sendunbindingtokens token_list))
                TokSRParen -> parser token_list
                TokBinOp binop -> BinExp binop (parser [head token_list]) (parser (tail token_list))
                TokAssume -> AssumeExp (parser token_list)
                TokID id -> IdentExp id
                TokIF -> IFExp (parser [head token_list]) (parser [head (tail token_list)]) (parser (tail (tail token_list))) 
                TokUnOp unop -> UnExp unop (parser token_list)
                TokNum int -> NumExp int 
                TokBool bool -> BoolExp bool

valuetoint:: Value -> Integer
valuetoint v = case v of IntVal i-> i

valuetobool:: Value -> Bool
valuetobool v = case v of BoolVal b-> b

eval :: Environment -> Tree -> Value

eval env (BindExp bindings bindexptree) =  eval (envexpand env bindings) bindexptree


eval env (BinExp op left right) = 
    let lft = eval env left
        rgt = eval env right
    in
        case op of
          Plus  -> IntVal ((valuetoint lft) + (valuetoint rgt))
          Minus -> IntVal ((valuetoint lft) - (valuetoint rgt))
          Times -> IntVal ((valuetoint lft) * (valuetoint rgt))
          Div   -> IntVal (quot (valuetoint lft) (valuetoint rgt))
          Eqv -> if ((valuetobool lft) == (valuetobool rgt)) then (BoolVal True) else (BoolVal False)
          And -> BoolVal ((valuetobool lft) && (valuetobool rgt))
          Or -> BoolVal ((valuetobool lft) || (valuetobool rgt))

eval env (UnExp op tree) =
    let x = eval env tree 
    in case op of
         IsZero  -> if ((valuetoint x)==0) then (BoolVal True) else (BoolVal False)

         Not  -> if ((valuetobool x)) then (BoolVal False) else (BoolVal True)

eval env (IFExp cond thenpart elsepart) =
         if (valuetobool (eval env cond))
                then (eval env thenpart) 
                else (eval env elsepart)

eval env (NumExp x) = IntVal x

eval env (BoolExp x) = BoolVal x

eval env (IdentExp x) = getvalue env x

main = do 
          putStr "Enter the String Expression \n"
          str <- getLine
          (print . (eval $ Data.Map.empty) . parser. tokenize . arranize) str
          return ()

--main = (print . eval . parser. tokenize . arranize) "( True )"
--main = (print . (eval $ M.empty) . parser. tokenize . arranize) "( + 5 ( assume ( [ ( y 2 ) ( x 3 ) ( z 7 ) ] ) ( + y x ) ) )"
-- ( + 5 ( assume ( [ ( y 2 ) ( x 3 ) ( z 7 ) ] ) ( + y x ) ) )
-- ( if ( assume ( ( y True ) ( x False ) )  ( ~ y ) ) 5 4 ) 