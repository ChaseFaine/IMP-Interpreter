-- Chase Faine

import Data.Char
import Data.List

-- Variables
type Vars = String
-- Arithmetic expressions
data AExpr = Var Vars | Const Integer
                      | Add AExpr AExpr | Sub AExpr AExpr
                      | Mul AExpr AExpr | Div AExpr AExpr
    deriving Show
-- Boolean expressions
data BExpr = TT | FF -- the true and false constants
                | And BExpr BExpr | Or BExpr BExpr | Not BExpr -- boolean operations
                | Eql AExpr AExpr -- equality of arithmetic expressions
                | Lt AExpr AExpr -- true if the first is less than the second
                | Lte AExpr AExpr -- true if it’s less than or equal to
    deriving Show
-- Instructions
data Instr = Assign Vars AExpr -- assign X to the value of an expression
            | IfThenElse BExpr Instr Instr -- conditional
            | While BExpr Instr -- looping construct
            | Do [Instr] -- a block of several instructions
            | Nop -- the "do nothing" instruction
    deriving Show
-- A program is a list of instructions
type Program = [Instr]

type Env = [ (Vars,Integer)]

lookUp :: Vars -> Env -> Integer
lookUp x [] = 1
lookUp x ((y,ys):xs) = if x == y then ys else lookUp x xs

-- update (x,v) e sets the value of x to v and keeps other variables in e the same
update :: (Vars, Integer) -> Env -> Env
update (x,v) [] = [(x,v)]
update (x,v) ((e1,e2):xs) = if x == e1 then (x,v) : xs else (e1,e2) : update (x,v) xs

-- Evaluating arithmetic and boolean expressions

evala :: Env -> AExpr -> Integer
evala env (Var x)     = lookUp x env
evala env (Const x)   = x
evala env (Add t1 t2) = (evala env t1) + (evala env t2)
evala env (Sub t1 t2) = (evala env t1) - (evala env t2)
evala env (Mul t1 t2) = (evala env t1) * (evala env t2)
evala env (Div t1 t2) = (evala env t1) `div` (evala env t2)

evalb :: Env -> BExpr -> Bool
evalb env (TT)        = True
evalb env (FF)        = False
evalb env (And t1 t2) = (evalb env t1) && (evalb env t2)
evalb env (Or t1 t2)  = (evalb env t1) || (evalb env t2)
evalb env (Not t1)    = not (evalb env t1)
evalb env (Eql t1 t2) = (evala env t1) == (evala env t2)
evalb env (Lt t1 t2)  = (evala env t1) < (evala env t2)
evalb env (Lte t1 t2) = (evala env t1) <= (evala env t2)

-- Executing instructions

exec :: Instr -> Env -> Env
exec (Assign x t1) e        = update (x,(evala e t1)) e
exec (IfThenElse x t1 t2) e = if evalb e x then exec t1 e else exec t2 e
exec (While x t1) e         = if evalb e x then exec (Do [t1, While x t1]) e else e
exec (Do []) e              = e
exec (Do (x:xs)) e          = exec (Do xs) (exec x e)
exec (Nop) e                = e

run :: Program -> Env
run p = exec (Do p) []

sum100 :: Program -- a program to add together all the numbers up to 100
sum100 = [
    Assign "X" (Const 0), -- initialize the sum at X=0
    Assign "C" (Const 1), -- initialize the counter at C=1
    While (Lt (Var "C") (Const 101)) -- while C < 101, do:
        (Do [Assign "X" (Add (Var "X") (Var "C")), -- X := X + C;
        Assign "C" (Add (Var "C") (Const 1))] -- C := C + 1
        )]

-- Lexical analysis

data UOps = NotOp deriving Show
data BOps = AddOp | SubOp | MulOp | DivOp
                  | AndOp | OrOp | EqlOp | LtOp | LteOp | AssignOp
    deriving Show
data Token = VSym String | CSym Integer | BSym Bool
            | UOp UOps | BOp BOps
            | LPar | RPar | LBra | RBra | Semi
            | Keyword String
            | Err String
            | PA AExpr | PB BExpr | PI Instr
    deriving Show

isVSym :: String -> Bool
isVSym = let q0 ""     = False
             q0 (x:xs) | x `elem` ['a'..'z'] = q1 xs
                       | x `elem` ['A'..'Z'] = q1 xs
                       | otherwise = False
             q1 [] = True
             q1 (x:xs) = (isLetter x || isDigit x || elem x "_'") && q1 xs
          in q0

isCSym :: String -> Bool
isCSym = let q0 "" = False
             q0 (x:xs) = isDigit x && q1 xs
             q1 "" = True
             q1 (x:xs) = isDigit x && q1 xs
          in q0

isBSym :: String -> Bool
isBSym "" = False
isBSym "TT" = True
isBSym "FF" = True
isBSym _ = False

preproc :: String -> String
preproc []                       = []
preproc ('(':xs)                 = " ( "     ++ preproc xs
preproc (')':xs)                 = " ) "     ++ preproc xs
preproc ('{':xs)                 = " { "     ++ preproc xs
preproc ('}':xs)                 = " } "     ++ preproc xs
preproc (';':xs)                 = " ; "     ++ preproc xs
preproc ('!':xs)                 = " ! "     ++ preproc xs
preproc ('\\':'/':xs)            = " \\/ "   ++ preproc xs
preproc ('/':'\\':xs)            = " /\\ "   ++ preproc xs
preproc ('+':xs)                 = " + "     ++ preproc xs
preproc ('-':xs)                 = " - "     ++ preproc xs
preproc ('*':xs)                 = " * "     ++ preproc xs
preproc ('/':xs)                 = " / "     ++ preproc xs
preproc ('<':'=':xs)             = " <= "    ++ preproc xs
preproc ('<':xs)                 = " < "     ++ preproc xs
preproc (':':'=':xs)             = " := "    ++ preproc xs
preproc ('=':'=':xs)             = " == "    ++ preproc xs
preproc ('T':'T':xs)             = " TT "    ++ preproc xs
preproc ('F':'F':xs)             = " FF "    ++ preproc xs
preproc ('i':'f':xs)             = " if "    ++ preproc xs
preproc ('t':'h':'e':'n':xs)     = " then "  ++ preproc xs
preproc ('e':'l':'s':'e':xs)     = " else "  ++ preproc xs
preproc ('w':'h':'i':'l':'e':xs) = " while " ++ preproc xs
preproc ('n':'o':'p':xs)         = " nop "   ++ preproc xs
preproc (x:xs)                   = x:preproc xs

stringtochar :: String -> [[Char]]
stringtochar x = [x]

classify :: String -> Token
classify "("          = LPar
classify ")"          = RPar 
classify "{"          = LBra 
classify "}"          = RBra
classify ";"          = Semi
classify "!"          = UOp NotOp
classify "/\\"        = BOp AndOp
classify "\\/"        = BOp OrOp
classify "+"          = BOp AddOp
classify "-"          = BOp SubOp
classify "*"          = BOp MulOp
classify "/"          = BOp DivOp
classify "<"          = BOp LtOp
classify "<="         = BOp LteOp
classify ":="         = BOp AssignOp
classify "=="         = BOp EqlOp
classify "TT"         = BSym True
classify "FF"         = BSym False
classify "if"         = Keyword "if"
classify "then"       = Keyword "then"
classify "else"       = Keyword "else"
classify "while"      = Keyword "while"
classify "nop"        = Keyword "nop"
classify x | isCSym x = CSym (read x)
classify x | isBSym x = BSym (read x)
classify x | isVSym x = VSym x

classify s = error $ "Token error: " ++ concat (stringtochar s)

lexer :: String -> [Token]
lexer s = map classify (words (preproc s))

-- Parsing

parser :: [Token] -> Instr
parser input = sr input []

sr :: [Token] -> [Token] -> Instr
sr (Err s : input) _ = error ("Lexical error: " ++ s)

sr [] [PI i] = i

sr input (VSym v : rs)     = sr input (PA (Var v) : rs)
sr input (CSym n : rs)     = sr input (PA (Const n) : rs)
sr input (BSym True : rs)  = sr input (PB TT : rs)
sr input (BSym False : rs) = sr input (PB FF : rs)

sr input (PB e1 : UOp NotOp    : rs)                = sr input (PB (Not e1) : rs)
sr input (PB e2 : BOp AndOp    : PB e1 : rs)        = sr input (PB (And e1 e2) : rs)
sr input (PB e2 : BOp OrOp     : PB e1 : rs)        = sr input (PB (Or e1 e2) : rs)
sr input (PA e2 : BOp AddOp    : PA e1 : rs)        = sr input (PA (Add e1 e2) : rs)
sr input (PA e2 : BOp SubOp    : PA e1 : rs)        = sr input (PA (Sub e1 e2) : rs)
sr input (PA e2 : BOp MulOp    : PA e1 : rs)        = sr input (PA (Mul e1 e2) : rs)
sr input (PA e2 : BOp DivOp    : PA e1 : rs)        = sr input (PA (Div e1 e2) : rs)
sr input (PA e2 : BOp LtOp     : PA e1 : rs)        = sr input (PB (Lt e1 e2) : rs)
sr input (PA e2 : BOp LteOp    : PA e1 : rs)        = sr input (PB (Lte e1 e2) : rs)
sr input (PA e2 : BOp AssignOp : PA (Var e1) : rs)  = sr input (PI (Assign e1 e2) : rs)
sr input (PA e2 : BOp EqlOp    : PA e1 : rs)        = sr input (PB (Eql e1 e2) : rs)

sr input (PI i : Keyword "else" : PI i2 : Keyword "then" : PB b : Keyword "if" : rs) = sr input (PI (IfThenElse b i i2) : rs)
sr input (PI i : PB b : Keyword "while" : rs)                                        = sr input (PI (While b i) : rs)
sr input (PI i : PB b : Keyword "nop" : rs)                                          = sr input (PI (Nop) : rs)

sr input (RPar : PA e : LPar : rs)      = sr input (PA e : rs)
sr input (RPar : PB e : LPar : rs)      = sr input (PB e : rs)
sr input (RBra : PI i : rs)             = sr input (PI (Do [i]) : rs)
sr input (RBra : rs)                    = sr input (PI (Do []) : rs)
sr input (PI (Do e) : Semi : PI i : rs) = sr input (PI (Do (i:e)) : rs)
sr input (PI (Do e) : LBra : rs)        = sr input (PI (Do e) : rs)
sr input (PI i2 : Semi : PI i1 : rs)    = sr input (PI (Do [i1, i2]) : rs)

sr (i:input) stack = sr input (i:stack)
sr [] stack = error (show stack)

-- I/O

helper :: Instr -> [Instr]
helper x = [x]

main :: IO ()
main = do
    putStrLn "Please enter a filename: "
    filename <- getLine
    file     <- readFile filename
    let l = lexer file
    let p = parser l
    let r = run (reverse (helper p))
    putStrLn (show r)