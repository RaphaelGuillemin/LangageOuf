module Eval where

import qualified Data.Map as M
import Parseur


--------------------------------------------------------------------------------
-- Les expressions et la traduction de Sexp en expression (Exp)
--------------------------------------------------------------------------------

-- type a = b indique que a est un synonyme de b
-- il ne s'agit pas vraiment d'un nouveau type
type Type = Symbol
type Constructor = Symbol
type DataConstructor = (Constructor, [Type])

type CasePattern = (Symbol, [Symbol], Exp)

data Mutability = Constant
                | Mutable
                deriving (Eq, Show)
                
data Scope = Lexical
           | Dynamic
           deriving (Eq, Show)

-- Les expressions du langages ouf
-- Vous n'avez pas à modifier ce datatype
data Exp = EInt Int
         | EVar Symbol
         | EDefine Symbol Exp
         | EApp Exp Exp
         | ELam Symbol Exp
         | ESet Symbol Exp
         | ELet [(Symbol, Exp)] Exp
         | EData Type [DataConstructor]
         | ECase Exp [CasePattern]
         | EOufScope Symbol Scope
         | EOufMutability Symbol Mutability
         deriving (Eq, Show)

type Error = String

reservedKeywords :: [Symbol]
reservedKeywords = ["lambda", "let", "case", "data", "define", "set", "ouf", "Error"]


var2Exp :: Sexp -> Either Error Exp
var2Exp (SSym ident) = Right $ EVar ident
var2Exp _ = Left "Doit être un identificateur"

var2Symbol :: Sexp -> Either Error Symbol
var2Symbol (SSym ident) = Right ident
var2Symbol _ = Left "Doit être un identificateur"

-- Vous devez compléter une partie cette fonction
sexp2Exp :: Sexp -> Either Error Exp
sexp2Exp (SNum x) = Right $ EInt x
sexp2Exp (SSym ident) =
  if ident `elem` reservedKeywords
  then Left $ ident ++ " is a reserved keyword"
  else Right $ EVar ident
sexp2Exp (SList ls@((SSym s) : xs)) | s `elem` reservedKeywords
  = specialForm2Exp ls 
sexp2Exp (SList (func : [])) =
  Left "Function application must provide at least one parameter"

-- Il faut écrire le cas pour les fonctions
sexp2Exp (SList (func : args)) = do
  func' <- var2Symbol func
  case args of
    (x:xs:[]) -> do 
              x' <- var2Symbol x 
              y <- var2Symbol xs
              return (EApp (EApp (EVar func') (EVar x')) (EVar y))
    (SNum z:[]) -> do
            z' <- sexp2Exp (SNum z)
            return (EApp (EVar func') (z'))
    _ -> return (EVar func')

sexp2Exp _ = Left "Erreur de syntaxe"



-- Il faut compléter cette fonction qui gère
-- toutes les formes spéciales (lambda, let ...)
specialForm2Exp :: [Sexp] -> Either Error Exp
specialForm2Exp ((SSym "lambda") :
                 (SList []) :
                 _ : []) = Left "Syntax Error : No parameter"
  
specialForm2Exp ((SSym "lambda") :
                 (SList params) :
                 body :
                 []) = do
  body' <- sexp2Exp body
  params' <- sequence  $ reverse $ map var2Symbol params
  return $ foldl (\b s -> ELam s b)
                 (ELam (head params') body')
                 (tail params')

specialForm2Exp ((SSym "define") :
                 []) = Left "Syntax Error : No parameter"

specialForm2Exp ((SSym "define") :
                   (SSym sym) :
                   (SNum a):
                   []) = do
                     func' <- var2Symbol (SSym sym)
                     a' <- sexp2Exp (SNum a)
                     return (EDefine func' a')

specialForm2Exp ((SSym "define") :
                   (SSym func) :
                   (SList body):
                   []) = do
                     func' <- var2Symbol (SSym func)
                     body' <- specialForm2Exp (body)
                     return (EDefine func' body')

specialForm2Exp _ = Left "Syntax Error : Unknown special form"



--------------------------------------------------------------------------------
-- L'évaluation
--------------------------------------------------------------------------------

-- Les valeurs retournées par l'évaluateur
-- Vous n'avez pas à modifier ce datatype
data Value = VInt Int
           | VLam Symbol Exp LexicalEnv
           | VPrim (Value -> Value)
           | VData Type Type [Value]
           | VUnit

instance Show Value where
  show (VInt n) = show n
  show (VData t c d) = "VData " ++ t ++ " (" ++
    (unwords $ show c : map show d) ++ ")"
  show VUnit = "VUnit"
  show (VPrim _) = "<primitive>"
  show (VLam s e env) = "VLamda [" ++ s ++ (unwords [",", show e, ",", show env])
    ++ "]"
  
instance Eq Value where
  (VInt n1) == (VInt n2) = n1 == n2
  VUnit == VUnit = True
  (VData t1 c1 d1) == (VData t2 c2 d2) =
     t1 == t2 && c1 == c2 && d1 == d2 
  -- Functions and primitives are not comparable
  _ == _ = False

-- Un environnement pour portée lexicale
-- Vous n'avez pas à modifier ce datatype
type LexicalEnv = [(Symbol, Value)]

-- L'environnement. Au début, comme celui de la portée lexicale
-- Vous devrez modifier ce type pour la portée dynamique
-- et les instructions ouf
type Env = LexicalEnv

-- lookup de la librairie standard utilise Maybe
-- au lieu de Either
lookup2 :: [(Symbol, a)] -> Symbol -> Either Error a
lookup2 [] sym = Left $ "Not in scope " ++ sym
lookup2 ((s, v) : _) sym | s == sym = Right v
lookup2 (_ : xs) sym = lookup2 xs sym

-- Recherche un identificateur dans l'environnement
lookupVar :: Env -> Symbol -> Either Error Value
lookupVar = lookup2

-- Ajoute une variable dans l'environnement
insertVar :: Env -> Symbol -> Value -> Env
insertVar e s v =  (s, v) : e

-- Insert plusieurs variables dans l'environnement
-- La première variable de la liste est la dernière insérée
insertVars :: Env -> [(Symbol, Value)] -> Env
insertVars env xs = foldr (\(s, v) env -> insertVar env s v) env xs

primDef :: [(Symbol, Value)]
primDef = [("+", prim (+)),
           ("-", prim (-)),
           ("*", prim (*))]
  where prim op =
          VPrim (\ (VInt x) -> VPrim (\ (VInt y) -> VInt (x `op` y)))

envEmpty :: Env
envEmpty = []

env0 :: Env
env0 = insertVars envEmpty primDef


-- L'évaluateur au niveau global
-- L'évaluateur retourne une valeur et un environnement mis à jour
-- L'environnement mis à jour est utile pour de nouvelles définitions
-- avec define ou data ou lorsque les variables sont
-- modifiées par set par exemple.
evalGlobal :: Env -> Exp -> Either Error (Env, Value)

evalGlobal env (EDefine s e) = 
  case eval env e of
    Left m -> Left m
    Right (e, v) -> Right (insertVar env s v, v)
    

evalGlobal env (EData t cs) = Left "Vous devez compléter cette partie"
evalGlobal env e = eval env e -- Autre que Define et Data, eval prend le relais

-- L'évaluateur pour les expressions
eval :: Env -> Exp -> Either Error (Env, Value)
eval _ (EDefine _ _) = Left $ "Define must be a top level form"
eval _ (EData _ _) = Left $ "Data must be a top level form"
eval env (EInt x) = Right (env, VInt x)
eval env (EVar sym) = do
  v <- lookupVar env sym
  return (env, v)

eval env (ESet sym e) = Left "a"
  
eval env (ELam sym body) = Right (env, VLam sym body env)
  --(env', body') <- eval (insertVars env0 sym) body
  --return (env',body')
  
  
  
  --do
  -- (env', body') <- eval env body
  -- x <- insertVar env sym body'
  -- return x

eval env (EApp f arg) = do
  (env', f') <- eval env f
  (env'', arg') <- eval env' arg
  case f' of
    VPrim prim -> return (env'', prim arg')
    VLam p body ferm -> do
      (env', value') <- eval ((p, arg') : ferm) body
      return (env', value')
    _ -> Left "Not a fonction"

eval env (ELet decls e) = Left "d"

eval env (ECase e patterns) = Left "e"

eval env (EOufScope sym scope) = Left "f"

eval env (EOufMutability ident mutability) = Left "g"