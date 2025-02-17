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
sexp2Exp (SList (func : args)) = 
  case (func : args ) of 
    ((SSym sym) : args) -> do
      func' <- var2Symbol func
      case args of
        (SNum z:[]) -> do
                z' <- sexp2Exp (SNum z)
                return (EApp (EVar func') (z'))
        (SSym z:[]) -> do
                z' <- var2Symbol (SSym z)
                return (EApp (EVar func') (EVar z'))
        (z:zs) -> do
                z' <- sexp2Exp (last zs)
                zs' <- sexp2Exp (SList(func:z:(init zs)))
                return (EApp zs' z')
        _ -> return (EVar func')

    (func : args : []) -> do
      expr <- sexp2Exp func
      args' <- sexp2Exp args
      return (EApp (expr) (args'))

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

specialForm2Exp ((SSym "let") :
                  (SList vars) :
                  (exp):
                  []) = do
                    vars' <- sequence(map (\(SList (sym : e : [])) -> do
                    sym' <- var2Symbol sym
                    e' <- sexp2Exp e
                    return (sym',e')) vars)
                    
                    exp' <- sexp2Exp exp
                    return (ELet vars' exp')

specialForm2Exp ((SSym "data") :
                  (SSym datatype) :
                  cons1 :
                  cons2 ) = do
                     type' <- var2Symbol (SSym datatype)     
                     cons1' <- dataConst cons1
                     cons2' <- sequence (map dataConst cons2)
                     cons' <- Right $ cons1':cons2'
                     return (EData type' cons')                  
                      
specialForm2Exp _ = Left "Syntax Error : Unknown special form"    

dataConst :: Sexp -> Either Error DataConstructor
dataConst (SList ((SSym cons):[])) = do
  cons' <- var2Symbol (SSym cons)
  return (cons', [])
dataConst (SList ((SSym cons):types)) = do
  cons' <- var2Symbol (SSym cons)
  types' <- sequence (map (\t -> var2Symbol t) types)
  return (cons', types')
dataConst _ = Left "Data invalid"

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

envTypes :: Env
envTypes = envEmpty

--intDef :: (Symbol, Value)
--intDef = ("Int", int)
--    where int =
--      VPrim (\ (VInt x) -> (VInt x))

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
    

evalGlobal env (EData t cs) = do
  cs' <- sequence (map (\(const, typelist) -> case typelist of
    [] -> Right ((const, VData t const [VUnit]))
    (x:[]) -> case x of
      "Int" -> Right ((const, (VData t const [VPrim (\(VInt x) -> (VInt x))])))
    (x:xs) -> case x of
      "Int" -> do
        x' <- Right $ VData t const [VPrim (\(VInt x) -> (VInt x))]
        xs' <- Right $ VData t const [VPrim (\(VData t cons val) -> (VData t cons val))]
        return (const, (VData t const [xs']))
      _ -> Left "Type inconnu"
    _ -> Left "Constructeur invalide") cs)
  env' <- Right (insertVars env cs')
  return (env', VUnit)

-- evalGlobal env (EData t cs) = do
--   cs' <- sequence (map (\(const, typelist) -> case typelist of
--     [] -> Right ((const, VData t const [VUnit]))
--     (x:[]) -> case x of
--       "Int" -> Right ((const, (VData t const [VPrim (\(VInt x) -> (VInt x))])))
--     (x:xs) -> do
--         x' <- Right $ VData t const [VPrim (\(VInt x) -> VPrim (\(VInt y) -> VData t const [(VInt x),(VInt y)]))]
--         xs' <- Right $ VData t const [VPrim (\(VInt x) -> (VInt x))]
--         return (const, (VData t const [x', xs']))) cs)
--         --[VPrim (\(VData t cons val) -> VPrim (\ (VInt x) -> (VData t cons [VInt x])))]
--         --[VPrim (\(VInt x) -> VPrim (\ (VData t cons val) -> (VData t cons [VInt x])))]
--         --xs' <- Right $ VData t const [VPrim (\(VData t cons val) -> (VData t cons val))]
--         --return (const, (VData t const [x', xs'])) cs)
--       --t -> 
--     --_ -> Left "Constructeur invalide") cs)
--   env' <- Right (insertVars env cs')
--   return (env', VUnit)

--   evalGlobal env (EData t cs) = case cs of
--     (const:[]) -> Right ((const, VData t const [VUnit]))
--     (const1:const2) -> do
--       const1' <- constToData t const const1

-- -- constToData :: Symbol -> [(Symbol, [Symbol])] -> [(Symbol, Value)]
-- constToData 


-- constToData (const, []) = (const, VData t const [VUnit])
-- constToData (const, (c:[])) = case x of
--   "Int" -> (const, (VData t const [VPrim (\(VInt x) -> (VInt x))]))
-- constToData (const, (c:cs)) = do
--   (const', c') <- constToData (const, c)
--   cs' <- VData t const [VData t constToData (c:cs)]

  

evalGlobal env e = eval env e -- Autre que Define et Data, eval prend le relais

-- consToValue :: Type -> DataConstructor -> Either Error (Symbol, Value)
-- consToValue t (cs, []) = Right $ (cs, (VData t cs []))
-- consToValue t (cs, list) = Right $ (cs, (VPrim (VData t cs)))
-- consToValue t (_,_) = Left "Constructeur non reconnu"



-- addTypeToEnv :: Env -> Exp -> (Exp, [Exp]) -> Env
-- addTypeToEnv env t (cs, []) = do
--   (cs', v) <- (cs, VData t cs [])
--   env' <- insertVars env (cs', v)
--   return env'
-- addTypeToEnv env t (cs, _) = do
--   (cs', v) <- (cs, VData t cs [VUnit])
--   env' <- insertVars env (cs', v)
--   return env
'
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

eval env (EApp f arg) = do
  (env', f') <- eval env f
  (env'', arg') <- eval env arg
  case f' of
    VPrim prim -> return (env'', prim arg')
    VLam p body ferm -> do
      (env', value') <- eval ((p, arg') : ferm) body
      return (env, value')
    VData t1 t2 cs -> case (head cs) of
      VPrim prim -> return (env'', prim arg')
      VData t1 t2 cs' -> return (env'', (head cs'))
      _ -> Left "Constructor is not a function"
    _ -> Left "Not a function"    

eval env (ELet decls e) = do
  decls' <- sequence(map(\(sym,exp) -> do
    (ferm, exp') <- eval env exp
    return (sym,exp')) decls)
  env' <- Right (insertVars env decls')
  (ferm, val) <- eval env' e
  return (env, val)

eval env (ECase e patterns) = Left "e"

eval env (EOufScope sym scope) = Left "f"

eval env (EOufMutability ident mutability) = Left "g"