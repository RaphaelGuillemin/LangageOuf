module Main where

import Data.List
import Data.Char
import Control.Monad.Trans
import System.Console.Haskeline
import Text.ParserCombinators.Parsec
import Control.Arrow

import Parseur
import Eval


mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f (Left x) = Left $ f x
mapLeft _ (Right x) = Right x

string2Sexp :: String -> Either Error Sexp
string2Sexp code = mapLeft show $ parse pOneSexp "" code

string2ManySexp :: String -> Either Error [Sexp]
string2ManySexp code = mapLeft show $ parse pManySexp "" code

sexp2ExpIO :: String -> IO ()
sexp2ExpIO code = either
                  (\err -> putStrLn $ show err)
                  (\exp -> putStrLn $ show exp)
                  (string2Sexp code >>= sexp2Exp)

evalIO :: Env -> String -> IO Env
evalIO env code = either
              (\err -> putStrLn (show err) >> return env)
              (\(env', value) -> putStrLn (show value) >> return env')
              (string2Sexp code >>= sexp2Exp >>= evalGlobal env)

-- Lit un fichier de Sexps
-- Chaque sexp contient deux sous exp
-- Les deux sont évaluées séparémment le résultat doit être identique
-- Lorsque la 2e Sexp a pour mot clé Erreur, alors la première doit
-- retourner une erreur

unittests :: String -> IO ()
unittests file =  do
  code <- readFile file
  case string2ManySexp code of
    Left err -> putStrLn err
    Right sexps ->
      case eval' (env0, []) sexps of
        (Just err, res) -> do
          putStrLn "Une erreur inattendue s'est produite"
          putStrLn $ "Le message est :" ++ (show err)
          putStrLn "Voici les résultats AVANT l'erreur"
          putStrLn (prettyprint res)
        (Nothing, res) -> putStrLn (prettyprint res)

  -- Évalue les expressions les unes après les autres
  -- Discarte les valeurs retournées par l'évaluateur mais
  -- conserve les résultats des test unitaires
  -- Si le code plante, on arrête les tests unitaires et on renvoie
  -- l'erreur avec les résultats déjà accumulé
  where eval' :: (Env, [Bool]) -> [Sexp] -> (Maybe Error, [Bool])
        eval' (_, res) [] = (Nothing, reverse res)
        eval' (env, res) ((SList (SSym ":check-error:" : exp : [])) : xs) =
          case sexp2Exp exp >>= eval env of
            Left _ -> eval' (env, True : res) xs
            Right _ -> eval' (env, False : res) xs

        eval' (env, res) ((SList (SSym ":check-equal:" : e1 : e2 : [])) : xs) =
          let x = do
                (_, v1) <- sexp2Exp e1 >>= eval env
                (_, v2) <- sexp2Exp e2 >>= eval env
                return $ v1 == v2
          in either (\err -> (Just err, reverse res))
             (\r -> eval' (env, r :res) xs)
             x

        eval' (env, res) (exp : xs) =
          let x = do
               (env', _) <- sexp2Exp exp >>= evalGlobal env
               return env'
          in either (\err -> (Just err, reverse res))
             (\env' ->  eval' (env', res) xs)
             x

prettyprint :: [Bool] -> String
prettyprint res = 
      let nbGood = length $ filter (== True) res 
          size = length res
          nbBad = size - nbGood
          details = map showResult (zip [1..] res)
          summary = (show size ++ " unittests effectués. " ++ show nbGood
                     ++ " OK et "
                     ++ show nbBad ++ " KO.")
      in trim (concat details) ++ "\n"  ++ summary

      where
        showResult :: (Int, Bool) -> String
        showResult (i, False) = "Test " ++ show i ++ " KO\n"
        showResult (i, True) = "" -- Nothing to say

-- REPL : Read Eval Print Loop
-- Vous permet d'évaluer des expressions à l'aide de GHCi,
-- l'interpréteur de Haskell qui vient avec la Haskell Platform
-- Pour quitter le mode Ouf, vous devez entrer :q
repl :: IO ()
repl = runInputT defaultSettings (loop env0)
  where
  loop :: Env -> InputT IO ()
  loop env = do
    input <- getInputLine "Ouf> "
    case input of
      Nothing -> outputStrLn "Leaving Ouf"
      Just input | trim input == ":q" -> outputStrLn "Leaving Ouf Haskell"
      Just input | startsWith ":e" $ trim input ->
                   (liftIO $ sexp2ExpIO (drop 2 input)) >> loop env
      Just input | trim input == ":showEnv" ->
                   outputStrLn (show env) >> loop env
      Just input -> (liftIO $ evalIO env input) >>= loop

  startsWith [] _ = False
  startsWith [a] (x : xs) | a == x = True
  startsWith (a : as) (x : xs) | a == x = startsWith as xs
  startsWith _ _ = False
  
trim = dropWhileEnd isSpace . dropWhile isSpace

testEval :: Env -> String -> Either Error (Env, Value)
testEval e s = string2Sexp s >>= sexp2Exp >>= evalGlobal e
  
main = repl
