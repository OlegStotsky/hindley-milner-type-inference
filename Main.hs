{-# LANGUAGE FlexibleContexts #-}

import Control.Monad.Except
import Data.List
import Data.Monoid
import Data.Semigroup
import Control.Monad.State

infixl 2 :@
infixr 3 :->

type Symb = String 

-- Терм
data Expr = 
  Var Symb 
  | Expr :@ Expr
  | Lam Symb Expr
     deriving (Eq,Show)

-- Тип
data Type = 
  TVar Symb 
  | Type :-> Type
    deriving (Eq,Show)

-- Контекст
newtype Env = Env [(Symb,Type)]
  deriving (Eq,Show)

-- Подстановка
newtype SubsTy = SubsTy [(Symb, Type)]
  deriving (Eq,Show)

unique :: Eq a => [a] -> [a]
unique [x] = [x]
unique [] = []
unique (x:xs) = let l = unique xs in if elem x l then l else x:l

freeVars :: Expr -> [Symb] 
freeVars (Var x) = [x]
freeVars (left :@ right) = unique $ (freeVars left) ++ (freeVars right)
freeVars (Lam x m) = filter (/=x) (freeVars m)

freeTVars :: Type -> [Symb]
freeTVars (TVar x) = [x]
freeTVars (l :-> r) = unique $ (freeTVars l) ++ (freeTVars r)

extendEnv :: Env -> Symb -> Type -> Env
extendEnv (Env env) sym t = Env $ unique $ (sym, t) : env

extendSubsTy :: SubsTy -> Symb -> Type -> SubsTy
extendSubsTy (SubsTy sbs) sym t = SubsTy $ unique $ (sym, t) : sbs

freeTVarsEnv :: Env -> [Symb]
freeTVarsEnv (Env env) = unique $ env >>= (\x -> freeTVars $ snd x)

appEnv :: (MonadError String m) => Env -> Symb -> m Type
appEnv (Env []) v = throwError ("There is no variable \"" ++ v ++ "\" in the environment.")
appEnv (Env (x:xs)) v = let (fi, se) = x in if fi == v then return se else appEnv (Env xs) v

appSubsTy :: SubsTy -> Type -> Type
appSubsTy sbs (l :-> r) = (appSubsTy sbs l) :-> (appSubsTy sbs r)
appSubsTy (SubsTy sbs) (TVar x) = case elemIndex x (map fst sbs) of
                          Just i -> snd (sbs !! i)
                          Nothing -> (TVar x)

getSub :: Symb -> SubsTy -> Maybe Type
getSub _ (SubsTy []) = Nothing
getSub s (SubsTy (x:xs)) = if s == (fst x) then (Just $ snd x) else getSub s (SubsTy xs)

appSubsEnv :: SubsTy -> Env -> Env
appSubsEnv _ (Env []) = Env []
appSubsEnv s q@(Env (e:env)) = let (sym, t) = e in extendEnv (appSubsEnv s (Env env)) sym (appSubsTy s t)

addMissingElems :: SubsTy -> SubsTy -> SubsTy
addMissingElems (SubsTy []) to = to
addMissingElems (SubsTy (x:xs)) to = let (sym, t) = x in case getSub sym to of
                                            Nothing -> extendSubsTy (addMissingElems (SubsTy $ xs) to) sym t
                                            _ -> addMissingElems (SubsTy $ xs) to

composeSubsTy :: SubsTy -> SubsTy -> SubsTy
composeSubsTy second first = addMissingElems second (composeSubsTyHelper second first)

composeSubsTyHelper :: SubsTy -> SubsTy -> SubsTy
composeSubsTyHelper second (SubsTy (x:xs)) = let (sym, t) = x; newT = appSubsTy second t 
                                             in extendSubsTy (composeSubsTy second (SubsTy $ xs)) sym newT
composeSubsTyHelper _ (SubsTy ([])) = SubsTy []

instance Semigroup SubsTy where
  (<>) = composeSubsTy

instance Monoid SubsTy where
  mempty = SubsTy $ []
  mappend = composeSubsTy

unify :: (MonadError String m) => Type -> Type -> m SubsTy
unify (TVar x) (TVar y) | x == y = return $ SubsTy []
unify left@(TVar x) y = if elem x (freeTVars y) 
  then throwError ("Can't unify (" ++ (show left) ++ ") with (" ++ (show y) ++ ")!")
  else return $ SubsTy [(x, y)]
unify left@(x :-> y) right@(TVar _) = unify right left
unify (a1 :-> b1) (a2 :-> b2) = do sbs <- unify b1 b2
                                   le <- unify (appSubsTy sbs a1) (appSubsTy sbs a2)
                                   return $ le <> sbs

getFreshSym :: Integer -> Symb
getFreshSym n = show n

equations :: (MonadError String m) => Env -> Expr -> Type -> m [(Type,Type)]
equations env x t = evalStateT (helper env x t) 0 where
   helper :: (MonadError String m) => Env -> Expr -> Type -> StateT Integer m ([(Type, Type)])
   helper env (Var x) t = do xType <- lift $ appEnv env x
                             return [(t, xType)]
   helper env (l :@ r) t = do st <- get
                              put $ (st + 1)
                              let tvar = TVar ("___" ++ (show st))
                              l <- helper env l (tvar :-> t)
                              r <- helper env r tvar
                              return $ l ++ r

   helper env (Lam x exp) t = do st <- get
                                 put $ (st + 1)
                                 st2 <- get
                                 put $ st2 + 1
                                 let tvar1 =  TVar ("___" ++ show st)
                                 let tvar2 = TVar ("___" ++ show st2)
                                 l <- helper (extendEnv env x tvar1) exp tvar2
                                 return $ (tvar1 :-> tvar2, t) : l

genStartingEnv :: Expr -> Env
genStartingEnv ex = Env $ helper (freeVars ex) 1 where
            helper (x:xs) n = (x, TVar $ (getFreshSym n)) : helper xs (n+1)
            helper [] n = []

principlePair :: (MonadError String m) =>  Expr -> m (Env,Type)
principlePair ex = do let startEnv = genStartingEnv ex
                      equations <- equations startEnv ex (TVar "0")
                      let (l, r) = foldr1 (\(l, r) (l', r') -> (l :-> l', r :-> r')) equations
                      sbt <- unify l r
                      return $ (appSubsEnv sbt startEnv, appSubsTy sbt (TVar "0"))
