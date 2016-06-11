{-# LANGUAGE GADTs, DataKinds, KindSignatures,
    MultiParamTypeClasses, FunctionalDependencies,
    TypeSynonymInstances, FlexibleInstances,
    StandaloneDeriving, PatternGuards, PatternSynonyms #-}

module Bits where

import Prelude hiding ((/))
import Control.Monad
import Control.Monad.Reader

data Stage    = Exp ExpStage | Val
data ExpStage = Raw  | Normal
data Status   = Done | Stuk

data Syn :: Stage -> Status -> * where
  B      :: Bool ->                          Syn s Done
  N      ::                                  Syn s Done
  (:&)   :: Syn s Done -> Syn s Done ->      Syn s Done
  L      :: Abst s ->                        Syn s Done
  S      :: Syn s Stuk ->                    Syn s Done
  I      :: Cached TERM ->                   Syn (Exp Normal) Done
  P      :: REF ->                           Syn s Stuk
  (:/)   :: Syn s Stuk -> Syn s Done ->      Syn s Stuk
  V      :: Int ->                           Syn (Exp e) Stuk
  (:::)  :: TERM -> TERM ->                  Syn (Exp Raw) Stuk

data Abst :: Stage -> * where
  U     :: Syn (Exp e) Done ->           Abst (Exp e)
  (:.)  :: ENV -> Syn (Exp Raw) Done ->  Abst Val

data REF = Name :< Cached TYPE deriving (Show, Eq)
refType :: REF -> TYPE
refType (_ :< s) = cached s

type VAL  = Syn Val Done
type BLK  = Syn Val Stuk
type TERM = Syn (Exp Raw) Done
type COMP = Syn (Exp Raw) Stuk
type NORM = Syn (Exp Normal) Done
type NEUT = Syn (Exp Normal) Stuk
type ENV  = [VAL]
type TYPE = VAL

deriving instance Eq (Syn s u)
deriving instance Eq (Abst s)

deriving instance Show (Syn s u)
deriving instance Show (Abst s)

newtype Cached x = Cache {cached :: x}
instance Eq (Cached x) where _ == _ = True
instance Show (Cached x) where show _ = ""

type Name = String

eval :: ENV -> Syn (Exp Raw) s -> VAL
eval _ (B b)      = B b
eval g N          = N
eval g (a :& d)   = eval g a :& eval g d
eval g (L (U a))  = L (g :. a)
eval g (S e)      = eval g e
eval g (P x)      = S (P x)
eval g (f :/ s)   = eval g f / eval g s
eval g (V i)      = g !! i
eval g (t ::: _)  = eval g t

fun :: Abst (Exp Raw) -> Abst Val
fun (U a) = [] :. a

class Slash f a v | f -> v where
  (/) :: f -> a -> v

instance Slash VAL VAL VAL where
  S f / v = S (f :/ v)
  L a / v = a / v
  (a :& d) / B 0 = a
  (a :& d) / B 1 = d
  B 0 / Cond a f t = f
  B 1 / Cond a f t = t

instance Slash (Abst Val) VAL VAL where
  (g :. t) / v  = eval (v : g) t

instance Slash VAL REF VAL where
  f / x = f / (S (P x) :: VAL)

instance Slash (Abst Val) REF VAL where
  f / x = f / (S (P x) :: VAL)

varOp :: (Int -> Either REF Int -> Maybe (Syn (Exp e) Stuk)) ->
         Int -> Syn (Exp e) u -> Syn (Exp e) u
varOp r l (P x)      | Just e <- r l (Left x)   = e
varOp r l (V i)      | Just e <- r l (Right i)  = e
varOp r l (L (U a))  = L (U (varOp r (l + 1) a))
varOp r l (a :& d)   = varOp r l a :& varOp r l d
varOp r l (S e)      = S (varOp r l e)
varOp r l (f :/ s)   = varOp r l f :/ varOp r l s
varOp r l (t ::: y)  = varOp r l t ::: varOp r l y
varOp r l t          = t

instantiate :: Syn (Exp Raw) Stuk -> Int -> Either REF Int ->
                 Maybe (Syn (Exp Raw) Stuk)
instantiate e i (Right j) | i == j = Just e
instantiate _ _ _ = Nothing

abstract :: REF -> Int -> Either REF Int ->
                 Maybe (Syn (Exp e) Stuk)
abstract x i (Left y) | x == y = Just (V i)
abstract _ _ _ = Nothing

instance Slash (Abst (Exp Raw)) (Syn (Exp Raw) Stuk)
              (Syn (Exp Raw) Done) where
  U a / e = varOp (instantiate e) 0 a

instance Slash (Abst (Exp Raw)) REF
              (Syn (Exp Raw) Done) where
  U a / x = varOp (instantiate (P x)) 0 a

type TC = ReaderT Int Maybe

class Discharge t a | t -> a, a -> t where
  (\\) :: REF -> t -> a

instance Discharge () () where
  _ \\ () = ()

instance Discharge (Syn (Exp e) Done) (Abst (Exp e)) where
  x \\ t = U (varOp (abstract x) 0 t)

(!-) :: Discharge t a => TYPE -> (REF -> TC t) -> TC a
s !- f = do
  i <- ask
  let x = show i :< Cache s
  fmap (x \\) (local succ (f x))

pattern TC t = B 0 :& B 0 :& t
pattern Type   = TC (B 0 :& B 0 :& N)
pattern Pi s t = TC (B 0 :& B 1 :& B 0 :& s :& L t :& N)
pattern Sg s t = TC (B 0 :& B 1 :& B 1 :& s :& L t :& N)
pattern Bit    = TC (B 1 :& B 0 :& B 0 :& N)

b0V :: VAL
b0V = B 0
b1V :: VAL
b1V = B 1

pattern Cond a f t = L a :& f :& t :& N


quoteV :: TYPE -> VAL -> TC NORM
quoteV Type (Pi s t) = do
  s' <- quoteV Type s
  t' <- s !- \ x -> quoteV Type (t / x)
  return (Pi s' t')
quoteV (Pi s t) f = do
  a' <- s !- \ x -> quoteV (t / x) (f / x)
  return (L a')
quoteV Type (Sg s t) = do
  s' <- quoteV Type s
  t' <- s !- \ x -> quoteV Type (t / x)
  return (Sg s' t')
quoteV (Sg s t) p = do
  let a = p / b0V
  a' <- quoteV s a
  d' <- quoteV (t / a) (p / b1V)
  return (a' :& d')
quoteV Type Bit = return Bit
quoteV Bit (B b) = return (B b)
quoteV _ (S e) = do
  (e', _) <- quoteB e
  return (S e')

quoteB :: BLK -> TC (NEUT, TYPE)
quoteB (P x) = return (P x, refType x)
quoteB (f :/ a) = do
  (f', y) <- quoteB f
  a' <- quoteA y a
  return (f' :/ a', actType (S f, y) a)

quoteA :: TYPE -> VAL -> TC NORM
quoteA (Pi s t) a      = quoteV s a
quoteA (Sg s t) (B b)  = return (B b)
quoteA Bit (Cond a f t) = do
  a' <- Bit !- \ x -> quoteV Type (a / x)
  f' <- quoteV (a / b0V) f
  t' <- quoteV (a / b1V) t
  return (Cond a' f' t')

checkV :: TYPE -> TERM -> TC VAL
checkV w t = do
  check w t
  return (eval [] t)

check :: TYPE -> TERM -> TC ()
check Type (Pi s t) = do
  s <- checkV Type s
  s !- \ x -> check Type (t / x)
check (Pi s t) (L a) = do
  s !- \ x -> check (t / x) (a / x)
check Type (Sg s t) = do
  s <- checkV Type s
  s !- \ x -> check Type (t / x)
check (Sg s t) (a :& d) = do
  a <- checkV s a
  check (t / a) d
check Type Bit = return ()
check Bit (B _) = return ()
check w (S e) = do
  v <- synth e
  v <<== w

action :: TYPE -> TERM -> TC ()
action (Pi s t) a = check s a
action (Sg s t) (B _) = return ()
action Bit (Cond a f t) = do
  Bit !- \ x -> check Type (a / x)
  check (fun a / b0V) f
  check (fun a / b1V) t
action _ _ = fail "bad action"

actType :: (VAL, TYPE) -> VAL -> TYPE
actType (_, Pi s t) a    = t / a
actType (_, Sg s t) (B 0)  = s
actType (p, Sg s t) (B 1)  = t / (p / b0V)
actType (b, Bit) (Cond a f t) = a / b

actionV :: TYPE -> TERM -> TC VAL
actionV y a = do
  action y a
  return (eval [] a)

synth :: COMP -> TC TYPE
synth (P x) = return (refType x)
synth (f :/ a) = do
  (f, y) <- synthV f
  a <- actionV y a
  return (actType (f, y) a)
synth (t ::: y) = do
  y <- checkV Type y
  check y t
  return y

synthV :: COMP -> TC (VAL, TYPE)
synthV e = do
  y <- synth e
  return (eval [] e, y)

(<<==) :: TYPE -> TYPE -> TC ()
Pi s t <<== Pi s' t' = do
  s' <<== s
  s' !- \ x -> (t / x) <<== (t' / x) 
Sg s t <<== Pi s' t' = do
  s <<== s'
  s !- \ x -> (t / x) <<== (t' / x)
Bit <<== Bit = return ()
S e <<== S f = do
  (e, _) <- quoteB e
  (f, _) <- quoteB f
  guard (e == f)
_ <<== _ = fail "no fit"

instance Num Bool where
  fromInteger 0 = False
  fromInteger _ = True
  False + b = b
  True + b = not b
  True * b = b
  False * b = False
  abs b = b
  negate = not
  signum = id

demand :: TYPE -> TERM -> VAL
demand y t = v where
  Just v = runReaderT (checkV y t) 0

myNotTyRaw :: TERM
myNotTyRaw = Pi Bit (U Bit)

myNotTy = demand Type myNotTyRaw

myNotRaw :: TERM
myNotRaw = L (U (S (V 0 :/ Cond (U Bit) (B 1) (B 0))))

myNot = demand myNotTy myNotRaw

