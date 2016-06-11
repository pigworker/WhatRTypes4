{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TypeOperators, TypeFamilies,
    FlexibleContexts #-}

{-----------------------------------------------------------------------------}
module




  -- What Are

     Types4

  -- Or Are They Only Against?



  -- I am Conor McBride

  -- and the Mathematically Structured Programming group
  -- at the University of Strathclyde, Glasgow, Scotland
  -- is

  where -- I come from.










import Data.Char
import Data.Monoid
import Control.Applicative
import Data.Traversable


{-----------------------------------------------------------------------}
-- a parser for things is...                                 (Fritz Ruehr)

newtype P thing = P {parse :: String -> [(thing, String)]} deriving Monoid

instance Monad P where
  return x = P $ \ s -> return (x, s)
  P pa >>= k = P $ \ s -> do
    (x, s) <- pa s
    parse (k x) s

instance Alternative P where  -- (what if P used Maybe?)
  empty = mempty
  (<|>) = mappend

eat :: (Char -> Bool) -> P Char
eat p = P $ \ s -> case s of
  c : s | p c -> [(c, s)]
  _ -> []

type Cell = Maybe Int

pcell :: P Cell
pcell = many (eat isSpace) *>
  (|Just    (|read (|eat isDigit : (|[]|)|)|)
   |Nothing (- eat (=='.')-)
   |)





{---------------------------------------------------------------------}
-- the functor kit

newtype         I x = I x                 deriving Show
newtype       K a x = K a                 deriving Show
data    (f :*: g) x = f x :*: g x         deriving Show
data    (f :+: g) x = L (f x) | R (g x)   deriving Show
newtype (f :.: g) x = C {unC :: f (g x)}  deriving Show


instance Applicative I where
  pure = I
  I f <*> I s = I (f s)

instance (Applicative f, Applicative g) => Applicative (f :*: g) where
  hiding instance Functor
  pure x = pure x :*: pure x
  (ff :*: gf) <*> (fs :*: gs) = (ff <*> fs) :*: (gf <*> gs)

instance (Applicative f, Applicative g) => Applicative (f :.: g) where
  hiding instance Functor
  pure x = C (|(|x|)|)
  C fgf <*> C fgs = C (|fgf <*> fgs|)

instance Monoid a => Applicative (K a) where
  hiding instance Functor
  pure x = K mempty
  K f <*> K s = K (mappend f s)

-- boring Functor and Traversable instances are elsewhere











instance Traversable (K a) where
  traverse f (K a) = (|(K a)|)
instance Traversable I where
  hiding instance Functor
  traverse f (I x) = (|I (f x)|)
instance (Functor f, Functor g) => Functor (f :*: g) where
  fmap k (fx :*: gx) = fmap k fx :*: fmap k gx
instance (Traversable f, Traversable g) => Traversable (f :*: g) where
  hiding instance Functor
  traverse k (fx :*: gx) = (|traverse k fx :*: traverse k gx|)
instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap k (L fx) = L (fmap k fx)
  fmap k (R gx) = R (fmap k gx)
instance (Traversable f, Traversable g) => Traversable (f :+: g) where
  hiding instance Functor
  traverse k (L fx) = (|L (traverse k fx)|)
  traverse k (R gx) = (|R (traverse k gx)|)
instance (Functor f, Functor g) => Functor (f :.: g) where
  fmap k (C fgx) = C (fmap (fmap k) fgx)
instance (Traversable f, Traversable g) => Traversable (f :.: g) where
  hiding instance Functor
  traverse k (C fgx) = (|C (traverse (traverse k) fgx)|)

{---------------------------------------------------------------------}
-- triples of triples, and their transposes

type Triple = I :*: I :*: I

pattern Tr a b c = I a :*: I b :*: I c

type Zone = Triple :.: Triple

czone :: Zone Char
czone = C (Tr (Tr 'a' 'b' 'c') (Tr 'd' 'e' 'f') (Tr 'g' 'h' 'i'))












{---------------------------------------------------------------------}
-- Newtype piggery-jokery

class Newtype new where
  type Old new
  pack :: Old new -> new
  unpack :: new -> Old new

newly :: (Newtype a, Newtype b) => (Old a -> Old b) -> a -> b
newly f = pack . f . unpack

ala :: (Newtype b, Newtype d) => ((a -> b)     -> c -> d) -> (Old b -> b)
                               -> (a -> Old b) -> c -> Old d
ala hof _ f = unpack . hof (pack . f)

infixl `ala`

instance Newtype ((f :.: g) x) where
  type Old ((f :.: g) x) = f (g x)
  pack = C
  unpack = unC

instance Newtype (Const a x) where
  type Old (Const a x) = a
  pack = Const
  unpack = getConst

instance Newtype (I x) where
  type Old (I x) = x
  pack = I
  unpack (I x) = x

instance Newtype (Product a) where
  type Old (Product a) = a
  pack = Product
  unpack = getProduct

instance Newtype (Sum a) where
  type Old (Sum a) = a
  pack = Sum
  unpack = getSum

instance Newtype Any where
  type Old Any = Bool
  pack = Any
  unpack = getAny

instance Newtype All where
  type Old All = Bool
  pack = All
  unpack = getAll



{-----------------------------------------------------------------------}
-- sudoku boards

type Board = Zone :.: Zone

pboard :: P (Board Cell)
pboard = sequenceA (pure pcell)

tryThis :: String
tryThis = unlines
  ["...23.6.."
  ,"1.......7"
  ,".4...518."
  ,"5.....9.."
  ,"..73.68.."
  ,"..4.....5"
  ,".867...5."
  ,"4.......9"
  ,"..3.62..."
  ]

xpBoard :: Board Cell -> Board Cell
xpBoard = newly sequenceA

boxBoard :: Board Cell -> Board Cell
boxBoard = newly (fmap C . newly (fmap sequenceA) . fmap unC)



















{---------------------------------------------------------------------------}
-- Milner's coincidence (0)



























{---------------------------------------------------------------------------}
-- Milner's coincidence (1)






--                   terms     versus     types




















{---------------------------------------------------------------------------}
-- Milner's coincidence (2)






--                   terms     versus     types
--                 written     versus     inferred





-- but sometimes you write types (e.g. to resolve ambiguity)
-- and sometimes the compiler infers terms (instance dictionaries)













{---------------------------------------------------------------------------}
-- Milner's coincidence (3)






--                   terms     versus     types
--                 written     versus     inferred
--                explicit     versus     invisible




-- are the things you read in the program text always written by you?
-- what if you could have mechanical help?













{---------------------------------------------------------------------------}
-- Milner's coincidence (4.0)






--                   terms     versus     types
--                 written     versus     inferred
--                explicit     versus     invisible
--                 runtime     versus     erasable




-- datakinds give us term-like stuff in erasable things
-- Data.Typeable gives us type representations you can match on at runtime















{---------------------------------------------------------------------------}
-- Milner's coincidence (4.1)






--                   terms     versus     types
--                 written     versus     inferred
--                explicit     versus     invisible
--                 runtime     versus     erasable




-- datakinds give us term-like stuff in erasable things
-- Data.Typeable gives us type representations you can match on at runtime

-- I claim that terms-versus-types and runtime-versus-erasable are
-- orthogonal












{---------------------------------------------------------------------------}
-- Milner's coincidence (4.2)






--                   terms     versus     types
--                 written     versus     inferred
--                explicit     versus     invisible
--                 runtime     versus     erasable




-- datakinds give us term-like stuff in erasable things
-- Data.Typeable gives us type representations you can match on at runtime

-- I claim that terms-versus-types and runtime-versus-erasable are
-- orthogonal

-- Also, I like to write types and get repaid with invisible runtime code










{---------------------------------------------------------------------------}
-- Milner's coincidence (5.0)






--                   terms     versus     types
--                 written     versus     inferred
--                explicit     versus     invisible
--                 runtime     versus     compile time
--                      ->     versus     forall




-- given what people fake up with "singletons" and "proxies", it's clear that
-- more than one quantifier is convenient











{---------------------------------------------------------------------------}
-- Milner's coincidence (5.1)






--                   terms     versus     types
--                 written     versus     inferred
--                explicit     versus     invisible
--                 runtime     versus     erasable
--                      ->     versus     forall




-- given what people fake up with "singletons" and "proxies", it's clear that
-- more than one quantifier is convenient

-- I'm trying to convince the Haskellers to let types depend on runtime values
-- and the dependently typed programmers to let types depend on erasable values










{---------------------------------------------------------------------------}
-- Milner's coincidence (6)






--                   terms     versus     types
--                 written     versus     inferred
--                explicit     versus     invisible
--                 runtime     versus     compile time
--                      ->     versus     forall
--                   input     versus     output





-- but the biggest questionable assumption is that we're working in batch mode














{---------------------------------------------------------------------------}
-- what if...?




-- what if types were a key *input* to the program construction process?

-- let me show you what if





















{------------------------------------------------------------------------}
-- a stray monoid instance, should it prove useful

instance Monoid x => Monoid (IO x) where
  mempty = (|mempty|)
  mappend x y = (|mappend x y|)
  