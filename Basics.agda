module Basics where

data Zero : Set where
record One : Set where constructor <>
data Two : Set where tt ff : Two

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 4 _,_ _*_

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x
  
