module Types4 where

open import Basics public

{-----------------------------------------------------------------------}
-- balanced search trees (based on my ICFP '14 paper
-- How to Keep Your Neighbours in Order


-- but the point here is to watch what the types buy us





















{-----------------------------------------------------------------------}
-- compare natural numbers   {- might we visit Basics.agda? -}

_<=_ : Nat -> Nat -> Set
ze <= y = One
su x <= ze = Zero
su x <= su y = x <= y

{-(-}
cmp : (x y : Nat) -> (x <= y) + (y <= x)
cmp ze y = inl <>
cmp (su x) ze = inr <>
cmp (su x) (su x₁) = cmp x x₁
{-)-}























{-----------------------------------------------------------------------}
-- loose bounds (one good idea, not always obvious)

data Bnd : Set where
  bot : Bnd
  # : Nat -> Bnd
  top : Bnd

_<B=_ : Bnd -> Bnd -> Set
bot <B= _ = One
# x <B= # y = x <= y
_ <B= top = One
_ <B= _ = Zero


-- an interval lets you choose a number that fits in some bounds
data Intv (l u : Bnd) : Set where
  intv : (x : Nat)(lx : l <B= # x)(xu : # x <B= u) -> Intv l u








{-----------------------------------------------------------------------}
-- 2-3-trees, indexed by bounds and height

data T23 (l u : Bnd) : (h : Nat) -> Set where

  leaf : (lu : l <B= u) ->
    T23 l u ze

  node2 : forall {h} x
    (tlx : T23 l (# x) h)(txu : T23 (# x) u h) ->
    T23 l u (su h)

  node3 : forall {h} x y
    (tlx : T23 l (# x) h)(txy : T23 (# x) (# y) h)(tyu : T23 (# y) u h) ->
    T23 l u (su h)








{-----------------------------------------------------------------------}
-- insertion

TooBig : Bnd -> Bnd -> Nat -> Set
TooBig l u h = Sg Nat \ x -> T23 l (# x) h * T23 (# x) u h

{-(-}
insert : forall {h l u} -> Intv l u -> T23 l u h ->
          TooBig l u h + T23 l u h
insert (intv x lx xu) (leaf lu) = {!!}
insert (intv x lx xu) (node2 x₁ t t₁) = {!!}
insert (intv x lx xu) (node3 y z tly tyz tzu) with cmp x y
insert (intv x lx xu) (node3 y z tly tyz tzu) | inl xy with insert (intv x lx xy) tly
insert (intv x lx xu) (node3 y z tly tyz tzu) | inl xy | inl (v , tlv , tvy)
  = inl (y , node2 v tlv tvy , node2 z tyz tzu)
insert (intv x lx xu) (node3 y z tly tyz tzu) | inl xy | inr x₁ = {!!}
insert (intv x lx xu) (node3 y z tly tyz tzu) | inr x₁ = {!!}
{-)-}






















{-----------------------------------------------------------------------}
-- confession








-- it took me about fifteen years to come up with that type for insert
















{-----------------------------------------------------------------------}
-- question (0)




-- how can we make better use of the way types act as "problem statement?"

















{-----------------------------------------------------------------------}
-- question (1)




-- how can we make better use of the way types act as "problem statement?"

   -- programmers should profit from the downpayment and focus on
   --   the actual choices














{-----------------------------------------------------------------------}
-- question (2)




-- how can we make better use of the way types act as "problem statement?"

   -- programmers should profit from the downpayment and focus on
   --   the actual choices

   -- "code" should be a readable record of a problem solving interaction












{-----------------------------------------------------------------------}
-- question (3)




-- how can we make better use of the way types act as "problem statement?"

   -- programmers should profit from the downpayment and focus on
   --   the actual choices

   -- "code" should be a readable record of a problem solving interaction

   -- we need tools to support redesign











{-----------------------------------------------------------------------}
-- an incomplete program is a formal document
