module Types4Crib where

open import Basics public

_<=_ : Nat -> Nat -> Set
ze <= y = One
su x <= ze = Zero
su x <= su y = x <= y

cmp : (x y : Nat) -> (x <= y) + (y <= x)
cmp ze y = inl <>
cmp (su x) ze = inr <>
cmp (su x) (su y) = cmp x y

data Bnd : Set where
  bot : Bnd
  # : Nat -> Bnd
  top : Bnd

_<B=_ : Bnd -> Bnd -> Set
bot <B= _ = One
# x <B= # y = x <= y
_ <B= top = One
_ <B= _ = Zero

data T23 (l u : Bnd) : Nat -> Set where
  leaf : (lu : l <B= u) -> T23 l u ze
  node2 : forall {h} x
    (tlx : T23 l (# x) h)(txu : T23 (# x) u h) ->
    T23 l u (su h)
  node3 : forall {h} x y
    (tlx : T23 l (# x) h)(txy : T23 (# x) (# y) h)(tyu : T23 (# y) u h) ->
    T23 l u (su h)

data Intv (l u : Bnd) : Set where
  intv : (x : Nat)(lx : l <B= # x)(xu : # x <B= u) -> Intv l u

TooBig : Bnd -> Bnd -> Nat -> Set
TooBig l u h = Sg Nat \ x -> T23 l (# x) h * T23 (# x) u h

insert : forall {h l u} -> Intv l u -> T23 l u h ->
          TooBig l u h + T23 l u h
insert (intv x lx xu) (leaf lu) = inl (x , (leaf lx , leaf xu))
insert (intv x lx xu) (node2 y tly tyu) with cmp x y
insert (intv x lx xu) (node2 y tly tyu) | inl xy with insert (intv x lx xy) tly
insert (intv x lx xu) (node2 y tly tyu) | inl xy | inl (z , tlz , tzu)
  = inr (node3 z y tlz tzu tyu)
insert (intv x lx xu) (node2 y tly tyu) | inl xy | inr tly'
  = inr (node2 y tly' tyu)
insert (intv x lx xu) (node2 y tly tyu) | inr yx with insert (intv x yx xu) tyu
insert (intv x lx xu) (node2 y tly tyu) | inr yx | inl (v , tyv , tvu) = inr (node3 y v tly tyv tvu)
insert (intv x lx xu) (node2 y tly tyu) | inr yx | inr tyv' = inr (node2 y tly tyv')
insert (intv x lx xu) (node3 y z tly tyz tzu) with cmp x y
insert (intv x lx xu) (node3 y z tly tyz tzu) | inl xy with insert (intv x lx xy) tly
insert (intv x lx xu) (node3 y z tly tyz tzu) | inl xy | inl (v , tlv , tvy) = inl (y , node2 v tlv tvy , node2 z tyz tzu)
insert (intv x lx xu) (node3 y z tly tyz tzu) | inl xy | inr tly' = inr (node3 y z tly' tyz tzu)
insert (intv x lx xu) (node3 y z tly tyz tzu) | inr yx with cmp x z
insert (intv x lx xu) (node3 y z tly tyz tzu) | inr yx | inl xz with insert (intv x yx xz) tyz
insert (intv x lx xu) (node3 y z tly tyz tzu) | inr yx | inl xz | inl (v , tyv , tvz)
  = inl (v , node2 y tly tyv , node2 z tvz tzu)
insert (intv x lx xu) (node3 y z tly tyz tzu) | inr yx | inl xz | inr tyz'
  = inr (node3 y z tly tyz' tzu)
insert (intv x lx xu) (node3 y z tly tyz tzu) | inr yx | inr zx with insert (intv x zx xu) tzu
insert (intv x lx xu) (node3 y z tly tyz tzu) | inr yx | inr zx | inl (v , tzv , tvu) = inl (z , node2 y tly tyz , node2 v tzv tvu)
insert (intv x lx xu) (node3 y z tly tyz tzu) | inr yx | inr zx | inr tzu' = inr (node3 y z tly tyz tzu')        
