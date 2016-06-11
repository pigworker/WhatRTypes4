module TypesMore where

open import Basics
open import Types4

module DESC (I : Set) where

  data Desc : Set1 where
    inx : I -> Desc
    sg  : (A : Set)(D : A -> Desc) -> Desc
    _!_ : I -> Desc -> Desc

  Node : Desc -> (I -> Set) -> I -> Set
  Node (inx x) R i = x == i
  Node (sg A D) R i = Sg A \ a -> Node (D a) R i
  Node (x ! D) R i = R x * Node D R i

  data Mu (D : Desc)(i : I) : Set where
    [_] : Node D (Mu D) i -> Mu D i

  cata : forall D {X} -> ({i : I} -> Node D X i -> X i) ->
           forall {i} -> Mu D i -> X i
  mapCata : forall {D} E {X} -> ({i : I} -> Node D X i -> X i) ->
           forall {i} -> Node E (Mu D) i -> Node E X i
  cata D f [ x ] = f (mapCata D f x)
  mapCata (inx x) f q = q
  mapCata (sg A E) f (a , e) = a , mapCata (E a) f e
  mapCata (i ! E) f (x , e) = cata _ f x , mapCata E f e

  module ORN (J : Set)(ji : J -> I) where

    Hits : I -> Set
    Hits i = Sg J \ j -> ji j == i

    data Orn : Desc -> Set1 where
      inx : forall {i} -> Hits i -> Orn (inx i)
      sg  : forall A {D} -> ((a : A) -> Orn (D a)) -> Orn (sg A D)
      _!_ : forall {i D} -> Hits i -> Orn D -> Orn (i ! D)
      ins : forall (X : Set) {D} -> (X -> Orn D) -> Orn D
      del : forall {A D} a -> Orn (D a) -> Orn (sg A D)

open DESC

NatDesc : Desc One
NatDesc = sg Two \ { tt -> inx <> ; ff -> <> ! inx <> }

NAT : Set
NAT = Mu One NatDesc <>
pattern ZE = [ tt , refl ]
pattern SU n = [ ff , n , refl ]
PLUS : NAT -> NAT -> NAT
PLUS ZE y = y
PLUS (SU x) y = SU (PLUS x y)

open ORN

orned : forall {I D J ji} -> Orn I J ji D -> Desc J
orned (inx (j , q)) = inx j
orned (sg A D) = sg A \ a -> orned (D a)
orned ((j , q) ! O) = j ! orned O
orned (ins X O) = sg X \ x -> orned (O x)
orned (del a O) = orned O

ListOrn : Set -> Orn One One _ NatDesc
ListOrn X = sg Two \
  { tt -> inx (<> , refl)
  ; ff -> ins X \ _ -> (<> , refl) ! (inx (<> , refl))
  }

forget : forall {I D J ji} (O : Orn I J ji D) {P : I -> Set} ->
         {j : J} -> Node J (orned O) (\ j -> P (ji j)) j ->
                    Node I D P (ji j)
forget (inx (j , refl)) refl = refl
forget (sg A O) (a , o) = a , forget (O a) o
forget ((j , refl) ! O) (p , o) = p , forget O o
forget (ins X O) (x , o) = forget (O x) o
forget (del a O) o = a , forget O o

plain : forall {I D J ji} (O : Orn I J ji D)
        {j : J} -> Mu J (orned O) j -> Mu I D (ji j)
plain O = cata _ (orned O) (\ x -> [ forget O {Mu _ _} x ])
