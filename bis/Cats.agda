module Cats where

open import Basics
open import Eq
open import Fun

module _ (O : Set)(_=>_ : O -> O -> Set) where

  record Cat : Set where
    field
      idC : {S : O}     ->  S => S
      coC : {R S T : O} ->  R => S  ->  S => T  ->  R => T
      idcoC : forall {S T}(f : S => T) -> coC idC f == f
      coidC : forall {S T}(f : S => T) -> coC f idC == f
      cocoC : forall {Q R S T}(f : Q => R)(g : R => S)(h : S => T) ->
                coC f (coC g h) == coC (coC f g) h

  data Comp' (s : O) : O -> Set where
    id' : Comp' s s
    co' : forall {t u} -> Comp' s t -> Comp' t u -> Comp' s u
    <_> : forall {t} -> s => t -> Comp' s t

module _ {O : Set}{_=>_ : O -> O -> Set} where

  Co' = Comp' O _=>_

  co^ : forall {r s t} -> Co' r s -> Co' s t -> Co' r t
  co^ f id'       = f
  co^ f (co' g h) = co^ (co^ f g) h
  co^ id'       g = g
  co^ f g         = co' f g

  module _ (C : Cat O _=>_) where
    open Cat C

    module CATSTUFF where

      eval : forall {s t} -> Co' s t -> s => t
      eval < f >     = f
      eval id'       = idC
      eval (co' f g) = coC (eval f) (eval g)
 
      lemma : forall {r s t}(f : Co' r s)(g : Co' s t) ->
        coC (eval f) (eval g) == eval (co^ f g)
      lemma f id'       = coidC (eval f)
      lemma f (co' g h) = 
        coC (eval f) (coC (eval g) (eval h))            =[ cocoC _ _ _ >=
        coC (coC (eval f) (eval g)) (eval h)  =[ coC $= lemma f g =$ _ >=
        coC (eval (co^ f g)) (eval h)             =[ lemma (co^ f g) h >=
        eval (co^ (co^ f g) h)                                      [QED]
      lemma id'       < g > = idcoC g
      lemma (co' f g) < h > = refl
      lemma < f >     < g > = refl
    
      norm : forall {s t} -> Co' s t -> Co' s t
      norm < f > = < f >      
      norm id'       = id'
      norm (co' f g) = co^ (norm f) (norm g)

      nova : forall {s t}(f : Co' s t) -> eval f == eval (norm f)
      nova < f >     = refl
      nova id'       = refl
      nova (co' f g) = 
        coC (eval f) (eval g)               =[ rf coC =$= nova f =$= nova g >=
        coC (eval (norm f)) (eval (norm g))      =[ lemma (norm f) (norm g) >=
        eval (co^ (norm f) (norm g))                                     [QED]

    CAT' : forall {s t} -> Reflector (Co' s t) (s => t)
    CAT' = record { eval = eval ; norm = norm ; nova = nova }
      where open CATSTUFF

Monoid : Set -> Set
Monoid X = Cat One \ _ _ -> X

module _ {O _=>_}(C : Cat O _=>_) where
  open Cat

  _op : Cat O (flip _=>_)
  idC _op = idC C
  coC _op = flip (coC C)
  idcoC _op = coidC C
  coidC _op = idcoC C
  cocoC _op f g h = sym (cocoC C h g f)

module _ {A _A>_ B _B>_}(CA : Cat A _A>_)(CB : Cat B _B>_)(F : A -> B) where
  open Cat
  
  record Functor : Set where
    field
      map   : forall {S T : A} -> S A> T -> F S B> F T
      mapId : forall {S} -> map (idC CA {S}) == idC CB
      mapCo : forall {R S T : A}(f : R A> S)(g : S A> T) ->
        map (coC CA f g) == coC CB (map f) (map g)

module _ {O _=>_}(C : Cat O _=>_) where

  open Cat C

  record Concrete (F : O -> Set) : Set where
    field
      fun : {S T : O} ->  S => T  -> F S -> F T
      funId : {S : O} -> fun (idC {S}) =:= id
      funCo : {R S T : O}(f : R => S)(g : S => T) ->
        fun (coC f g) =:= fun g ` fun f

module _ where

  open Cat
  open Concrete
  
  SM0 : Monoid One
  idC SM0 = _
  coC SM0 = _
  idcoC SM0 _ = refl
  coidC SM0 _ = refl
  cocoC SM0 _ _ _ = refl

  data Sm01 : Two -> Two -> Set where
    id2 : {b : Two} -> Sm01 b b
    f01 : Sm01 #0 #1

  SM01 : Cat Two Sm01
  idC   SM01 = id2
  coC SM01 id2 g = g
  coC SM01 f id2 = f
  idcoC SM01 f = refl
  coidC SM01 id2 = refl
  coidC SM01 f01 = refl
  cocoC SM01 id2 g h = refl
  cocoC SM01 f01 id2 id2 = refl

  Three = Two + One
  data Sm012 : Three -> Three -> Set where
    id3 : {x : Three} -> Sm012 x x
    f01 : Sm012 (#0 , #0) (#0 , #1)
    f12 : Sm012 (#0 , #1) (#1 , <>)
    f02 : Sm012 (#0 , #0) (#1 , <>)

  SM012 : Cat Three Sm012
  idC SM012 = id3
  coC SM012 id3 g = g
  coC SM012 f01 id3 = f01
  coC SM012 f01 f12 = f02
  coC SM012 f12 id3 = f12
  coC SM012 f02 id3 = f02
  idcoC SM012 f = refl
  coidC SM012 id3 = refl
  coidC SM012 f01 = refl
  coidC SM012 f12 = refl
  coidC SM012 f02 = refl
  cocoC SM012 id3 g h = refl
  cocoC SM012 f01 id3 h = refl
  cocoC SM012 f01 f12 id3 = refl
  cocoC SM012 f12 id3 id3 = refl
  cocoC SM012 f02 id3 id3 = refl

  ID : {X : Set}(f : X -> X)(q : (x : X) -> f x == x) -> Concrete SM0 (\ _ -> X)
  fun (ID f q) _ = f
  funId (ID f q) x = q x
  funCo (ID f q) g h x = sym (q (f x))

  FUN : {S T : Set} -> (S -> T) -> Concrete SM01 (S <?> T)
  fun (FUN f) id2 = id
  fun (FUN f) f01 = f
  funId (FUN f) x = refl
  funCo (FUN f) id2 h   x = refl
  funCo (FUN f) f01 id2 x = refl

  TRI : {R S T : Set}(f : R -> S)(g : S -> T)(h : R -> T) ->
        ((r : R) -> h r == g (f r)) ->
        Concrete SM012 (un ((R <?> S) <?> kk T))
  fun (TRI f g h q) id3 = id
  fun (TRI f g h q) f01 = f
  fun (TRI f g h q) f12 = g
  fun (TRI f g h q) f02 = h
  funId (TRI f g h q) _ = refl
  funCo (TRI f g h q) id3 b x = refl
  funCo (TRI f g h q) f01 id3 x = refl
  funCo (TRI f g h q) f01 f12 x = q x
  funCo (TRI f g h q) f12 id3 x = refl
  funCo (TRI f g h q) f02 id3 x = refl


ArrEq : forall {X : Set}(R : X -> X -> Set){x0 x1 y0 y1 : X} ->
  x0 == x1 -> y0 == y1 -> R x0 y0 -> R x1 y1 -> Set
ArrEq R refl refl f g = f == g

module _ {X : Set}(MX : Monoid X){_=>_ : X -> X -> Set}(CX : Cat X _=>_) where

  module M = Cat MX
  module C = Cat CX

  record Monoidal : Set where
    field
      _><_ : forall {S S' T T'} ->
        S => T -> S' => T' -> (M.coC S S') => (M.coC T T')
      moid : forall S S' ->
        (C.idC {S} >< C.idC {S'}) == C.idC {M.coC S S'}
      moco : forall {R R' S S' T T'}
        (f0 : R => S)(g0 : R' => S')
        (f1 : S => T)(g1 : S' => T') ->
        C.coC (f0 >< g0) (f1 >< g1) ==
        (C.coC f0 f1) >< (C.coC g0 g1)
    {- proving these things is hard: do we use them?
      lunitor : forall {S T}(f : S => T) ->
        ArrEq _=>_ (M.idcoC S) (M.idcoC T) (C.idC {M.idC} >< f) f
      runitor : forall {S T}(f : S => T) ->
        ArrEq _=>_ (M.coidC S) (M.coidC T) (f >< C.idC {M.idC}) f
      associator : forall {S0 S1 S2 T0 T1 T2}
        (f0 : S0 => T0)(f1 : S1 => T1)(f2 : S2 => T2) ->
        ArrEq _=>_ (M.cocoC S0 S1 S2) (M.cocoC T0 T1 T2)
          (f0 >< (f1 >< f2)) ((f0 >< f1) >< f2)
    -}
