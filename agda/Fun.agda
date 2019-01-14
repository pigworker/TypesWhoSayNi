module Fun where

open import Eq

id : forall {l}{X : Set l} -> X -> X
id x = x

_`_ : forall {i j k}{R : Set i}{S : Set j}{T : Set k} ->
      (S -> T) -> (R -> S) -> R -> T
(f ` g) r = f (g r)
infixl 60 _`_

_=:=_ : forall {k l}{S : Set k}{T : S -> Set l}(f g : (x : S) -> T x) -> Set _
f =:= g = forall x -> f x == g x
infix 10 _=:=_

flip : forall {i j k}{R : Set i}{S : Set j}{T : Set k} ->
       (R -> S -> T) -> S -> R -> T
flip f s r = f r s

kk : forall {k l}{R : Set k}{S : Set l} -> R -> S -> R
kk r _ = r
