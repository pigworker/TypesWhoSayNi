module Bwd where

open import Basics

data Bwd (X : Set) : Set where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

infixl 8 _-,_

module _ {X : Set} where

  data Env (P : X -> Set) : Bwd X -> Set where
    [] : Env P []
    _-,_ : forall {xz x} -> Env P xz -> P x -> Env P (xz -, x)

  env : forall {P Q} -> (forall {x} -> P x -> Q x) ->
          forall {xz} -> Env P xz -> Env Q xz
  env f [] = []
  env f (pz -, p) = env f pz -, f p

  envExt : forall {P Q : X -> Set} ->
           (f g : forall {x} -> P x -> Q x) ->
           (q : forall {x}(p : P x) -> f p == g p) ->
           forall {xz}(pz : Env P xz) -> env f pz == env g pz
  envExt f g q [] = refl
  envExt f g q (pz -, p) = rf _-,_ =$= envExt f g q pz =$= q p

  envComp : forall {P Q R : X -> Set}
    (f : forall {x} -> P x -> Q x)
    (g : forall {x} -> Q x -> R x)
    (h : forall {x} -> P x -> R x)
    (q : forall {x}(p : P x) -> g (f p) == h p)
    {xz}(pz : Env P xz) ->
    env g (env f pz) == env h pz
  envComp f g h q [] = refl
  envComp f g h q (pz -, p) = rf _-,_ =$= envComp f g h q pz =$= q p

  env0 : forall {P : X -> Set}{xz yz : Env P []} -> xz == yz
  env0 {xz = []} {[]} = refl
