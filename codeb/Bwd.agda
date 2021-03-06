module Bwd where

open import Agda.Primitive
open import Basics

infixl 8 _-,_
data Bwd {l}(X : Set l) : Set l where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

module _ {X : Set} where

 data Null : Bwd X -> Set where
   null : Null []

 data Sole (x : X) : Bwd X -> Set where
   sole : Sole x ([] -, x)

 data Env (P : X -> Set) : Bwd X -> Set where
   []   : Env P []
   _-,_ : forall {xz x} -> Env P xz -> P x -> Env P (xz -, x)

 env : forall {P Q} -> [ P -:> Q ] -> [ Env P -:> Env Q ]
 env f [] = []
 env f (pz -, p) = env f pz -, f p

 envExt : forall {P Q : X -> Set}{xz}(pz : Env P xz){f g : [ P -:> Q ]} ->
   (forall {x}(p : P x) -> f p ~ g p) -> env f pz ~ env g pz
 envExt []        q = r~
 envExt (pz -, p) q = _-,_ $~ envExt pz q ~$~ q p

 envComp : forall {P Q R : X -> Set}{xz}(pz : Env P xz)
   {f : [ P -:> Q ]}{g : [ Q -:> R ]}{h : [ P -:> R ]} ->
   (forall {x}(p : P x) -> (f >> g) p ~ h p) ->
   (env f >> env g) pz ~ env h pz
 envComp []        q = r~
 envComp (pz -, p) q = _-,_ $~ envComp pz q ~$~ q p

 envComps : forall {P Q R S : X -> Set}{xz}(pz : Env P xz)
   {f : [ P -:> Q ]}{g : [ Q -:> S ]}{h : [ P -:> R ]}{k : [ R -:> S ]}
   (q : forall {x}(p : P x) -> (f >> g) p ~ (h >> k) p) ->
   (env f >> env g) pz ~ (env h >> env k) pz
 envComps pz {f}{g}{h}{k} q =
   env g (env f pz)          ~[ envComp pz (\ _ -> r~) >
   env (\ p -> g (f p)) pz   ~[ envExt pz q >
   env (\ p -> k (h p)) pz   < envComp pz (\ _ -> r~) ]~
   env k (env h pz) [QED]
  
 env0 : forall {P : X -> Set}{xz yz : Env P []} -> xz ~ yz
 env0 {xz = []} {[]} = r~
