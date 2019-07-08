------------------------------------------------------------------------------
-----                                                                    -----
-----     Lib.Bwd                                                        -----
-----                                                                    -----
------------------------------------------------------------------------------

module Lib.Bwd where

open import Lib.Pi
open import Lib.Sigma
open import Lib.Equality
open import Lib.Index

infixl 8 _-,_
data Bwd {l}(X : Set l) : Set l where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

module _ {X : Set} where

 infixl 8 _+B_
 _+B_ : Bwd X -> Bwd X -> Bwd X
 xz +B [] = xz
 xz +B (yz -, y) = xz +B yz -, y

 data Null : Bwd X -> Set where
   null : Null []

 data Sole (x : X) : Bwd X -> Set where
   sole : Sole x ([] -, x)

 data Env (P : X -> Set) : Bwd X -> Set where
   []   : Env P []
   _-,_ : forall {xz x} -> Env P xz -> P x -> Env P (xz -, x)

 module _ {P : X -> Set} where

  env0 : forall {xz yz : Env P []} -> xz ~ yz
  env0 {xz = []} {[]} = r~

  envBwd : forall {xz} -> Env P xz -> Bwd < P >
  envBwd [] = []
  envBwd (pz -, p) = envBwd pz -, (! p)

  purE : [ P ] -> [ Env P ]
  purE p {[]} = []
  purE p {xz -, x} = purE p -, p

  module _ {Q : X -> Set} where

   env : [ P -:> Q ] -> [ Env P -:> Env Q ]
   env f [] = []
   env f (pz -, p) = env f pz -, f p

   envExt : forall {xz}(pz : Env P xz){f g : [ P -:> Q ]} ->
     (forall {x}(p : P x) -> f p ~ g p) -> env f pz ~ env g pz
   envExt []        q = r~
   envExt (pz -, p) q = _-,_ $~ envExt pz q ~$~ q p

   _$E_ : [ Env (P -:> Q) -:> Env P -:> Env Q ]
   [] $E [] = []
   (fz -, f) $E (pz -, p) = (fz $E pz) -, f p

 module _ {P Q R : X -> Set} where
   
  envComp : forall {xz}(pz : Env P xz)
   {f : [ P -:> Q ]}{g : [ Q -:> R ]}{h : [ P -:> R ]} ->
   (forall {x}(p : P x) -> (f - g) p ~ h p) ->
   (env f - env g) pz ~ env h pz
  envComp []        q = r~
  envComp (pz -, p) q = _-,_ $~ envComp pz q ~$~ q p

 module _ {P Q R S : X -> Set} where
    
  envComps : forall {xz}(pz : Env P xz)
    {f : [ P -:> Q ]}{g : [ Q -:> S ]}{h : [ P -:> R ]}{k : [ R -:> S ]}
    (q : forall {x}(p : P x) -> (f - g) p ~ (h - k) p) ->
    (env f - env g) pz ~ (env h - env k) pz
  envComps pz {f}{g}{h}{k} q =
    env g (env f pz)  ~[ envComp pz (\ _ -> r~) >
    env (f - g) pz    ~[ envExt pz q >
    env (h - k) pz    < envComp pz (\ _ -> r~) ]~
    env k (env h pz)  [QED]
