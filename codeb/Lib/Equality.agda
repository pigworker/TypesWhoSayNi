------------------------------------------------------------------------------
-----                                                                    -----
-----     Lib.Equality                                                   -----
-----                                                                    -----
------------------------------------------------------------------------------

module Lib.Equality where

open import Lib.Pi
open import Lib.Sigma

module _ {l}{X : Set l} where


------------------------------------------------------------------------------
-- the relation and its constructor
------------------------------------------------------------------------------

 infix 3 _~_
 
 data _~_ (x : X) : X -> Set l where
   r~ : x ~ x

{-
I've been astonished how much horizontal space I save by adopting a one
character operator for equality. Given that the system has taken =, the
adoption of ~ seems like the next best.
-}


------------------------------------------------------------------------------
-- equivalence closure
------------------------------------------------------------------------------

 infix 40 _-~-_
 infix 41 _~o

 _~o : forall {x y} -> x ~ y -> y ~ x                 -- symmetry
 r~ ~o = r~

 _-~-_ : forall {x y z} -> x ~ y -> y ~ z -> x ~ z    -- transitivity
 r~ -~- q = q

{-
For short inline proofs, composing equational assumptions, it's ok to use
these operations which foreground the proof objects. Symmetry has higher
priority, so it can be used without parens in transitivity.
-}


------------------------------------------------------------------------------
-- derivation style
------------------------------------------------------------------------------

 infixr 30 _~[_>_ _<_]~_
 infixr 31 _[QED]

 _~[_>_ : forall x {y z} -> x ~ y -> y ~ z -> x ~ z
 x ~[ q0 > q1 = q0 -~- q1

 _<_]~_ : forall x {y z} -> y ~ x -> y ~ z -> x ~ z
 x < q0 ]~ q1 = q0 ~o -~- q1

 _[QED] : forall x -> x ~ x
 x [QED] = r~

{-
Longer, more involved proofs require clearer awareness of the terms being
related by the proofs. I write proofs like

      thing0         ~[ proof01 >
      thing1         < proof02 ]~
      thing2         [QED]

to give a proof of thing0 ~ thing2, showing the stages of my reasoning.
-}


------------------------------------------------------------------------------
-- applicative style
------------------------------------------------------------------------------

rf : forall {k}{X : Set k} (x : X) -> x ~ x
rf x = r~

module _ {k l}{X : Set k}{Y : Set l} where
 
 infixl 2 _~$~_ _$~_ _~$   -- "associating to the left, rather as we all did
                           -- in the sixties" (Roger Hindley)
  
 _~$~_ : {f g : X -> Y}{a b : X} -> f ~ g -> a ~ b -> f a ~ g b
 r~ ~$~ r~ = r~
  
 _$~_ : {a b : X}            (f : X -> Y) -> a ~ b -> f a ~ f b
 f $~ q = rf f ~$~ q

 _~$ : {f g : X -> Y}{a : X} ->     f ~ g          -> f a ~ g a
 f ~$ = f ~$~ r~

{-
In the pre-cubical era, it's useful to adopt a combinator style for proving
equations between applicative (often, constructor) forms. E.g., if

  q0 : x0 ~ y0, q1 : x1 ~ y1

then

  f $- q0 ~$~ q1 ~$ : f x0 y0 z ~ f x1 y1 z
-}


------------------------------------------------------------------------------
-- type transportation
------------------------------------------------------------------------------

module _ {l}{S T : Set l} where

 _:[_> : S -> S ~ T -> T
 s :[ r~ > = s

 <_]:_ : S ~ T -> T -> S
 < r~ ]: s = s

{-
These ship values between equal types, e.g., if xs : Vec X (m +N n), then I
might well have

  xs :[ Vec X $- comm+N m n > : Vec X (n +N m)
-}


------------------------------------------------------------------------------
-- pointwise equality
------------------------------------------------------------------------------

module _ {l}{X Y : Set l} where

 _~:~_ : (f g : X -> Y) -> Set l
 f ~:~ g = forall x -> f x ~ g x
 

------------------------------------------------------------------------------
-- injectivity, surjectivity, isomorphism
------------------------------------------------------------------------------

module _ {l}{X Y : Set l}(f : X -> Y) where

 Injective Surjective Iso :  Set l

 Injective   = forall x y -> f x ~ f y -> x ~ y
 Surjective  = forall y -> < f - (_~ y)>
 Iso         = Injective * Surjective

module _ {l}(X Y : Set l) where

 record _`->_ : Set l where
   field
     inj        : X -> Y
     injective  : Injective inj
 open _`->_ public

 record _->>_ : Set l where
   field
     sur         : X -> Y
     surjective  : Surjective sur
 open _->>_ public

 record _<~>_ : Set l where
   field
     iso    : X -> Y
     isoInj : Injective iso
     isoSur : Surjective iso
   inv : Y -> X
   inv y = fst (isoSur y)
   iso-inv : (iso - inv) ~:~ id
   iso-inv x with isoSur (iso x)
   ... | x' , q = isoInj x' x q
   inv-iso : (inv - iso) ~:~ id
   inv-iso y = isoSur y .snd

module _ {l}{X Y : Set l}(f : X <~> Y) where
 open _<~>_

 flip<~> : Y <~> X
 iso    flip<~> = inv f
 isoInj flip<~> y z q = 
   y                  < inv-iso f y ]~
   (inv f - iso f) y  ~[ iso f $~ q >
   (inv f - iso f) z  ~[ inv-iso f z >
   z  [QED]
 isoSur flip<~> x = iso f x , iso-inv f x


------------------------------------------------------------------------------
-- register the builtin, to enable rewrite
------------------------------------------------------------------------------

{-# BUILTIN EQUALITY _~_ #-}
