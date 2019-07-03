------------------------------------------------------------------------------
-----                                                                    -----
-----     Thin.Select                                                    -----
-----                                                                    -----
------------------------------------------------------------------------------

module Thin.Select where

open import Lib.Bwd
open import Lib.Equality
open import Lib.Pi
open import Lib.Index
open import Lib.Sigma
open import Thin.Data
open import Thin.Triangle

module _ {B : Set} where  -- B is the type of bindings

 open THIN {B}


 module _ {P : B -> Set} where


------------------------------------------------------------------------------
-- using a thinning to select from an environment...
------------------------------------------------------------------------------

  infixr 6 _<?_
 
  _<?_ : forall {ga de} -> ga <= de -> Env P de -> Env P ga
  []        <? [] = []
  (th -, b) <? (pz -, p) = (th <? pz) -, p
  (th -^ b) <? (pz -, p) = th <? pz


------------------------------------------------------------------------------
-- ...makes Env P a contravariant functor from <= to Set...
------------------------------------------------------------------------------

  id<? : forall {ga}(pz : Env P ga) -> idth <? pz ~ pz
  id<? []        = r~
  id<? (pz -, p) = (_-, p) $~ id<? pz

  infix 7 _&<?_
  
  _&<?_ : PreTri \ th ph ps -> th & ph =< ps ->
          (pz : Env P _) -> th <? ph <? pz ~ ps <? pz
  []      &<? []                             = r~
  t -, b  &<? pz -, p = (_-, p) $~ t &<? pz
  t -^, b &<? pz -, p = t &<? pz
  t -^ b  &<? pz -, p = t &<? pz


------------------------------------------------------------------------------
-- ...and is natural in P...
------------------------------------------------------------------------------

 nat<? : forall {P Q : B -> Set}(f : [ P -:> Q ]){ga de}(th : ga <= de) ->
   (pz : Env P de) -> (env f - (th <?_)) pz ~ ((th <?_) - env f) pz
 nat<? f []        []        = r~
 nat<? f (th -, b) (pz -, p) = (_-, f p) $~ nat<? f th pz
 nat<? f (th -^ b) (pz -, p) = nat<? f th pz


