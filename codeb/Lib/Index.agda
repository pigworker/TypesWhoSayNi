------------------------------------------------------------------------------
-----                                                                    -----
-----     Lib.Index                                                      -----
-----                                                                    -----
------------------------------------------------------------------------------

module Lib.Index where

open import Lib.Pi
open import Lib.Sigma
open import Lib.Sum


------------------------------------------------------------------------------
-- indexed type formers
------------------------------------------------------------------------------

module _ {l}{X : Set l} where

 infixr 1 _-:>_
 infixr 2 _:+_
 infixr 3 _:*_     -- probably need to rejig everything
 _-:>_ _:*_ _:+_ : (S T : X -> Set l) -> X -> Set l
 (S -:> T) x = S x -> T x
 (S :* T) x = S x * T x
 (S :+ T) x = S x + T x


------------------------------------------------------------------------------
-- Molly Metcalfe counting sheep
------------------------------------------------------------------------------

 module _ {k : Level} where
 
  infixr 2 <>\_
  <>\_ : forall {k}{S T : X -> Set l}{P : < S :* T > -> Set k} ->
         ({x : X}(s : S x)(t : T x) -> P (s ^ t)) ->
         (st : < S :* T >) -> P st
  (<>\ f) (s ^ t) = f s t

  YAN Yan : (S : X -> Set l) ->
    ({x : X} -> S x -> Set k) -> Set (lmax k l)
  YAN S T = forall {x}(s : S x) -> T s
  Yan S T = forall {x}{s : S x} -> T s

  TAN Tan : (S T : X -> Set l) ->
    ({x : X} -> S x -> T x -> Set k) -> Set (lmax k l)
  TAN S T U = forall {x}(s : S x)(t : T x) -> U s t
  Tan S T U = forall {x}{s : S x}{t : T x} -> U s t

  TETHER Tether : (S T U : X -> Set l) ->
    ({x : X} -> S x -> T x -> U x -> Set k) -> Set (lmax k l)
  TETHER S T U V = forall {x}(s : S x)(t : T x)(u : U x) -> V s t u
  Tether S T U V = forall {x}{s : S x}{t : T x}{u : U x} -> V s t u
 
