------------------------------------------------------------------------------
-----                                                                    -----
-----     Thin.Partition                                                 -----
-----                                                                    -----
------------------------------------------------------------------------------

module Thin.Partition where

open import Lib.Bwd
open import Lib.Equality
open import Lib.Pi
open import Lib.Index
open import Lib.Sigma
open import Lib.Sum
open import Thin.Data
open import Thin.Triangle
open import Thin.Square
open import Thin.Cover
open import Thin.Pullback

module _ {B : Set} where  -- B is the type of bindings

 open THIN {B}

 Part : forall {ga0 ga ga1}(th : ga0 <= ga)(ph : ga1 <= ga) -> Set
 Part th ph = th /u\ ph * Pullback (no& th ^ no& ph)

 
