------------------------------------------------------------------------------
-----                                                                    -----
-----     Lib.Maybe                                                      -----
-----                                                                    -----
------------------------------------------------------------------------------

module Lib.Maybe where

data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no  : Maybe X

_>M=_ : forall {A B} -> Maybe A -> (A -> Maybe B) -> Maybe B
yes a >M= k = k a
no    >M= k = no
