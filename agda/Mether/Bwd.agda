module Bwd where

open import Basics

data Bwd (X : Set) : Set where
  []   : Bwd X
  _-,_ : Bwd X -> X -> Bwd X
infixl 30 _-,_

null : forall {X}(xz : Bwd X) -> Dec (xz ~ [])
null [] = tt , r~
null (xz -, x) = ff , \ ()

_<<<_ : forall {X} -> Bwd X -> Bwd X -> Bwd X
xz <<< [] = xz
xz <<< (yz -, y) = (xz <<< yz) -, y

_>>=_ : forall {S T} -> Bwd S -> (S -> Bwd T) -> Bwd T
[] >>= k = []
(sz -, s) >>= k = (sz >>= k) <<< k s
