module Bidi (Atom : Set) where

open import Basics
open import SynU

data Dir : Set where chk syn : Dir
  
data Tag : Dir -> Set where
  em cs ab : Tag chk
  am : Atom -> Tag chk
  ra el : Tag syn
    
BiD : {d : Dir} -> Tag d -> Syn One Dir
--   sort  tag      arity
BiD {.chk} em     = ` syn
BiD {.chk} cs     = ` chk *' ` chk
BiD {.chk} ab     = <> >' ` chk
BiD {.chk} (am a) = un'
BiD {.syn} ra     = ` chk *' ` chk
BiD {.syn} el     = ` syn *' ` chk

open TERM Tag BiD (\ _ -> syn)
