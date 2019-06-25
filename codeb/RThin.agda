module RThin {X : Set} where

open import Basics
open import Bwd

OPE : Bwd X -> Bwd X -> Set
OPE [] jz = One
OPE (iz -, i) [] = Zero
OPE (iz -, i) (jz -, j)
  = (OPE (iz -, i) jz)
  + (OPE iz jz * (i == j))

record _<=_ (iz jz : Bwd X) : Set where
  constructor ope
  field
    epo : OPE iz jz

_<,_ : forall {iz jz} -> iz <= jz -> forall k -> (iz -, k) <= (jz -, k)
ope th <, k = ope (inr (th , refl))

_<^_ : forall {iz jz} -> iz <= jz -> forall k -> iz <= (jz -, k)
_<^_ {[]} th k = _
_<^_ {iz -, i} (ope th) k = ope (inl th)

data Tri : forall {iz jz kz} ->
  iz <= jz -> jz <= kz -> iz <= kz -> Set where
  []     : Tri {[]}{[]}{[]} _ _ _
  _-,_ : forall {iz jz kz}
    {th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
    Tri th ph ps -> forall k -> 
    Tri (th <, k) (ph <, k) (ps <, k)
  _-^,_ : forall {iz jz kz}
    {th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
    Tri th ph ps -> forall k -> 
    Tri (th <^ k) (ph <, k) (ps <^ k)
  _-^_ : forall {iz jz kz}
    {th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
    Tri th ph ps -> forall k ->
    Tri th (ph <^ k) (ps <^ k)

opec : forall iz jz kz -> OPE iz jz -> OPE jz kz -> OPE iz kz
opec [] _ _ _ _ = _
opec (_ -, _) [] _ () _
opec (_ -, _) (_ -, _) [] _ ()
opec (iz -, i) (jz -, j) (kz -, k)
  th (inl ph)
  = inl (opec (iz -, i) (jz -, j) kz th ph)
opec (iz -, i) (jz -, j) (kz -, .j)
  (inl th) (inr (ph , refl))
  = inl (opec (iz -, i) jz kz th ph)
opec (iz -, .j) (jz -, j) (kz -, .j)
  (inr (th , refl)) (inr (ph , refl))
  = inr (opec iz jz kz th ph , refl)

_-<-_ : forall {iz jz kz} -> iz <= jz -> jz <= kz -> iz <= kz
ope th -<- ope ph = ope (opec _ _ _ th ph)

mkTri : forall {iz jz kz}(th : iz <= jz)(ph : jz <= kz) ->
  Tri th ph (th -<- ph)
mkTri {[]} {[]} {[]} (ope <>) (ope <>) = []
mkTri {[]} {[]} {kz -, k} (ope <>) (ope <>)
  = mkTri {[]} {[]} {kz} _ _ -^ k
mkTri {[]} {jz -, j} {[]} (ope <>) (ope ())
mkTri {[]} {jz -, j} {kz -, k} (ope <>) (ope (inl ph))
  = mkTri {[]} {jz -, j} {kz} _ (ope ph) -^ k
mkTri {[]} {jz -, j} {kz -, .j} (ope <>) (ope (inr (ph , refl)))
  = mkTri {[]}{jz}{kz} _ (ope ph) -^, j
mkTri {iz -, x} {jz} {kz} th ph = {!!}
