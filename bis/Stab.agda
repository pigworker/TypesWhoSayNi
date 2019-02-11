module Stab where

open import Basics
open import Eq
open import Atom
open import Bwd
open import All
open import Pat
open import Term
open import Deriv
open import Thin
open import ActCats

module _ where
  open BetaRule
  
  redThin : forall {ga d}{t t' : Term ([] , atom NIL) ga lib d} -> t ~> t' ->
            forall {de}(th : ga <= de) -> (t ^ th) ~> (t' ^ th)
  redThin (car t) th = car (redThin t th)
  redThin (cdr t) th = cdr (redThin t th)
  redThin (abst t) th = abst (redThin t (th su))
  redThin (thnk {e = e} n) th rewrite Act.actThunk THIN e (refl , th)
    = thnk (redThin n th)
  redThin (targ e) th = targ (redThin e th)
  redThin (elim s) th = elim (redThin s th)
  redThin (term t) th = term (redThin t th)
  redThin (type T) th = type (redThin T th)
  redThin (beta {R} x ts Ts ss) th
    rewrite plugThinLemma (betaIntro R) ts th
          | plugThinLemma (betaType R) Ts th
          | plugThinLemma (betaElim R) ss th
          | instThinLemma (redTerm R) [] (cons (cons ts Ts) ss) th
          | instThinLemma (redType R) [] (cons (cons ts Ts) ss) th
          = beta {R = R} x _ _ _

