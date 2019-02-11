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

  redSbst : forall {ga d}{t t' : Term ([] , atom NIL) ga lib d} -> t ~> t' ->
            forall {de}(sg : [ [] , atom NIL ! ga ]/ de) -> (t / sg) ~> (t' / sg)
  redSbst (car t) sg = car (redSbst t sg)
  redSbst (cdr t) sg = cdr (redSbst t sg)
  redSbst (abst t) sg = abst (redSbst t (wksb sg))
  redSbst (thnk (targ e)) sg = thnk (targ (redSbst e sg))
  redSbst (thnk (elim s)) sg = thnk (elim (redSbst s sg) )
  redSbst (thnk {e = ._} (beta x ts Ts ss)) sg = thnk (redSbst (beta x ts Ts ss) sg)
  redSbst (targ e) sg = targ (redSbst e sg) 
  redSbst (elim s) sg = elim (redSbst s sg)
  redSbst (term t) sg = term (redSbst t sg)
  redSbst (type T) sg = type (redSbst T sg)
  redSbst (beta {R} x ts Ts ss) sg
    rewrite plugSbstLemma0 (betaIntro R) ts sg
          | plugSbstLemma0 (betaType R) Ts sg
          | plugSbstLemma0 (betaElim R) ss sg
          | instSbstLemma0 (redTerm R) [] (cons (cons ts Ts) ss) sg
          | instSbstLemma0 (redType R) [] (cons (cons ts Ts) ss) sg
          = beta {R = R} x _ _ _
