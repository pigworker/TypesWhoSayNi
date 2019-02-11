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

CxThin : forall {ga de}(th : ga <= de) -> Context ga -> Context de -> Set
CxThin th Ga De = all (_^ th) Ga == select th De

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

  open FormationRule
  open CheckingRule
  open EliminationRule
  open UniverseRule

  derThin : forall {ga}{Ga : Context ga}{J : Judgement ga} -> Ga != J ->
            forall {de}{De : Context de}(th : ga <= de) -> CxThin th Ga De ->
            De != (J ^J th)
  premsThin : forall {ga}{Ga : Context ga}{gas inp suj0 tru suj1}
              (Pz : Premises gas inp suj0 tru suj1)
              (sgs : [ ([] , atom NIL) ! gas ]/ ga)
              (inps : Env ([] , atom NIL) (ga ,P inp))
              (sujs0 : Env ([] , atom NIL) (ga ,P suj0)) ->
              let Jz , trus , sujs1 = premises ga Pz sgs inps sujs0 in
              All (Ga !=_) Jz ->
              forall {de}{De : Context de}(th : ga <= de) -> CxThin th Ga De ->
              let Jz' , trus' , sujs1' = premises de Pz
                    (all (_^ th) sgs) (inps ^E th) (sujs0 ^E th) in
              All (De !=_) Jz' * trus' == (trus ^E th) * sujs1' == (sujs1 ^E th)
  premThin : forall {ga}{gas inp tru suj xi tr' suj'}{Ga : Context (ga -+ xi)}
    (P : Premise gas inp tru suj xi tr' suj')
    (sgs : [ ([] , atom NIL) ! gas ]/ ga)
    (inps : Env ([] , atom NIL) (ga ,P inp))
    (trus : Env ([] , atom NIL) (ga ,P tru))
    (sujs0 : Env ([] , atom NIL) (ga ,P suj)) ->
    let J , trs , sujs1 = premise ga P sgs inps trus sujs0 in
    Ga != J ->
    forall {de}{De : Context (de -+ xi)}(th : ga <= de) ->
    CxThin (th ^+ oi {S = xi}) Ga De ->
    let J' , trs' , sujs1' = premise de P
         (all (_^ th) sgs) (inps ^E th) (trus ^E th) (sujs0 ^E th) in
    (De != J') * trs' == ActWeak.acte THINWEAK trs th * (sujs1' == (sujs1 ^E th))
    
  derThin {Ga = Ga}(extend {S = S} d) {De = De} th Th
    with derThin d {De = all (_^ (oi no)) De -, ((S ^ th) ^ (oi no))} (th su)
      (_-,_
        $= (all (_^ (th su)) (all (_^ (oi no)) Ga)
              =[ icompoLemma THINTHINTHIN THINTHINTHIN _ _ _ _
                ((refl ,_) $= (_no $= oiLemma th)) Ga >=
            all (_^ (oi no)) (all (_^ th) Ga)
              =[ all (_^ (oi no)) $= Th >=
            all (_^ (oi no)) (select th De)
              =< selectAll th (_^ (oi no)) De ]=
            select th (all (_^ (oi no)) De)
              [QED])
        =$= pointCompo THINTHINTHIN THINTHINTHIN _ _ _ _ S
              ((refl ,_) $= (_no $= oiLemma th)))
  ... | d' = extend d'
  derThin {Ga = Ga} (var {x = x}) {De = De} th Th 
    rewrite sym (top $= selectAll x (_^ th) Ga) | Th
          | sym (POLYSELECT.funCo th x De) = var
  derThin (thunk {n = n} d0 d1) th Th
    rewrite Act.actThunk THIN n (refl , th)
          = thunk {n = n ^ th} (derThin d0 th Th) (derThin d1 th Th)
  derThin (unis {n = n} d0 d1) th Th
    rewrite Act.actThunk THIN n (refl , th)
          = unis {n = n ^ th} (derThin d0 th Th) (derThin d1 th Th)
  derThin (rad d0 d1)            th Th = rad (derThin d0 th Th) (derThin d1 th Th)
  derThin eq                     th Th = eq
  derThin (pre x d)              th Th = pre (redThin x th) (derThin d th Th)
  derThin (post d x)             th Th = post (derThin d th Th) (redThin x th)
  derThin (type {R} rule Ts dz)  th Th
    rewrite plugThinLemma (typeSuj R) Ts th
    = let dz' , _ , _ = premsThin (typePrems R) [] (atom NIL) Ts dz th Th in
      type rule (Ts ^E th) dz'
  derThin (chk {R} rule Ts ts dz)     th Th
    rewrite plugThinLemma (chkInp R) Ts th | plugThinLemma (chkSuj R) ts th
    = let dz' , _ , _ = premsThin (chkPrems R) [] Ts ts dz th Th in 
      chk rule (Ts ^E th) (ts ^E th) dz'
  derThin {ga} (elir {R} rule e Ss ss d dz) {de}{De} th Th
    with elir rule {Ga = De} (e ^ th) (Ss ^E th) (ss ^E th) | derThin d th Th
  ... | ready | d'
    with premises ga (elimPrems R) ([] -, e) Ss ss
       | premises de (elimPrems R) ([] -, (e ^ th)) (Ss ^E th) (ss ^E th)
       | premsThin (elimPrems R) ([] -, e) Ss ss dz th Th
  ... | Jz , trus , sujs | Jz' , ._ , ._ | dz' , refl , refl
    rewrite plugThinLemma (trgType R) Ss th
          | plugThinLemma (elimSuj R) ss th
          | instThinLemma (resType R) ([] -, e) trus th
      = ready d' dz'
  derThin (unic {R} rule Ts dz)       th Th
    rewrite plugThinLemma (uniInp R) Ts th
    = let dz' , _ , _ = premsThin (uniPrems R) [] Ts (atom NIL) dz th Th in
      unic rule (Ts ^E th) dz'
  
  premsThin [] sgs inpz sujs0 [] th Th = [] , refl , refl
  premsThin {ga} (Pz -, P) sgs inps sujs0 (dz -, d) {de} th Th
    with premises ga Pz sgs inps sujs0
       | premises de Pz (all (_^ th) sgs) (inps ^E th) (sujs0 ^E th)
       | premsThin Pz sgs inps sujs0 dz th Th
  ... | Jz , trus , sujs1 | Jz' , ._ , ._ | dz' , refl , refl
    with premise ga P sgs inps trus sujs1
       | premise de P (all (_^ th) sgs) (inps ^E th) (trus ^E th) (sujs1 ^E th)
       | premThin P sgs inps trus sujs1 d th Th
  ... | J , tr , sujs2 | J' , ._ , ._ | d' , refl , refl
      = (dz' -, d') , refl , refl

  premThin (S !- P) sgs inps trus sujs0 d th Th = {!!}
  premThin {xi = xi} (type (ps , T , ph)) sgs inps trus sujs0 d th Th
    with derThin d (th ^+ oi {S = xi}) Th
  ... | d' = {!!} , {!!} , {!!}
  premThin (T :> t) sgs inps trus sujs0 d th Th = {!!}
  premThin (univ T) sgs inps trus sujs0 d th Th = {!!}
  premThin (tyeq S T) sgs inps trus sujs0 d th Th = {!!}
