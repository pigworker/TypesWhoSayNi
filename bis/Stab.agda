module Stab where

open import Basics
open import Eq
open import Cats
open import Atom
open import Bwd
open import All
open import Pat
open import Term
open import Deriv
open import Thin
open import ActCats

diagSgTh : forall {M ga de}(sg : [ M ! ga ]/ de){ps xi}
           (ph : ps <= xi) ->
           all (_^ (oi ^+ ph)) (sg >/< idsb {ps}) ==
           select (oi ^+ ph) (sg >/< idsb {xi})
diagSgTh {M}{ga}{de} sg {ps}{xi} ph = 
  all (_^ (oi ^+ ph)) (sg >/< idsb {ps})
    =[ allCat (_^ (oi ^+ ph)) (all _ sg) (all _ idsb) >=
  all (_^ (oi ^+ ph)) (all (_^ thinl oi ps) sg) :+
  all (_^ (oi ^+ ph)) (all (_^ thinr de oi) (idsb {ps}))
    =[ _:+_ $= (all (_^ (oi ^+ ph)) (all (_^ thinl oi ps) sg)
                 =< allCo _ _ _ (\ t -> 
                    t ^ thinl oi xi
                      =< (t ^_) $= ((thinl oi ps -< (oi ^+ ph))
                                      =[ Monoidal.moco OPEMON oi oe oi ph >=
                                     (oi -< oi) ^+ (oe -< ph)
                                      =[ _^+_ $= POLYTHIN.idcoC _
                                             =$= oeU (oe -< ph) oe >=
                                     thinl oi xi
                                      [QED]) ]=
                    t ^ (thinl oi ps -< (oi ^+ ph))
                      =< thinco t _ _ ]=
                    (t ^ thinl oi ps) ^ (oi ^+ ph)
                      [QED]) sg ]=
               all (_^ thinl oi xi) sg
                 =< POLYSELECT.funId _ ]=
               select oi (all (_^ thinl oi xi) sg)
                 [QED])
           =$= (all (_^ (oi ^+ ph)) (all (_^ thinr de oi) (idsb {ps}))
                 =< allCo _ _ _ (\ t -> 
                     t ^ (ph -< thinr de oi)
                       =[ (t ^_) $= (ph -< thinr de oi
                                      =[ thinrAmmel ph oi >=
                                     thinr de (ph -< oi)
                                      =< thinr de $= oiLemma ph ]=
                                     thinr de (oi -< ph)
                                      =< thinrLemma oi oi ph ]=
                                     thinr de oi -< (oi ^+ ph)
                                      [QED]) >=
                     t ^ (thinr de oi -< (oi ^+ ph))
                       =< thinco t _ _ ]=
                     (t ^ thinr de oi) ^ (oi ^+ ph)
                       [QED]
                    ) idsb ]=
                all (_^ (ph -< thinr de oi)) idsb
                 =< selIdsb (ph -< thinr de oi) ]=
                select (ph -< thinr de oi) (idsb {de -+ xi})
                 =[ POLYSELECT.funCo (thinr de (oi {S = xi})) ph idsb >=
                select ph (select (thinr de oi) (idsb {de -+ xi}))
                 =[ select ph $= selIdsb (thinr de oi) >=
                select ph (all (_^ thinr de oi) (idsb {xi}))
                  [QED]) >=
  select oi (all (_^ thinl oi xi) sg) :+
    select ph (all (_^ thinr de oi) (idsb {xi}))
    =< selCat oi ph (all _ sg) (all _ idsb) ]=
  select (oi ^+ ph) (sg >/< idsb {xi})
    [QED]


CxThin : forall {ga de}(th : ga <= de) ->
  Context ([] , NIL) ga -> Context ([] , NIL) de -> Set
CxThin th Ga De = all (_^ th) Ga == select th De

module STABTHIN (TH : TypeTheory) where
  open TYPETHEORY TH
  open BetaRule
  
  redThin : forall {M ga d}{t t' : Term M ga lib d} -> t ~> t' ->
            forall {de}(th : ga <= de) -> (t ^ th) ~> (t' ^ th)
  redThinz : forall {M ga ga'}{ez ez' : All (\ _ -> Term M ga lib syn) ga'} ->
             ez ~z> ez' ->
            forall {de}(th : ga <= de) ->
            Act.actz THIN ez (refl , th) ~z> Act.actz THIN ez' (refl , th)
  redThin (car t) th = car (redThin t th)
  redThin (cdr t) th = cdr (redThin t th)
  redThin (abst t) th = abst (redThin t (th su))
  redThin (thnk {e = e} n) th rewrite Act.actThunk THIN e (refl , th)
    = thnk (redThin n th)
  redThin (targ e) th = targ (redThin e th)
  redThin (elim s) th = elim (redThin s th)
  redThin (term t) th = term (redThin t th)
  redThin (type T) th = type (redThin T th)
  redThin (meta ez) th = meta (redThinz ez th)
  redThin (beta {R} x ts Ts ss) th
    rewrite plugThinLemma (betaIntro R) ts th
          | plugThinLemma (betaType R) Ts th
          | plugThinLemma (betaElim R) ss th
          | instThinLemma (redTerm R) [] (cons (cons ts Ts) ss) th
          | instThinLemma (redType R) [] (cons (cons ts Ts) ss) th
          = beta {R = R} x _ _ _
  redThinz (llll ez) th = llll (redThinz ez th)
  redThinz (rrrr e) th = rrrr (redThin e th)

  redSbst : forall {M ga d}{t t' : Term M ga lib d} -> t ~> t' ->
            forall {de}(sg : [ M ! ga ]/ de) -> (t / sg) ~> (t' / sg)
  redSbstz : forall {M ga ga'}{ez ez' : All (\ _ -> Term M ga lib syn) ga'} ->
             ez ~z> ez' ->
            forall {de}(sg : [ M ! ga ]/ de) ->
            Act.actz SBST ez (refl , sg) ~z> Act.actz SBST ez' (refl , sg)
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
  redSbst (meta ez) sg = meta (redSbstz ez sg)
  redSbst (beta {R} x ts Ts ss) sg
    rewrite plugSbstLemma0 (betaIntro R) ts sg
          | plugSbstLemma0 (betaType R) Ts sg
          | plugSbstLemma0 (betaElim R) ss sg
          | instSbstLemma0 (redTerm R) [] (cons (cons ts Ts) ss) sg
          | instSbstLemma0 (redType R) [] (cons (cons ts Ts) ss) sg
          = beta {R = R} x _ _ _
  redSbstz (llll ez) sg = llll (redSbstz ez sg)
  redSbstz (rrrr e) sg = rrrr (redSbst e sg)

  open FormationRule
  open CheckingRule
  open EliminationRule
  open UniverseRule
  open Monoidal (OPEMON {One})

  derThin : forall {ga}{Ga : Context  ([] , NIL) ga}
                   {J : Judgement ([] , NIL) ga} ->
            Ga != J ->
            forall {de}{De : Context ([] , NIL) de}(th : ga <= de) ->
            CxThin th Ga De ->
            De != (J ^J th)
  premsThin : forall {ga}{Ga : Context ([] , NIL) ga}{gas inp suj0 tru suj1}
              (Pz : Premises gas inp suj0 tru suj1)
              (sgs : [ ([] , NIL) ! gas ]/ ga)
              (inps : Env ([] , NIL) (ga ,P inp))
              (sujs0 : Env ([] , NIL) (ga ,P suj0)) ->
              let Jz , trus , sujs1 = premises ga Pz sgs inps sujs0 in
              All (Ga !=_) Jz ->
              forall {de}{De : Context ([] , NIL) de}(th : ga <= de) ->
              CxThin th Ga De ->
              let Jz' , trus' , sujs1' = premises de Pz
                    (all (_^ th) sgs) (inps ^E th) (sujs0 ^E th) in
              All (De !=_) Jz' * trus' == (trus ^E th) * sujs1' == (sujs1 ^E th)
  premThin : forall {ga}{gas inp tru suj xi tr' suj'}
    {Ga : Context ([] , NIL) (ga -+ xi)}
    (P : Premise gas inp tru suj xi tr' suj')
    (sgs : [ ([] , NIL) ! gas ]/ ga)
    (inps : Env ([] , NIL) (ga ,P inp))
    (trus : Env ([] , NIL) (ga ,P tru))
    (sujs0 : Env ([] , NIL) (ga ,P suj)) ->
    let J , trs , sujs1 = premise ga P sgs inps trus sujs0 in
    Ga != J ->
    forall {de}{De : Context ([] , NIL) (de -+ xi)}(th : ga <= de) ->
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
    = let dz' , _ , _ = premsThin (typePrems R) [] NIL Ts dz th Th in
      type rule (Ts ^E th) dz'
  derThin (chk {R} rule Ts ts dz)     th Th
    rewrite plugThinLemma (chkInp R) Ts th | plugThinLemma (chkSuj R) ts th
    = let dz' , _ , _ = premsThin (chkPrems R) [] Ts ts dz th Th in 
      chk rule (Ts ^E th) (ts ^E th) dz'
  derThin {ga} (elir {R} rule e Ss ss d dz) {de}{De} th Th
    with elir rule (e ^ th) (Ss ^E th) (ss ^E th) | derThin d th Th
  ... | ready | d'
    with premises ga (elimPrems R) ([] -, e) Ss ss
       | premises de (elimPrems R) ([] -, (e ^ th)) (Ss ^E th) (ss ^E th)
       | premsThin (elimPrems R) ([] -, e) Ss ss dz th Th
  ... | Jz , trus , sujs | Jz' , ._ , ._ | dz' , refl , refl
    rewrite plugThinLemma (trgType R) Ss th
          | plugThinLemma (elimSuj R) ss th
          | instThinLemma (resType R) ([] -, e) (cons Ss trus) th
      = ready d' dz'
  derThin (unic {R} rule Ts dz)       th Th
    rewrite plugThinLemma (uniInp R) Ts th
    = let dz' , _ , _ = premsThin (uniPrems R) [] Ts NIL dz th Th in
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

  premThin {xi = xi} {Ga = Ga} (S !- P) sgs inps trus sujs0 (extend d) {De = De} th Th
    with premThin P sgs inps trus sujs0 d
          {De = all (_^ (oi no)) De -,
            ((S % (all (_^ th) sgs , cons (inps ^E th) (trus ^E th))) ^ (oi no))} th
          (_-,_ $= (all (_^ ((th ^+ oi {S = xi}) su)) (all (_^ (oi no)) Ga)
                     =[ icompoLemma THINTHINTHIN THINTHINTHIN _ _ _ _
                         ((refl ,_) $= (_no $= oiLemma _)) Ga >=
                    all (_^ (oi no)) (all (_^ (th ^+ oi {S = xi})) Ga)
                     =[ all (_^ (oi no)) $= Th >=
                    all (_^ (oi no)) (select (th ^+ oi {S = xi}) De)
                     =< selectAll (th ^+ oi {S = xi}) (_^ (oi no)) De ]=
                    select (th ^+ oi {S = xi}) (all (_^ (oi no)) De)
                     [QED])
            =$= (((S % (sgs , cons inps trus)) ^ (oi no)) ^ ((th ^+ oi {S = xi}) su)
                   =[ pointCompo THINTHINTHIN THINTHINTHIN _ _ _ _
                      (S % (sgs , cons inps trus)) ((refl ,_) $= (_no $= oiLemma _)) >=
                 ((S % (sgs , cons inps trus)) ^ (th ^+ oi {S = xi})) ^ (oi no)
                   =[ (_^ (oi no)) $= instThinLemma S sgs (cons inps trus) th >=
                 (S % (all (_^ th) sgs , cons (inps ^E th) (trus ^E th))) ^ (oi no)
                   [QED]))
  ... | d' , q0 , q1
    = extend d' , abst $= q0 , q1
  premThin {ga}{xi = xi} (type (ps , T , ph)) sgs inps trus sujs0 d {de = de} th Th
    with derThin d (th ^+ oi {S = xi}) Th | removeThin T sujs0 th
  ... | d' | q0 , q1
    rewrite q0 | q1
    | pointCompo THINTHINTHIN THINTHINTHIN
      (refl , (th ^+ oi {S = ps})) (refl , (oi {S = de} ^+ ph))
      (refl , (oi {S = ga} ^+ ph)) (refl , (th ^+ oi {S = xi}))
      (fst (remove ga T sujs0)) ((refl ,_) $= diag th ph)
    = d' , refl , refl
  premThin {ga}{xi = xi} (T :> (ps , t , ph)) sgs inps trus sujs0 d {de = de} th Th
    with derThin d (th ^+ oi {S = xi}) Th | removeThin t sujs0 th
  ... | d' | q0 , q1
    rewrite instThinLemma T sgs (cons inps trus) th | q0 | q1
    | pointCompo THINTHINTHIN THINTHINTHIN
      (refl , (th ^+ oi {S = ps})) (refl , (oi {S = de} ^+ ph))
      (refl , (oi {S = ga} ^+ ph)) (refl , (th ^+ oi {S = xi}))
      (fst (remove ga t sujs0)) ((refl ,_) $= diag th ph)
    = d' , refl , refl  
  premThin {xi = xi} (univ T) sgs inps trus sujs0 d th Th
    with derThin d (th ^+ oi {S = xi}) Th
  ... | d' rewrite instThinLemma T sgs (cons inps trus) th = d' , refl , refl
  premThin {xi = xi} (tyeq S T) sgs inps trus sujs0 d th Th
    with derThin d (th ^+ oi {S = xi}) Th
  ... | d' rewrite instThinLemma S sgs (cons inps trus) th
                 | instThinLemma T sgs (cons inps trus) th
      = d' , refl , refl

theUsualShoogle :
  forall {M d ga de}(t : Term M ga lib d)
    (sg : [ M ! ga ]/ de)(e : Term M (de -, <>) lib syn)->
    (t ^ (oi no)) / (all (_^ (oi no)) sg -, e) ==
    (t / sg) ^ (oi no)
theUsualShoogle t sg e = 
  (t ^ (oi no)) / (all (_^ (oi no)) sg -, e)
    =[ pointCompo THINSBSTSBST SBSTTHINSBST _ _ _ _ t
       ((refl ,_) $= POLYSELECT.funId _) >=
  (t / sg) ^ (oi no)
    [QED]

_/J_ : forall {ga}(J : Judgement ([] , NIL) ga){de}(sg : [ [] , NIL ! ga ]/ de) ->
       Judgement ([] , NIL) de
(S !- J) /J sg = (S / sg) !- (J /J wksb sg)
type T   /J sg = type (T / sg)
univ T   /J sg = univ (T / sg)
(T :> t) /J sg = (T / sg) :> (t / sg)
(e <: S) /J sg = (e / sg) <: (S / sg)
(S ~ T)  /J sg = (S / sg) ~ (T / sg)


module STABSBST (TH : TypeTheory) where
  open TYPETHEORY TH
  open STABTHIN TH
  open FormationRule
  open CheckingRule
  open EliminationRule
  open UniverseRule
  open Monoidal (OPEMON {One})
  
  CxSbst : forall {ga de}(sg : [ [] , NIL ! ga ]/ de)
           (Ga : Context ([] , NIL) ga)(De : Context ([] , NIL) de) -> Set
  CxSbst {ga} sg Ga De = (i : <> <- ga) -> De != (project i sg <: (project i Ga / sg))

  ruCxSbst : forall {ga de}(sg : [ [] , NIL ! ga ]/ de)
             (Ga : Context ([] , NIL) ga)(De : Context ([] , NIL) de) ->
             CxSbst sg Ga De -> CxSbst (sg >/< idsb {[]}) Ga De
  ruCxSbst sg Ga De eSs rewrite sbstRunitor sg = eSs

  wkru : forall {ga de}(sg : [ [] , NIL ! ga ]/ de) xi ->
    wksb (sg >/< idsb {xi}) == (sg >/< idsb {xi -, <>})
  wkru {ga}{de} sg xi = _-,_
     $= (all (_^ (oi no)) (all (_^ thinl oi xi) sg :+ all (_^ thinr de oi) idsb)
          =[ allCat (_^ (oi no)) (all _ sg) (all _ idsb) >=
        all (_^ (oi no)) (all (_^ thinl oi xi) sg)
                                        :+ all (_^ (oi no)) (all (_^ thinr de oi) idsb)
          =< _:+_ $= allCo _ _ _ (\ t -> t ^ (thinl oi xi no)
                                           =< (t ^_) $= (_no $= POLYTHIN.coidC _) ]=
                                          t ^ ((thinl oi xi -< oi) no)
                                           =< thinco t _ _ ]=
                                          (t ^ thinl oi xi) ^ (oi no)
                                            [QED]) sg
                  =$= icompoLemma THINTHINTHIN THINTHINTHIN _ _ _ _
                      ((refl ,_) $= (_no $= oiLemma _)) idsb ]=
        all (_^ (thinl oi xi no)) sg :+
        all (_^ (thinr de oi su)) (all (_^ (oi no)) idsb)
          [QED])
    =$= (#_ $= (_su $= oeU _ _))

  exCxSbst : forall {ga de}(sg : [ [] , NIL ! ga ]/ de)
             (Ga : Context ([] , NIL) ga)(De : Context ([] , NIL) de)
             (eSs : CxSbst sg Ga De)
             (e : Syn ([] , NIL) (de -, <>))(S : Chk ([] , NIL) ga) ->
             let sg' = (all (_^ (oi no)) sg -, e)
                 Ga' = (all (_^ (oi no)) (Ga -, S))
                 S' = (S ^ (oi no)) / sg'
                 De' = all (_^ (oi no)) De -, S' in
             De' != (e <: S') ->
             CxSbst sg' Ga'  De'
  exCxSbst sg Ga De eSs e S eS (i no)
    with derThin (eSs i)
      {De = all (_^ (oi no)) De -, ((S ^ (oi no)) / (all (_^ (oi no)) sg -, e))}
      (oi no) (sym (POLYSELECT.funId _))
  ... | d
    rewrite selectAll i (_^ (oi no)) sg
          | selectAll i (_^ (oi no)) Ga
          | theUsualShoogle (project i Ga) sg e = d
  exCxSbst sg Ga De eSs e S eS (i su) = eS

  derSbst : forall {ga}{Ga : Context ([] , NIL) ga}{J : Judgement ([] , NIL) ga} ->
            Ga != J ->
            forall {de}{De : Context ([] , NIL) de}
            sg -> CxSbst sg Ga De ->
            De != (J /J sg)
  premsSbst : forall {ga}{Ga : Context ([] , NIL) ga}{gas inp suj0 tru suj1}
              (Pz : Premises gas inp suj0 tru suj1)
              (sgs : [ ([] , NIL) ! gas ]/ ga)
              (inps : Env ([] , NIL) (ga ,P inp))
              (sujs0 : Env ([] , NIL) (ga ,P suj0)) ->
              let Jz , trus , sujs1 = premises ga Pz sgs inps sujs0 in
              All (Ga !=_) Jz ->
              forall {de}{De : Context ([] , NIL) de} sg -> CxSbst sg Ga De ->
              let Jz' , trus' , sujs1' = premises de Pz
                    (all (_/ sg) sgs) (inps /E sg) (sujs0 /E sg) in
              All (De !=_) Jz' * trus' == (trus /E sg) * sujs1' == (sujs1 /E sg)
  premSbst : forall {ga}{gas inp tru suj xi tr' suj'}
    {Ga : Context ([] , NIL) (ga -+ xi)}
    (P : Premise gas inp tru suj xi tr' suj')
    (sgs : [ ([] , NIL) ! gas ]/ ga)
    (inps : Env ([] , NIL) (ga ,P inp))
    (trus : Env ([] , NIL) (ga ,P tru))
    (sujs0 : Env ([] , NIL) (ga ,P suj)) ->
    let J , trs , sujs1 = premise ga P sgs inps trus sujs0 in
    Ga != J ->
    forall {de}{De : Context ([] , NIL) (de -+ xi)}(sg : [ [] , NIL ! ga ]/ de) ->
    CxSbst (sg >/< idsb {xi}) Ga De ->
    let J' , trs' , sujs1' = premise de P
         (all (_/ sg) sgs) (inps /E sg) (trus /E sg) (sujs0 /E sg) in
    (De != J') * trs' == ActWeak.acte SBSTWEAK trs sg * (sujs1' == (sujs1 /E sg))
            
  derSbst (extend {S = S} d) sg eSs with
    exCxSbst sg _ _ eSs (# (oe su)) S var
  ... | eSse rewrite theUsualShoogle S sg (# (oe su))
      = extend (derSbst d (wksb sg) eSse)
  derSbst (var {x = x}) sg eSs = eSs x
  derSbst (thunk {n = n} d0 d1) sg eSs rewrite Act.actThunk SBST n (refl , sg)
    = thunk {n = n / sg} (derSbst d0 sg eSs) (derSbst d1 sg eSs)
  derSbst (unis {n = n} d0 d1) sg eSs rewrite Act.actThunk SBST n (refl , sg)
    = unis {n = n / sg} (derSbst d0 sg eSs) (derSbst d1 sg eSs)
  derSbst (rad d0 d1) sg eSs = rad (derSbst d0 sg eSs) (derSbst d1 sg eSs)
  derSbst eq sg eSs = eq
  derSbst (pre x d) sg eSs = pre (redSbst x sg) (derSbst d sg eSs)
  derSbst (post d x) sg eSs = post (derSbst d sg eSs) (redSbst x sg)
  derSbst (type {R} rule Ts dz) sg eSs
    rewrite plugSbstLemma0 (typeSuj R) Ts sg
    = let dz' , _ , _ = premsSbst (typePrems R) [] NIL Ts dz sg eSs in
      type rule (Ts /E sg) dz'
  derSbst (chk {R} rule Ts ts dz) sg eSs
    rewrite plugSbstLemma0 (chkInp R) Ts sg | plugSbstLemma0 (chkSuj R) ts sg
    = let dz' , _ , _ = premsSbst (chkPrems R) [] Ts ts dz sg eSs in 
      chk rule (Ts /E sg) (ts /E sg) dz'
  derSbst {ga} (elir {R} rule e Ss ss d dz) {de}{De} sg eSs
    with elir rule (e / sg) (Ss /E sg) (ss /E sg) | derSbst d sg eSs
  ... | ready | d'
    with premises ga (elimPrems R) ([] -, e) Ss ss
       | premises de (elimPrems R) ([] -, (e / sg)) (Ss /E sg) (ss /E sg)
       | premsSbst (elimPrems R) ([] -, e) Ss ss dz sg eSs
  ... | Jz , trus , sujs | Jz' , ._ , ._ | dz' , refl , refl
        rewrite plugSbstLemma0 (trgType R) Ss sg
          | plugSbstLemma0 (elimSuj R) ss sg
          | instSbstLemma0 (resType R) ([] -, e) (cons Ss trus) sg
          = ready d' dz'
  derSbst (unic {R} rule Ts dz) sg eSs
    rewrite plugSbstLemma0 (uniInp R) Ts sg
    = let dz' , _ , _ = premsSbst (uniPrems R) [] Ts NIL dz sg eSs in
      unic rule (Ts /E sg) dz'
  premsSbst [] sgs inps sujs0 dz sg eSs = [] , refl , refl
  premsSbst {ga} (Pz -, P) sgs inps sujs0 (dz -, d) {de} sg eSs
    with premises ga Pz sgs inps sujs0
       | premises de Pz (all (_/ sg) sgs) (inps /E sg) (sujs0 /E sg)
       | premsSbst Pz sgs inps sujs0 dz sg eSs
  ... | Jz , trus , sujs1 | Jz' , ._ , ._ | dz' , refl , refl
    with premise ga P sgs inps trus sujs1
       | premise de P (all (_/ sg) sgs) (inps /E sg) (trus /E sg) (sujs1 /E sg)
       | premSbst P sgs inps trus sujs1 d sg (ruCxSbst _ _ _ eSs)
  ... | J , tr , sujs2 | J' , ._ , ._ | d' , refl , refl
      = (dz' -, d') , refl , refl
  premSbst {xi = xi} {Ga = Ga} (S !- P) sgs inps trus sujs0 (extend d) {De = De} sg eSs
    with exCxSbst (sg >/< idsb {xi}) _ _ eSs (# (oe su)) (S % (sgs , cons inps trus)) var
  ... | eSs'
      rewrite theUsualShoogle (S % (sgs , cons inps trus)) (sg >/< idsb {xi}) (# (oe su))
            | instSbstLemma S sgs (cons inps trus) sg
            | wkru sg xi
      = let d' , q0 , q1 = premSbst P sgs inps trus sujs0 d sg eSs'
        in  extend d' , abst $= q0 , q1
  premSbst {ga}{xi = xi} (type (ps , T , ph)) sgs inps trus sujs0 d {de} sg eSs
    with derSbst d (sg >/< idsb {xi}) eSs | removeSbst T sujs0 sg
  ... | d' | q0 , q1
    rewrite q0 | q1
    | pointCompo SBSTTHINSBST THINSBSTSBST
      (refl , (sg >/< idsb {ps})) (refl , (oi {S = de} ^+ ph))
      (refl , (oi {S = ga} ^+ ph)) (refl , (sg >/< idsb {xi}))
      (fst (remove ga T sujs0)) ((refl ,_) $= diagSgTh sg ph )
    = d' , refl , refl
  premSbst {ga}{xi = xi} (T :> (ps , t , ph)) sgs inps trus sujs0 d {de} sg eSs
    with derSbst d (sg >/< idsb {xi}) eSs | removeSbst t sujs0 sg
  ... | d' | q0 , q1
    rewrite instSbstLemma T sgs (cons inps trus) sg | q0 | q1
    | pointCompo SBSTTHINSBST THINSBSTSBST
      (refl , (sg >/< idsb {ps})) (refl , (oi {S = de} ^+ ph))
      (refl , (oi {S = ga} ^+ ph)) (refl , (sg >/< idsb {xi}))
      (fst (remove ga t sujs0)) ((refl ,_) $= diagSgTh sg ph)
    = d' , refl , refl
  premSbst {xi = xi} (univ T) sgs inps trus sujs0 d sg eSs
    with derSbst d (sg >/< idsb {xi}) eSs 
  ... | d' rewrite instSbstLemma T sgs (cons inps trus) sg =  d' , refl , refl
  premSbst {xi = xi} (tyeq S T) sgs inps trus sujs0 d sg eSs
    with derSbst d (sg >/< idsb {xi}) eSs 
  ... | d' rewrite instSbstLemma S sgs (cons inps trus) sg
                 | instSbstLemma T sgs (cons inps trus) sg = d' , refl , refl

