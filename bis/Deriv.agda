module Deriv where

open import Basics
open import Fun
open import Eq
open import Bwd
open import Thin
open import Atom
open import Pat
open import Term
open import All
open import ActCats
open import Hull

module _ (M : Meta) where

  Chk Syn : Nat -> Set
  Chk ga = Term M ga lib chk
  Syn ga = Term M ga lib syn

  data Judgement (ga : Nat) : Set where
    _!-_ : Chk ga -> Judgement (ga -, <>) -> Judgement ga
    type univ : Chk ga -> Judgement ga
    _:>_ : Chk ga -> Chk ga -> Judgement ga
    _<:_ : Syn ga -> Chk ga -> Judgement ga
    _~_  : Chk ga -> Chk ga -> Judgement ga

  _^J_ : forall {ga de}(J : Judgement ga)(th : ga <= de) -> Judgement de
  (S !- J) ^J th = (S ^ th) !- (J ^J (th su))
  type T   ^J th = type (T ^ th)
  univ T   ^J th = univ (T ^ th)
  (T :> t) ^J th = (T ^ th) :> (t ^ th)
  (e <: S) ^J th = (e ^ th) <: (S ^ th)
  (S ~ T)  ^J th = (S ^ th) ~ (T ^ th)

Subject : Nat -> Pat [] -> Pat [] -> Set
Subject ga suj suj' = Sg _ \ de -> Remove de suj suj' * de <= ga

data Premise gas (inp tru suj : Pat []) de : Pat de -> Pat [] -> Set where
  _!-_ : forall {tr' suj'}
         -> Term (gas , cons inp tru) de lib chk
         -> Premise gas inp tru suj (de -, <>) tr' suj'
         -> Premise gas inp tru suj de (abst tr') suj'
  type : forall {suj'}
         -> (x : Subject de suj suj')
         -> Premise gas inp tru suj de (hole (snd (snd x))) suj'
  _:>_ : forall {suj'}
         -> Term (gas , cons inp tru) de lib chk
         -> (x : Subject de suj suj')
         -> Premise gas inp tru suj de (hole (snd (snd x))) suj'
  univ : Term (gas , cons inp tru) de lib chk
         -> Premise gas inp tru suj de (atom NIL) suj
  tyeq :    Term (gas , cons inp tru) de lib chk
         -> Term (gas , cons inp tru) de lib chk
         -> Premise gas inp tru suj de (atom NIL) suj

data Premises gas inp suj0 : Pat [] -> Pat [] -> Set where
  [] : Premises gas inp suj0 (atom NIL) suj0
  _-,_ : forall {tru suj1 tr' suj2}
    -> Premises gas inp suj0 tru suj1
    -> Premise gas inp tru suj1 [] tr' suj2
    -> Premises gas inp suj0 (cons tru tr') suj2

remove : forall ga {M}{de' de}{suj suj' : Pat de'}(x : Remove {de'} de suj suj') ->
  Env M (ga ,P suj) -> Term M (ga -+ de) lib chk * Env M (ga ,P suj')
remove ga hole (hole t) = t , atom NIL
remove ga (car x) (cons ss ts) = let s , ss' = remove ga x ss in s , cons ss' ts
remove ga (cdr x) (cons ss ts) = let t , ts' = remove ga x ts in t , cons ss ts'
remove ga (abst x) (abst ts) = let t , ts' = remove ga x ts in t , abst ts'

removeThin : forall {ga}{M}{de' de}{suj suj' : Pat de'}(x : Remove {de'} de suj suj')
  (ts : Env M (ga ,P suj)) ->
  let t , ss = remove ga x ts in
  forall {ga'}(th : ga <= ga') ->
  let t' , ss' = remove ga' x (ActWeak.acte THINWEAK ts th) in
  t' == (t ^ (th ^+ oi {S = de})) *
  ss' == (ActWeak.acte THINWEAK ss th)
removeThin hole (hole t) th = refl , refl
removeThin (car x) (cons ss ts) th with removeThin x ss th
... | q0 , q1 rewrite q0 | q1 = refl , refl
removeThin (cdr x) (cons ss ts) th with removeThin x ts th
... | q0 , q1 rewrite q0 | q1 = refl , refl
removeThin (abst x) (abst ts) th with removeThin x ts th
... | q0 , q1 rewrite q0 | q1 = refl , refl

removeSbst : forall {ga}{M}{de' de}{suj suj' : Pat de'}(x : Remove {de'} de suj suj')
  (ts : Env M (ga ,P suj)) ->
  let t , ss = remove ga x ts in
  forall {ga'}(sg : [ M ! ga ]/ ga') ->
  let t' , ss' = remove ga' x (ActWeak.acte SBSTWEAK ts sg) in
  t' == (t / (sg >/< idsb {de})) *
  ss' == (ActWeak.acte SBSTWEAK ss sg)
removeSbst hole (hole t) th = refl , refl
removeSbst (car x) (cons ss ts) th with removeSbst x ss th
... | q0 , q1 rewrite q0 | q1 = refl , refl
removeSbst (cdr x) (cons ss ts) th with removeSbst x ts th
... | q0 , q1 rewrite q0 | q1 = refl , refl
removeSbst (abst x) (abst ts) th with removeSbst x ts th
... | q0 , q1 rewrite q0 | q1 = refl , refl

premise : forall ga {M gas inp tru suj de tr' suj'}
  -> Premise gas inp tru suj de tr' suj'
  -> [ M ! gas ]/ ga
  -> Env M (ga ,P inp)
  -> Env M (ga ,P tru)
  -> Env M (ga ,P suj)
  -> Judgement M (ga -+ de)
   * Env M (ga ,P tr')
   * Env M (ga ,P suj')
premise ga (S' !- pr) sgs inps trus sujs =
  let S = S' % (sgs , cons inps trus)
      J , ts , sujs' = premise ga pr sgs inps trus sujs
  in  (S !- J) , abst ts , sujs'
premise ga (type (_ , x , th)) sgs inps trus sujs =
  let T , sujs' = remove ga x sujs
  in  type (T ^ (oi ^+ th)) , hole T , sujs'
premise ga (T' :> (_ , x , th)) sgs inps trus sujs =
  let T = T' % (sgs , cons inps trus)
      t , sujs' = remove ga x sujs
  in  (T :> (t ^ (oi ^+ th))) , hole t , sujs'
premise ga (univ T') sgs inps trus sujs =
  let T = T' % (sgs , cons inps trus)
  in  univ T , atom NIL , sujs
premise ga (tyeq S' T') sgs inps trus sujs =
  let S = S' % (sgs , cons inps trus)
      T = T' % (sgs , cons inps trus)
  in  (S ~ T) , atom NIL , sujs

premises : forall ga {M gas inp suj0 tru suj1}
  -> Premises gas inp suj0 tru suj1
  -> [ M ! gas ]/ ga
  -> Env M (ga ,P inp)
  -> Env M (ga ,P suj0)
  -> Bwd (Judgement M ga)
   * Env M (ga ,P tru)
   * Env M (ga ,P suj1)
premises ga [] sgs inps sujs = [] , atom NIL , sujs
premises ga (prs -, pr) sgs inps sujs0 = 
  let jz , trus , sujs1 = premises ga prs sgs inps sujs0
      j , trs' , sujs2 = premise ga pr sgs inps trus sujs1
  in  (jz -, j) , cons trus trs' , sujs2

record FormationRule : Set where
  field
    typeSuj    : Pat []
    {typeTru}  : Pat []
    {typeSuj'} : Pat []
    typePrems  : Premises [] (atom NIL) typeSuj typeTru typeSuj'
    {typeDone} : Unholey typeSuj'

record CheckingRule : Set where
  field
    chkInp    : Pat []
    chkSuj    : Pat []
    {chkTru}  : Pat []
    {chkSuj'} : Pat []
    chkPrems  : Premises [] chkInp chkSuj chkTru chkSuj'
    {chkDone} : Unholey chkSuj'

record EliminationRule : Set where
  field
    trgType    : Pat []
    elimSuj    : Pat []
    {elimTru}  : Pat []
    {elimSuj'} : Pat []
    elimPrems  : Premises ([] -, <>) trgType elimSuj elimTru elimSuj'
    {elimDone} : Unholey elimSuj'
    resType    : Term (([] -, <>) , cons trgType elimTru) [] lib chk

module _ where
  open FormationRule
  open CheckingRule
  open EliminationRule

  trgTypeMatches : (e : EliminationRule) -> Bwd FormationRule ->
    Bwd (Sg FormationRule \ T ->
         Sg (Pat []) \ uT ->
         (uT <P= trgType e) * (uT <P= typeSuj T))
  trgTypeMatches e [] = []
  trgTypeMatches e (Tz -, T) with unify (trgType e) (typeSuj T)
  trgTypeMatches e (Tz -, T) | fail , u = trgTypeMatches e Tz
  trgTypeMatches e (Tz -, T) | [ uT ]M , er , Tr =
    trgTypeMatches e Tz -, (T , uT , er , Tr)

  elimTypeMatches : Bwd EliminationRule -> Bwd FormationRule ->
    Bwd (Sg EliminationRule \ e -> Sg FormationRule \ T ->
         Sg (Pat []) \ uT ->
         (uT <P= trgType e) * (uT <P= typeSuj T))
  elimTypeMatches [] Tz = []
  elimTypeMatches (ez -, e) Tz =
    elimTypeMatches ez Tz -+
    bwd (e ,_) (trgTypeMatches e Tz)

  introTypeMatches :
    (x : Sg EliminationRule \ e -> Sg FormationRule \ T ->
         Sg (Pat []) \ uT ->
         (uT <P= trgType e) * (uT <P= typeSuj T)) ->
    let e , T , uT , uTe , uTT = x in
    Bwd CheckingRule ->
    Bwd (Sg CheckingRule \ t -> Sg (Pat []) \ vT ->
      (vT <P= uT) * (vT <P= chkInp t))
  introTypeMatches (e , T , uT , uTe , uTT) [] = []
  introTypeMatches (e , T , uT , uTe , uTT) (tz -, t) with unify uT (chkInp t)
  ... | fail , _ = introTypeMatches (e , T , uT , uTe , uTT) tz
  ... | [ vT ]M , r0 , r1
    =  introTypeMatches (e , T , uT , uTe , uTT) tz
    -, (t , vT , r0 , r1)

  Redex = Sg EliminationRule \ e -> Sg FormationRule \ T -> Sg CheckingRule \ t ->
     Sg (Pat []) \ Ty ->
     (Ty <P= trgType e) * (Ty <P= typeSuj T) * (Ty <P= chkInp t)

  Reduct : Redex -> Set
  Reduct (e , T , t , Ty , re , rT , rt) =
    Term ([] , cons (cons (chkSuj t) Ty) (elimSuj e)) [] lib chk

  wellTypedRedexes : Bwd EliminationRule -> Bwd FormationRule -> Bwd CheckingRule ->
    Bwd Redex
  wellTypedRedexes ez Tz tz = help (elimTypeMatches ez Tz)
    where
      help : _ -> _
      help [] = []
      help (mz -, m@(e , T , u , r0 , r1)) =
        help mz -+
        bwd (\ { (t , Ty , r2 , r3) -> 
               e , T , t , Ty , (r2 -<P=- r0) , (r2 -<P=- r1) , r3 })
          (introTypeMatches m tz)

record UniverseRule : Set where
  field
    uniInp    : Pat []
    {uniTru}  : Pat []
    uniPrems  : Premises [] uniInp (atom NIL) uniTru (atom NIL)

record BetaRule : Set where
  field
    betaIntro betaType betaElim : Pat []
    redTerm redType : Term ([] , cons (cons betaIntro betaType) betaElim) [] lib chk

module _ where
  open FormationRule
  open CheckingRule
  open EliminationRule
  open BetaRule

  betaRules : (rz : Bwd Redex) -> All Reduct rz -> Bwd (BetaRule)
  betaRules .[] [] = []
  betaRules (rz -, (e , T , t , Ty , re , rT , rt)) (uz -, u)
    with (patTerm (chkSuj t) (car ` car) :: patTerm Ty (car ` cdr))
       | refineMatch re (patEnv Ty [] (car ` cdr))
  ... | rad | chi , _
    with premises [] (elimPrems e) ([] -, rad) chi
          (patEnv (elimSuj e) [] cdr)
  ... | _ , pi , _ =
    betaRules rz uz -, record
      { betaIntro = chkSuj t
      ; betaType  = Ty
      ; betaElim  = elimSuj e
      ; redTerm   = u
      ; redType   = resType e % (([] -, rad) , cons chi pi)
      }

  betaRulesUnambiguous : (rz : Bwd Redex) ->
    Apart (\ { (e , T , t , Ty , re , rT , rt) ->
               cons (cons (chkSuj t) Ty) (elimSuj e) }) rz ->
    (uz : All Reduct rz) ->
    Apart (\ b -> cons (cons (betaIntro b) (betaType b)) (betaElim b))
      (betaRules rz uz)
  betaRulesUnambiguous .[] rza [] = _
  betaRulesUnambiguous (rz -, (e , T , t , Ty , re , rT , rt)) (rza , a) (uz -, u)
    = betaRulesUnambiguous rz rza uz , help rz a uz where
    help : forall rz ->
      Apartz (\ { (e , T , t , Ty , re , rT , rt)
              -> cons (cons (chkSuj t) Ty) (elimSuj e) })
          rz (e , T , t , Ty , re , rT , rt) ->
      (uz : All Reduct rz) ->
      Apartz (\ b -> cons (cons (betaIntro b) (betaType b)) (betaElim b))
       (betaRules rz uz) _
    help .[] a [] = _
    help (rz -, (e' , T' , t' , Ty' , re' , rT' , rt')) (az , a) (uz -, u)
       = help rz az uz , a
       
{-
data Context : Nat -> Set where
  [] : Context []
  _-,_ : forall {ga} -> Context ga -> Chk ga -> Context (ga -, <>)
-}

Context : Meta -> Nat -> Set
Context M ga = All (\ _ -> Term M ga lib chk) ga

record TypeTheory : Set where
  open FormationRule
  open CheckingRule
  open EliminationRule
  open UniverseRule
  open BetaRule
  field
    formation   : Bwd FormationRule
    checking    : Bwd CheckingRule
    elimination : Bwd EliminationRule
    universe    : Bwd UniverseRule
  redexes : Bwd Redex
  redexes = wellTypedRedexes elimination formation checking
  field
    reducts     : All Reduct redexes
    formationUnambiguous   : Apart typeSuj formation
    checkingUnambiguous    : Apart (\ r -> cons (chkInp r) (chkSuj r)) checking
    eliminationUnambiguous : Apart (\ r -> cons (trgType r) (elimSuj r)) elimination
    universeUnambiguous    : Apart uniInp universe
  computation : Bwd BetaRule
  computation = betaRules redexes reducts

module TYPETHEORY (TH : TypeTheory) where
  open TypeTheory TH

  module _ {M : Meta} where

    data _~>_ {ga} : forall {d}(t t' : Term M ga lib d) -> Set where

      car  : forall {s s' t} -> s ~> s' -> (s & t) ~> (s' & t)
      cdr  : forall {s t t'} -> t ~> t' -> (s & t) ~> (s & t')
      abst : forall {t t'} -> t ~> t' -> (\\ t) ~> (\\ t')
      thnk : forall {n e} -> essl n ~> e -> thnk n ~> [ e ]
      targ : forall {e e' s} -> e ~> e' -> (e $ s) ~> (e' $ s)
      elim : forall {e s s'} -> s ~> s' -> (e $ s) ~> (e $ s')
      term : forall {t t' T} -> t ~> t' -> (t :: T) ~> (t' :: T)
      type : forall {t T T'} -> T ~> T' -> (t :: T) ~> (t :: T')
      beta : forall {R}(x : R <- computation) -> let open BetaRule R in
        (ts : Env M (ga ,P betaIntro)) ->
        (Ts : Env M (ga ,P betaType)) ->
        (ss : Env M (ga ,P betaElim)) ->
        (((betaIntro %P ts) :: (betaType %P Ts)) $ (betaElim %P ss))
          ~>
        ((redTerm % ([] , cons (cons ts Ts) ss))
          :: (redType % ([] , cons (cons ts Ts) ss)))


    data _!=_ {ga : Nat}(Ga : Context M ga) : Judgement M ga -> Set where


      extend : forall {S J}
  
            -> all (_^ (oi no)) (Ga -, S) != J
            -------------------------------------
            -> Ga != (S !- J)


      var    : forall {x}

        ---------------------------------
        -> Ga != (# x <: project x Ga)


      thunk  : forall {n S T}

        -> Ga != (n <: S) -> Ga != (S ~ T)
        -------------------------------------
        -> Ga != (T :> [ n ])


      unis   : forall {n S}

        -> Ga != (n <: S) -> Ga != univ S
        -----------------------------------
        -> Ga != type [ n ]


      rad    : forall {t T}

        -> Ga != type T -> Ga != (T :> t)
        ------------------------------------
        -> Ga != ((t :: T) <: T)
           

      eq   : forall {T}

        -------------------
        -> Ga != (T ~ T)


      pre  : forall {T T' t}

        -> T ~> T'   -> Ga != (T' :> t)
        ----------------------------------
        -> Ga != (T :> t)


      post : forall {e S S'}

        -> Ga != (e <: S)   -> S ~> S'
        --------------------------------
        -> Ga != (e <: S')


      type : forall {R}(rule : R <- formation) -> let open FormationRule R in
         forall (ts : Env M (ga ,P typeSuj))
        -> let Jz , _ = premises ga typePrems [] (atom NIL) ts in

           All (Ga !=_) Jz
        --------------------------------
        -> Ga != type (typeSuj %P ts)


      chk  : forall {R}(rule : R <- checking) -> let open CheckingRule R in
         forall 
         (Ts : Env M (ga ,P chkInp))
         (ts : Env M (ga ,P chkSuj))
        -> let Jz , _ = premises ga chkPrems [] Ts ts in

           All (Ga !=_) Jz
        ----------------------------------------------
        -> Ga != ((chkInp %P Ts) :> (chkSuj %P ts))


      elir  : forall {R}(rule : R <- elimination) -> let open EliminationRule R in
         forall (e : Term M ga lib syn)
         (Ss : Env M (ga ,P trgType))
         (ss : Env M (ga ,P elimSuj))
        -> let Jz , trus , _ = premises ga elimPrems ([] -, e) Ss ss in

           Ga != (e <: (trgType %P Ss))
        -> All (Ga !=_) Jz
        -----------------------------------------------------------------
        -> Ga != ((e $ (elimSuj %P ss)) <: (resType % ([] -, e , cons Ss trus))) 


      unic : forall {R}(rule : R <- universe) -> let open UniverseRule R in
         forall 
         (Ts : Env M (ga ,P uniInp))
        -> let Jz , _ = premises ga uniPrems [] Ts (atom NIL) in

           All (Ga !=_) Jz
        ----------------------------------------------
        -> Ga != univ (uniInp %P Ts)
