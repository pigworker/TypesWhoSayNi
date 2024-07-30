module Deriv where

open import String
open import Basics
open import Fun
open import Eq
open import Bwd
open import Thin
open import Atom
open import Pat
open import Ref
open import Term
open import Action
open import All
open import ActCats
open import Hull

pattern NIL = !!! 0

??_ : forall {M G}(x : G <P- snd M) -> Term M G lib chk
?? x = x ?- idsb
infixr 60 ??_

target : forall {p} -> Term ([] -, <> , p) [] lib syn
target = essl (mets (oe su))

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

module _ {M : Meta} where

  _^J_ : forall {ga de}(J : Judgement M ga)(th : ga <= de) -> Judgement M de
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
         -> Term (gas , inp &&& tru) de lib chk
         -> Premise gas inp tru suj (de -, <>) tr' suj'
         -> Premise gas inp tru suj de (\\\ tr') suj'
  type : forall {suj'}
         -> (x : Subject de suj suj')
         -> Premise gas inp tru suj de (??? (renom (fst (snd x))) (snd (snd x))) suj'
  _:>_ : forall {suj'}
         -> Term (gas , inp &&& tru) de lib chk
         -> (x : Subject de suj suj')
         -> Premise gas inp tru suj de (??? (renom (fst (snd x))) (snd (snd x))) suj'
  univ : Term (gas , inp &&& tru) de lib chk
         -> Premise gas inp tru suj de NIL suj
  tyeq :    Term (gas , inp &&& tru) de lib chk
         -> Term (gas , inp &&& tru) de lib chk
         -> Premise gas inp tru suj de NIL suj

data Premises gas inp suj0 : Pat [] -> Pat [] -> Set where
  [] : Premises gas inp suj0 NIL suj0
  _-,_ : forall {tru suj1 tr' suj2}
    -> Premises gas inp suj0 tru suj1
    -> Premise gas inp tru suj1 [] tr' suj2
    -> Premises gas inp suj0 (tru &&& tr') suj2

remove : forall ga {M}{de' de}{suj suj' : Pat de'}(x : Remove {de'} de suj suj') ->
  Env M (ga ,P suj) -> Term M (ga -+ de) lib chk * Env M (ga ,P suj')
remove ga ??? (??? t) = t , NIL
remove ga (car x) (ss &&& ts) = let s , ss' = remove ga x ss in s , ss' &&& ts
remove ga (cdr x) (ss &&& ts) = let t , ts' = remove ga x ts in t , ss &&& ts'
remove ga (\\\ x) (\\\ ts) = let t , ts' = remove ga x ts in t , \\\ ts'

removeThin : forall {ga}{M}{de' de}{suj suj' : Pat de'}(x : Remove {de'} de suj suj')
  (ts : Env M (ga ,P suj)) ->
  let t , ss = remove ga x ts in
  forall {ga'}(th : ga <= ga') ->
  let t' , ss' = remove ga' x (ActWeak.acte THINWEAK ts th) in
  t' == (t ^ (th ^+ oi {S = de})) *
  ss' == (ActWeak.acte THINWEAK ss th)
removeThin ??? (??? t) th = refl , refl
removeThin (car x) (ss &&& ts) th with removeThin x ss th
... | q0 , q1 rewrite q0 | q1 = refl , refl
removeThin (cdr x) (ss &&& ts) th with removeThin x ts th
... | q0 , q1 rewrite q0 | q1 = refl , refl
removeThin (\\\ x) (\\\ ts) th with removeThin x ts th
... | q0 , q1 rewrite q0 | q1 = refl , refl

removeSbst : forall {ga}{M}{de' de}{suj suj' : Pat de'}(x : Remove {de'} de suj suj')
  (ts : Env M (ga ,P suj)) ->
  let t , ss = remove ga x ts in
  forall {ga'}(sg : [ M ! ga ]/ ga') ->
  let t' , ss' = remove ga' x (ActWeak.acte SBSTWEAK ts sg) in
  t' == (t / (sg >/< idsb {de})) *
  ss' == (ActWeak.acte SBSTWEAK ss sg)
removeSbst ??? (??? t) th = refl , refl
removeSbst (car x) (ss &&& ts) th with removeSbst x ss th
... | q0 , q1 rewrite q0 | q1 = refl , refl
removeSbst (cdr x) (ss &&& ts) th with removeSbst x ts th
... | q0 , q1 rewrite q0 | q1 = refl , refl
removeSbst (\\\ x) (\\\ ts) th with removeSbst x ts th
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
  let S = S' % (sgs , inps &&& trus)
      J , ts , sujs' = premise ga pr sgs inps trus sujs
  in  (S !- J) , \\\ ts , sujs'
premise ga (type (_ , x , th)) sgs inps trus sujs =
  let T , sujs' = remove ga x sujs
  in  type (T ^ (oi ^+ th)) , ??? T , sujs'
premise ga (T' :> (_ , x , th)) sgs inps trus sujs =
  let T = T' % (sgs , inps &&& trus)
      t , sujs' = remove ga x sujs
  in  (T :> (t ^ (oi ^+ th))) , ??? t , sujs'
premise ga (univ T') sgs inps trus sujs =
  let T = T' % (sgs , inps &&& trus)
  in  univ T , NIL , sujs
premise ga (tyeq S' T') sgs inps trus sujs =
  let S = S' % (sgs , inps &&& trus)
      T = T' % (sgs , inps &&& trus)
  in  (S ~ T) , NIL , sujs

premises : forall ga {M gas inp suj0 tru suj1}
  -> Premises gas inp suj0 tru suj1
  -> [ M ! gas ]/ ga
  -> Env M (ga ,P inp)
  -> Env M (ga ,P suj0)
  -> Bwd (Judgement M ga)
   * Env M (ga ,P tru)
   * Env M (ga ,P suj1)
premises ga [] sgs inps sujs = [] , NIL , sujs
premises ga (prs -, pr) sgs inps sujs0 = 
  let jz , trus , sujs1 = premises ga prs sgs inps sujs0
      j , trs' , sujs2 = premise ga pr sgs inps trus sujs1
  in  (jz -, j) , trus &&& trs' , sujs2

record FormationRule : Set where
  field
    typeSuj    : Pat []
    {typeTru}  : Pat []
    {typeSuj'} : Pat []
    typePrems  : Premises [] NIL typeSuj typeTru typeSuj'
    {typeDone} : So (unholey typeSuj')

record CheckingRule : Set where
  field
    chkInp    : Pat []
    chkSuj    : Pat []
    {chkTru}  : Pat []
    {chkSuj'} : Pat []
    chkPrems  : Premises [] chkInp chkSuj chkTru chkSuj'
    {chkDone} : So (unholey chkSuj')

record EliminationRule : Set where
  field
    trgType    : Pat []
    elimSuj    : Pat []
    {elimTru}  : Pat []
    {elimSuj'} : Pat []
    elimPrems  : Premises ([] -, <>) trgType elimSuj elimTru elimSuj'
    {elimDone} : So (unholey elimSuj')
    resType    : Term (([] -, <>) , trgType &&& elimTru) [] lib chk

module _ where
  open FormationRule
  open CheckingRule
  open EliminationRule

  Redex = Sg CheckingRule \ t -> Sg EliminationRule \ e ->
          chkInp t ~~ trgType e

  redPat : Redex -> Pat []
  redPat (t , e , Ty , _) = (chkSuj t &&& Ty) &&& elimSuj e

  getRedexes : Bwd CheckingRule -> Bwd EliminationRule -> Bwd Redex
  getRedexes tz ez = 
    tz >>= \ t ->
    ez >>= \ e ->
    guard (unify? (chkInp t) (trgType e)) >>= \ u ->
    [] -, (t , e , u)

  data [_::_]_~>?::_ : (p P q : Pat []) ->
                        Term ([] , (p &&& P) &&& q) [] lib chk -> Set where
    [_::_]_~>_::_ : forall p P q ->
                    Term ([] , (p &&& P) &&& q) [] lib chk ->
                    forall T ->
                    [ p :: P ] q ~>?:: T

  Reduct : Redex -> Set
  Reduct (t , e , Ty , rt , re)
    with (patTerm (chkSuj t) (car ` car) :: patTerm Ty (car ` cdr))
       | refineMatch re (patEnv Ty [] (car ` cdr))
  ...  | rad | chi , _ with premises [] (elimPrems e) ([] -, rad) chi
          (patEnv (elimSuj e) [] cdr)
  ...  | _ , pi , _ =
    [ chkSuj t :: Ty ] elimSuj e ~>?:: (resType e % (([] -, rad) , chi &&& pi))

  noOverlap : (tz : Bwd CheckingRule)(ez : Bwd EliminationRule) ->
    Pairwise (\ x y -> chkInp x &&& chkSuj x ~~ chkInp y &&& chkSuj y -> Zero) tz ->
    Pairwise (\ x y -> trgType x &&& elimSuj x ~~ trgType y &&& elimSuj y -> Zero) ez ->
    Pairwise (\ x y -> redPat x ~~ redPat y -> Zero)
       (getRedexes tz ez)
  noOverlap tz ez tzA ezA th u with inBind tz _ th
  noOverlap tz ez tzA ezA ._ u | isInBind yzz thz q with findPairJoin yzz (thinQ q)
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz with bwdRThin thz ti
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, r with inBind ez _ r
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, r | isInBind yzz1 thz1 q1 with findPairJoin yzz1 (ejz -< thinQ q1)
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, .(bind^ _ thz1 q1) | isInBind yzz1 thz1 q1 | #0 , zz , si , ekz with bwdRThin thz1 si
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, .(bind^ _ thz1 q1) | isInBind yzz1 thz1 q1 | #0 , zz , si , ekz | ([] -, e) , ph , [] -, s with unify? (chkInp t) (trgType e)
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, .(bind^ _ thz1 q1) | isInBind yzz1 thz1 q1 | #0 , .[] , si , () | [] -, e , ph , [] -, ze | #0 , v
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, .(bind^ _ thz1 q1) | isInBind yzz1 thz1 q1 | #0 , zz , si , bad0 | [] -, e , ph , [] -, bad1 | #1 , v
    = busted (bad0 -< bad1)
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, .(bind^ _ thz1 q1) | isInBind yzz1 thz1 q1 | #1 , zz , zz' , si , ri , qi with bwdRThin thz1 si
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, .(bind^ _ thz1 q1) | isInBind yzz1 thz1 q1 | #1 , zz , zz' , si , ri , qi | ([] -, e0 -, e1) , th' , [] -, x0 -, x1 with ezA th'
  ... | n with unify? (chkInp t) (trgType e0) | unify? (chkInp t) (trgType e1)
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, .(bind^ _ thz1 q1) | isInBind yzz1 thz1 q1 | #1 , zz , zz' , si , ri , qi | [] -, e0 -, e1 , th' , [] -, x0 -, x1 | n | #0 , d0 | b1 , d1 = busted (ri -< x0)
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, .(bind^ _ thz1 q1) | isInBind yzz1 thz1 q1 | #1 , zz , zz' , si , ri , qi | [] -, e0 -, e1 , th' , [] -, x0 -, x1 | n | #1 , d0 | #0 , d1 = busted (qi -< x1)
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, .(bind^ _ thz1 q1) | isInBind yzz1 thz1 q1 | #1 , zz , zz' , si , ri , qi | [] -, e0 -, e1 , th' , [] -, x0 -, x1 | n | #1 , d0 , f0 , g0 | #1 , d1 , f1 , g1 with ri -< x0 | qi -< x1
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, .(bind^ _ thz1 q1) | isInBind yzz1 thz1 q1 | #1 , zz , zz' , si , ri , qi | [] -, e0 -, e1 , th' , [] -, x0 -, x1 | n | #1 , d0 , f0 , g0 | #1 , d1 , f1 , g1 | () no | j
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, .(bind^ _ thz1 q1) | isInBind yzz1 thz1 q1 | #1 , zz , zz' , si , ri , qi | [] -, e0 -, e1 , th' , [] -, x0 -, x1 | n | #1 , d0 , f0 , g0 | #1 , d1 , f1 , g1 | ze su | () no
  noOverlap tz ez tzA ezA .(bind^ _ thz q) (.((_ &&& _) &&& _) , (h0 &&& h2) &&& h1 , (h4 &&& h5) &&& h3) | isInBind yzz thz q | #0 , yz , ti , ejz | [] -, t , th , [] -, .(bind^ _ thz1 q1) | isInBind yzz1 thz1 q1 | #1 , zz , zz' , si , ri , qi | [] -, e0 -, e1 , th' , [] -, x0 -, x1 | n | #1 , d0 , f0 , g0 | #1 , d1 , f1 , g1 | ze su | ze su = n (_ , (h2 -<P=- g0) &&& h1 , (h5 -<P=- g1) &&& h3)
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #1 , yz , zz , ti , si , ri with bwdRThin thz ti
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #1 , yz , zz , ti , si , ri | ([] -, t0 -, t1) , th' , [] -, x0 -, x1 with inBind ez _ x0 | inBind ez _ x1
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #1 , ._ , ._ , ti , si , ri | [] -, t0 -, t1 , th' , [] -, ._ -, ._ | isInBind yzz1 thz1 refl | isInBind yzz2 thz2 refl with findOneJoin yzz1 si | findOneJoin yzz2 ri
  ... | _ , f0 , g0 | _ , f1 , g1 with bwdRThin thz1 g0 | bwdRThin thz2 g1
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #1 , .(join yzz1) , .(join yzz2) , ti , si , ri | [] -, t0 -, t1 , th' , [] -, .(bind^ _ thz1 refl) -, .(bind^ _ thz2 refl) | isInBind yzz1 thz1 refl | isInBind yzz2 thz2 refl | _ , f0 , g0 | _ , f1 , g1 | ([] -, e0) , _ , [] -, x0 | ([] -, e1) , _ , [] -, x1 with unify? (chkInp t0) (trgType e0) | unify? (chkInp t1) (trgType e1)
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #1 , .(join yzz1) , .(join yzz2) , ti , si , ri | [] -, t0 -, t1 , th' , [] -, .(bind^ _ thz1 refl) -, .(bind^ _ thz2 refl) | isInBind yzz1 thz1 refl | isInBind yzz2 thz2 refl | _ , f0 , g0 | _ , f1 , g1 | [] -, e0 , _ , [] -, x0 | [] -, e1 , _ , [] -, x1 | #0 , h0 | b1 , h1 = busted (f0 -< x0)
  noOverlap tz ez tzA ezA .(bind^ _ thz q) u | isInBind yzz thz q | #1 , .(join yzz1) , .(join yzz2) , ti , si , ri | [] -, t0 -, t1 , th' , [] -, .(bind^ _ thz1 refl) -, .(bind^ _ thz2 refl) | isInBind yzz1 thz1 refl | isInBind yzz2 thz2 refl | _ , f0 , g0 | _ , f1 , g1 | [] -, e0 , _ , [] -, x0 | [] -, e1 , _ , [] -, x1 | #1 , h0 | #0 , h1 = busted (f1 -< x1)
  noOverlap tz ez tzA ezA .(bind^ _ thz q) (_ , (h4 &&& h6) &&& h5 , (h8 &&& h9) &&& h7) | isInBind yzz thz q | #1 , .(join yzz1) , .(join yzz2) , ti , si , ri | [] -, t0 -, t1 , th' , [] -, .(bind^ _ thz1 refl) -, .(bind^ _ thz2 refl) | isInBind yzz1 thz1 refl | isInBind yzz2 thz2 refl | _ , f0 , g0 | _ , f1 , g1 | [] -, e0 , _ , [] -, x0 | [] -, e1 , _ , [] -, x1 | #1 , _ , h0 , h1 | #1 , _ , h2 , h3 with f0 -< x0 | f1 -< x1
  noOverlap tz ez tzA ezA .(bind^ _ thz q) (.((_ &&& _) &&& _) , (h4 &&& h6) &&& h5 , (h8 &&& h9) &&& h7) | isInBind yzz thz q | #1 , .(join yzz1) , .(join yzz2) , ti , si , ri | [] -, t0 -, t1 , th' , [] -, .(bind^ _ thz1 refl) -, .(bind^ _ thz2 refl) | isInBind yzz1 thz1 refl | isInBind yzz2 thz2 refl | _ , f0 , g0 | _ , f1 , g1 | [] -, e0 , _ , [] -, x0 | [] -, e1 , _ , [] -, x1 | #1 , _ , h0 , h1 | #1 , _ , h2 , h3 | () no | p1
  noOverlap tz ez tzA ezA .(bind^ _ thz q) (.((_ &&& _) &&& _) , (h4 &&& h6) &&& h5 , (h8 &&& h9) &&& h7) | isInBind yzz thz q | #1 , .(join yzz1) , .(join yzz2) , ti , si , ri | [] -, t0 -, t1 , th' , [] -, .(bind^ _ thz1 refl) -, .(bind^ _ thz2 refl) | isInBind yzz1 thz1 refl | isInBind yzz2 thz2 refl | _ , f0 , g0 | _ , f1 , g1 | [] -, e0 , _ , [] -, x0 | [] -, e1 , _ , [] -, x1 | #1 , _ , h0 , h1 | #1 , _ , h2 , h3 | p0 su | () no
  noOverlap tz ez tzA ezA .(bind^ _ thz q) (.((_ &&& _) &&& _) , (h4 &&& h6) &&& h5 , (h8 &&& h9) &&& h7) | isInBind yzz thz q | #1 , .(join yzz1) , .(join yzz2) , ti , si , ri | [] -, t0 -, t1 , th' , [] -, .(bind^ _ thz1 refl) -, .(bind^ _ thz2 refl) | isInBind yzz1 thz1 refl | isInBind yzz2 thz2 refl | _ , f0 , g0 | _ , f1 , g1 | [] -, e0 , _ , [] -, x0 | [] -, e1 , _ , [] -, x1 | #1 , _ , h0 , h1 | #1 , _ , h2 , h3 | p0 su | p1 su
    = tzA th' (_ , (h6 -<P=- h0) &&& h4 , (h9 -<P=- h2) &&& h8)
  
record UniverseRule : Set where
  field
    uniInp    : Pat []
    {uniTru}  : Pat []
    uniPrems  : Premises [] uniInp NIL uniTru NIL

record BetaRule : Set where
  field
    betaIntro betaType betaElim : Pat []
    redTerm redType : Term ([] , (betaIntro &&& betaType) &&& betaElim) [] lib chk

module _ where
  open FormationRule
  open CheckingRule
  open EliminationRule
  open BetaRule

  betaRules : (rz : Bwd Redex) -> All Reduct rz ->
    Sg (Bwd (BetaRule)) \ bz ->
    BwdR (\ { (t , e , Ty , rt , re) b ->
        betaIntro b == chkSuj t
      * betaType  b == Ty
      * betaElim  b == elimSuj e })
      rz bz
  betaRules [] [] = [] , []
  betaRules (rz -, r) (uz -, ([ p :: P ] q ~> t :: T))
    with betaRules rz uz
  ... | bz , rbz
      = (bz -, record
          { betaIntro = p
          ; betaType  = P
          ; betaElim  = q
          ; redTerm   = t
          ; redType   = T
          })
      , rbz -, (refl , refl , refl)

stringRemove : (x : String){ga : Nat}(p : Pat ga) ->
  So (schemIsIn x p) ->
  Sg _ \ de -> Sg _ \ p' -> Remove de p p'
stringRemove x (!!! a) ()
stringRemove x (p &&& q) prf with schemIsIn x q | stringRemove x q
stringRemove x (p &&& q) prf | #0 | _ = 
  let _ , _ , r = stringRemove x p prf in _ , _ , car r
stringRemove x (p &&& q) prf | #1 | f =
  let _ , _ , r = f <> in _ , _ , cdr r
stringRemove x (\\\ q) prf = 
  let _ , _ , r = stringRemove x q prf in _ , _ , \\\ r
stringRemove x (??? _ th) prf = _ , _ , ???

??s : forall (x : String){p : Pat []}{prf : So (schemIsIn x p)} ->
      let de , p' , r = stringRemove x p prf in
      forall {ga} -> de <= ga -> Subject ga p p'
??s x {p}{prf} th with stringRemove x p prf
... | de , p' , r = de , r , th
