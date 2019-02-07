module Deriv where

open import Basics
open import Eq
open import Bwd
open import Thin
open import Atom
open import Pat
open import Term
open import All

Chk Syn : Nat -> Set
Chk ga = Term ([] , atom NIL) ga lib chk
Syn ga = Term ([] , atom NIL) ga lib syn


data Judgement (ga : Nat) : Set where
  _!-_ : Chk ga -> Judgement (ga -, <>) -> Judgement ga
  type univ : Chk ga -> Judgement ga
  _:>_ : Chk ga -> Chk ga -> Judgement ga
  _<:_ : Syn ga -> Chk ga -> Judgement ga
  _::_ : <> <- ga -> Chk ga -> Judgement ga
  _~_  : Chk ga -> Chk ga -> Judgement ga

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

remove : forall ga {M}{de' de}{suj suj' : Pat de'} -> (x : Remove {de'} de suj suj') ->
  Env M (ga ,P suj) -> Term M (ga -+ de) lib chk * Env M (ga ,P suj')
remove ga hole (hole t) = t , atom NIL
remove ga (car x) (cons ss ts) = let s , ss' = remove ga x ss in s , cons ss' ts
remove ga (cdr x) (cons ss ts) = let t , ts' = remove ga x ts in t , cons ss ts'
remove ga (abst x) (abst ts) = let t , ts' = remove ga x ts in t , abst ts'

premise : forall ga {gas inp tru suj de tr' suj'}
  -> Premise gas inp tru suj de tr' suj'
  -> [ ([] , atom NIL) ! gas ]/ ga
  -> Env ([] , atom NIL) (ga ,P inp)
  -> Env ([] , atom NIL) (ga ,P tru)
  -> Env ([] , atom NIL) (ga ,P suj)
  -> Judgement (ga -+ de)
   * Env ([] , atom NIL) (ga ,P tr')
   * Env ([] , atom NIL) (ga ,P suj')
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

premises : forall ga {gas inp suj0 tru suj1}
  -> Premises gas inp suj0 tru suj1
  -> [ ([] , atom NIL) ! gas ]/ ga
  -> Env ([] , atom NIL) (ga ,P inp)
  -> Env ([] , atom NIL) (ga ,P suj0)
  -> Bwd (Judgement ga)
   * Env ([] , atom NIL) (ga ,P tru)
   * Env ([] , atom NIL) (ga ,P suj1)
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
    resType    : Term (([] -, <>) , elimTru) [] lib chk

record UniverseRule : Set where
  field
    uniInp    : Pat []
    {uniTru}  : Pat []
    uniPrems  : Premises [] uniInp (atom NIL) uniTru (atom NIL)


data Context : Nat -> Set where
  [] : Context []
  _-,_ : forall {ga} -> Context ga -> Chk ga -> Context (ga -, <>)


postulate
  formation   : Bwd FormationRule
  checking    : Bwd CheckingRule
  elimination : Bwd EliminationRule
  universe    : Bwd UniverseRule

data _!=_ : {ga : Nat}(Ga : Context ga) -> Judgement ga -> Set where


  extend : forall {ga}{Ga : Context ga}{S J}
  
            -> (Ga -, S) != J
            --------------------
            -> Ga != (S !- J)


  var0    : forall {ga}{Ga : Context ga}{S}
  
        ---------------------------------------------
        -> (Ga -, S) != ((oe su) :: (S ^ (oi no)))


  vars   : forall {ga}{Ga : Context ga}{x S T}
  
        -> Ga != (x :: S)
        --------------------------------------------
        -> (Ga -, T) != ((x no) :: (S ^ (oi no)))


  var    : forall {ga}{Ga : Context ga}{x S}

        -> Ga != (x :: S)
        ----------------------
        -> Ga != (# x <: S)


  thunk  : forall {ga}{Ga : Context ga}{n S T}

        -> Ga != (n <: S) -> Ga != (S ~ T)
        -------------------------------------
        -> Ga != (T :> [ n ])


  unis   : forall {ga}{Ga : Context ga}{n S}

        -> Ga != (n <: S) -> Ga != univ S
        -----------------------------------
        -> Ga != type [ n ]


  rad    : forall {ga}{Ga : Context ga}{t T}

        -> Ga != type T -> Ga != (T :> t)
        ------------------------------------
        -> Ga != ((t :: T) <: T)
           

  eq     : forall {ga}{Ga : Context ga}{T}

        -------------------
        -> Ga != (T ~ T)


  type : forall {R}(rule : R <- formation) -> let open FormationRule R in
         forall {ga}{Ga : Context ga}(ts : Env ([] , atom NIL) (ga ,P typeSuj))
        -> let Jz , _ = premises ga typePrems [] (atom NIL) ts in

           All (Ga !=_) Jz
        --------------------------------
        -> Ga != type (typeSuj %P ts)


  chk  : forall {R}(rule : R <- checking) -> let open CheckingRule R in
         forall {ga}{Ga : Context ga}
         (Ts : Env ([] , atom NIL) (ga ,P chkInp))
         (ts : Env ([] , atom NIL) (ga ,P chkSuj))
        -> let Jz , _ = premises ga chkPrems [] Ts ts in

           All (Ga !=_) Jz
        ----------------------------------------------
        -> Ga != ((chkInp %P Ts) :> (chkSuj %P ts))


  syn  : forall {R}(rule : R <- elimination) -> let open EliminationRule R in
         forall {ga}{Ga : Context ga}(e : Term ([] , atom NIL) ga lib syn)
         (Ss : Env ([] , atom NIL) (ga ,P trgType))
         (ss : Env ([] , atom NIL) (ga ,P elimSuj))
        -> let Jz , trus , _ = premises ga elimPrems ([] -, e) Ss ss in

           Ga != (e <: (trgType %P Ss))
        -> All (Ga !=_) Jz
        -----------------------------------------------------------------
        -> Ga != ((e $ (elimSuj %P ss)) <: (resType % ([] -, e , trus))) 


  unic : forall {R}(rule : R <- universe) -> let open UniverseRule R in
         forall {ga}{Ga : Context ga}
         (Ts : Env ([] , atom NIL) (ga ,P uniInp))
        -> let Jz , _ = premises ga uniPrems [] Ts (atom NIL) in

           All (Ga !=_) Jz
        ----------------------------------------------
        -> Ga != univ (uniInp %P Ts)
