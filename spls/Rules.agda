module Rules where

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
open import Deriv

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
  redexes = getRedexes checking elimination
  field
    reducts     : All Reduct redexes
    {unambiguousFormation} :
      So (Apart typeSuj formation)
    {unambiguousChecking} :
      So (Apart (\ r -> chkInp r &&& chkSuj r) checking)
    {unambiguousElimination} :
      So (Apart (\ r -> trgType r &&& elimSuj r) elimination)
    {unambiguousUniverse} :
      So (Apart uniInp universe)
  computation : Bwd BetaRule
  computation = fst (betaRules redexes reducts)
  computationUnambiguous :
    Pairwise (\ x y -> (betaIntro x &&& betaType x) &&& betaElim x
                    ~~ (betaIntro y &&& betaType y) &&& betaElim y
                    -> Zero) computation
  computationUnambiguous th u
    with getRedexes checking elimination
       | betaRules redexes reducts
       | noOverlap checking elimination
           (trapa (\ r -> chkInp r &&& chkSuj r) checking
             unambiguousChecking)
           (trapa (\ r -> trgType r &&& elimSuj r) elimination
             unambiguousElimination)
  ... | rz | bz , rbz | rzA with bwdRThin rbz th
  ... | ([] -, (t0 , e0 , Ty0 , _) -, (t1 , e1 , Ty1 , _)) , ph
      , [] -, (refl , refl , refl) -, (refl , refl , refl) = rzA ph u

module TYPETHEORY {TH : TypeTheory}{M : Meta} where
  open TypeTheory TH

  data _~>_ {ga} : forall {d}(t t' : Term M ga lib d) -> Set
  data _~z>_ {ga} : forall {de : Nat}
                      (ez ez' : All (\ _ -> Term M ga lib syn) de) -> Set

  data _~>_ {ga} where

      car  : forall {s s' t} -> s ~> s' -> (s & t) ~> (s' & t)
      cdr  : forall {s t t'} -> t ~> t' -> (s & t) ~> (s & t')
      abst : forall {t t'} -> t ~> t' -> (\\ t) ~> (\\ t')
      thnk : forall {n e} -> essl n ~> e -> thnk n ~> [ e ]
      targ : forall {e e' s} -> e ~> e' -> (e $ s) ~> (e' $ s)
      elim : forall {e s s'} -> s ~> s' -> (e $ s) ~> (e $ s')
      term : forall {t t' T} -> t ~> t' -> (t :: T) ~> (t' :: T)
      type : forall {t T T'} -> T ~> T' -> (t :: T) ~> (t :: T')
      meta : forall {de}{x : de <P- snd M}
        {ez ez' : All (\ _ -> Term M ga lib syn) de} ->
        ez ~z> ez' -> (x ?- ez) ~> (x ?- ez')
      beta : forall {R}(x : R <- computation) -> let open BetaRule R in
        (ts : Env M (ga ,P betaIntro)) ->
        (Ts : Env M (ga ,P betaType)) ->
        (ss : Env M (ga ,P betaElim)) ->
        (((betaIntro %P ts) :: (betaType %P Ts)) $ (betaElim %P ss))
          ~>
        ((redTerm % ([] , (ts &&& Ts) &&& ss))
          :: (redType % ([] , (ts &&& Ts) &&& ss)))

  data _~z>_ {ga} where
    
      llll : forall {de}{ez ez' : All _ de}{e} ->
              ez ~z> ez' -> (ez -, e) ~z> (ez' -, e)
      rrrr : forall {de}{ez : All _ de}{e e'} ->
              e ~> e' -> (ez -, e) ~z> (ez -, e')

  data _=>_ {ga} : forall {d}(t t' : Term M ga lib d) -> Set
  data _=z>_ {ga} : forall {de}(ez ez' : All (\ _ -> Term M ga lib syn) de) -> Set
  data _=P>_ {ga}{de} : forall {p : Pat de}(ts ts' : Env M (ga ,P p)) -> Set

  data _=>_ {ga} where

      atom : (a : Atom) -> (! a) => (! a)
      cons : forall {s s' t t'} -> s => s' -> t => t' -> (s & t) => (s' & t')
      abst : forall {t t'} -> t => t' -> (\\ t) => (\\ t')
      thnk : forall {n e} -> essl n => e -> thnk n => [ e ]
      vari : forall i -> (# i) => (# i)
      mets : forall x -> essl (mets x) => essl (mets x)
      elim : forall {e e' s s'} -> e => e' -> s => s' -> (e $ s) => (e' $ s')
      radi : forall {t t' T T'} -> t => t' -> T => T' -> (t :: T) => (t' :: T')
      _?-_ : forall {de}(x : de <P- snd M) ->
             {ez ez' : All (\ _ -> Term M ga lib syn) de} ->
             ez =z> ez' -> (x ?- ez) => (x ?- ez')
      beta : forall {R}(x : R <- computation) -> let open BetaRule R in
        {ts ts' : Env M (ga ,P betaIntro)} ->
        {Ts Ts' : Env M (ga ,P betaType)} ->
        {ss ss' : Env M (ga ,P betaElim)} ->
        ts =P> ts' -> Ts =P> Ts' -> ss =P> ss' ->
        (((betaIntro %P ts) :: (betaType %P Ts)) $ (betaElim %P ss))
          =>
        ((redTerm % ([] , (ts' &&& Ts') &&& ss'))
          :: (redType % ([] , (ts' &&& Ts') &&& ss')))

  data _=z>_ {ga} where

      [] : [] =z> []
      _-,_ : forall {de}{ez ez' : All _ de}{e e'} -> ez =z> ez' -> e => e' ->
             (ez -, e) =z> (ez' -, e')

  data _=P>_ {ga}{de} where

      !!!_ : (a : Atom) -> !!! a =P> !!! a
      _&&&_ : forall {p q : Pat de}{tp tp' : Env M (ga ,P p)}{tq tq' : Env M (ga ,P q)}
             -> tp =P> tp' -> tq =P> tq' -> tp &&& tq =P> tp' &&& tq'
      \\\_ : forall {q}{tq tq' : Env M (ga ,P q)} -> tq =P> tq' -> \\\ tq =P> \\\ tq'
      ??? : forall {x}{de'}{th : de' <= de}{t t'} -> t => t' ->
             _=P>_ {p = ??? x th} (??? t) (??? t')


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
        -> let Jz , _ = premises ga typePrems [] NIL ts in

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
        -> Ga != ((e $ (elimSuj %P ss)) <: (resType % ([] -, e , Ss &&& trus))) 


      unic : forall {R}(rule : R <- universe) -> let open UniverseRule R in
         forall 
         (Ts : Env M (ga ,P uniInp))
        -> let Jz , _ = premises ga uniPrems [] Ts NIL in

           All (Ga !=_) Jz
        ----------------------------------------------
        -> Ga != univ (uniInp %P Ts)
