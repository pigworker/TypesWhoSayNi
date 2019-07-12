------------------------------------------------------------------------------
-----                                                                    -----
-----     Syntax.Pat                                                     -----
-----                                                                    -----
------------------------------------------------------------------------------

module Syntax.Pat where

open import Lib.Zero
open import Lib.One
open import Lib.Equality
open import Lib.Pi
open import Lib.Sigma
open import Lib.Sum
open import Lib.Index
open import Lib.Bwd
open import Lib.Maybe
open import Thin.Data
open import Thin.Select
open import Thin.Triangle
open import Thin.Thinned
open import Thin.Cover
open import Thin.Pullback
open import Relevant.Pair
open import Relevant.Abstraction
open import Syntax.Desc

module _
  (B : Set) -- what binders are like
  (S : Set) -- what sorts exist
  (b2s : B -> S)  -- what sort of thing each binder binds
 where
 open THIN {B}
 open DESC B S b2s
 module _
  (Cn : S -> Set) -- what constructors exist for each sort
  (Ds : {s : S} -> Cn s -> Desc)
  (Pc : S -> Set) -- which constructors are allowed in patterns
  (pc : {s : S} -> Pc s -> Cn s)
  where

  data Ptn (s : S)(ga : Scope) : Set
  
  Pn : Desc -> Scope -> Set
  Pn = CdB Ptn
  
  data Ptn s ga where
    hole : Pn (` s) ga
    _$_  : (c : Pc s) -> Pn (Ds (pc c)) ga -> Pn (` s) ga

  MP : Desc -> Scope -> Set
  MP D ga = Maybe (Pn D :< ga)

  data DBMP {ga} : forall D -> MP D ga -> Set where
    no   : forall {D} -> DBMP D no
    null : DBMP un' (yes (null ^ noth))
    _,_  : forall {D E d e} -> DBMP D (yes d) -> DBMP E (yes e) ->
            DBMP (D *' E) (yes (d /,\ e))
    _\\\_ : forall b {D d} -> DBMP D (yes d) -> DBMP (b >' D) (yes (b \\ d))
    hole : forall {s de}(th : de <= ga) -> DBMP (` s) (yes (hole ^ th))
    _$_ : forall {s}(c : Pc s){d} -> DBMP (Ds (pc c)) (yes d) ->
           DBMP (` s) (yes ((c $_) :$ d))

  psupp : forall {D ga de}{th : ga <= de}{p : Pn D ga} ->
          DBMP D (yes (p ^ th)) -> ga <= de
  psupp {th = th} _ = th

  dBMP : forall D {ga}(p : MP D ga) -> DBMP D p
  dBP  : forall D {ga de}(p : Pn D ga)(th : ga <= de) -> DBMP D (yes (p ^ th))
  dBMP D no = no
  dBMP D (yes (p ^ th)) = dBP D p th
  dBP un'      null          th with noth! th noth ; ... | r~ = null
  dBP (D *' E) (d </ u \> e) th =
    (dBP D d (u/ u -<- th) , dBP E e (u\ u -<- th))
    :[ DBMP (D *' E) $~ (yes $~ fst (prPr ~Pr~ covPr)) >
  dBP (b >' D) (ll p)        th = b \\\ dBP D p (th -, b)
  dBP (b >' D) (kk p)        th = b \\\ dBP D p (th -^ b)
  dBP (` s)    hole          th = hole th
  dBP (` s)    (c $ p)       th = c $ dBP (Ds (pc c)) p th

  infix 3 _::_<MP=_ _<P=_
  
  _<P=_  : forall {D ga}{r p : MP D ga} -> DBMP D r -> DBMP D p -> Set  
  _<P=_ {r = no}           _ _         = One
  _<P=_ {r = yes (r ^ th)} _ (hole ph) = <(_& ph =< th)>
  r         <P= no         = Zero
  hole th   <P= _          = Zero
  null      <P= null       = One
  (dr , er) <P= (dp , ep)  = dr <P= dp * er <P= ep 
  (b \\\ r) <P= (.b \\\ p) = r <P= p
  (c $ r)   <P= (c' $ p)   = c ~ c' >< \ { r~ -> r <P= p }

  _::_<MP=_ : forall D {ga} -> MP D ga -> MP D ga -> Set
  D :: r <MP= p = dBMP D r <P= dBMP D p
  
  pat<= : forall {D ga}{r p : Pn D :< ga}
    (r' : DBMP D (yes r))(p' : DBMP D (yes p)) ->
    r' <P= p' -> <(_& thin p =< thin r)>
  pat<= r (hole th) rp = rp
  pat<= null null rp = ! no& _
  pat<= (dr , er) (dp , ep) (drp , erp)
    with pat<= dr dp drp | pat<= er ep erp       ; ... | ! dv | ! ev
    with psupp dp /+\ psupp ep                   ; ... | ! ! dpv , epv , pu
    with assoc02 (dv ^ dpv) | assoc02 (ev ^ epv) ; ... | _ ^ dw | _ ^ ew
    with copU dw ew (psupp dr /+\ psupp er)      ; ... | ! _ , v , _
    = ! v
  pat<= (.b \\\ r) (b \\\ p) rp with pat<= r p rp
  ... | ! (v -, .b) = ! v
  ... | ! v -^, .b  = ! v
  ... | ! (v -^ .b) = ! v
  pat<= (c $ r) (.c $ p) (r~ , rp) = pat<= r p rp
  pat<= (hole th) (c $ p) ()


{-

  unify : forall D {ga}(p q : MP D ga) -> <(D ::_<MP= p) :* (D ::_<MP= q)>
  unify' : forall D {ga}(p q : Pn D :< ga) ->
    <(D ::_<MP= yes p) :* (D ::_<MP= yes q)>
  unify D no      q       = no , _
  unify D (yes _) no      = no , _
  unify D (yes p) (yes q) = unify' D p q
  unify' un' (null ^ th) (null ^ ph) = yes (null ^ noth) , _
  unify' (D *' E) (dp </ up \> ep ^ th) (dq </ uq \> eq ^ ph)
    with unify' D (dp ^ u/ up -<- th) (dq ^ u/ uq -<- ph)
       | unify' E (ep ^ u\ up -<- th) (eq ^ u\ uq -<- ph)
  ... | no , _ | _ = no , _
  ... | _ | no , _ = no , _
  ... | yes dr , dpr , dqr | yes er , epr , eqr
    = yes (dr /,\ er) , help where
    help : (D :: (dr /,\ er) -/ <P= dp ^ u/ up -<- th *
            E :: (dr /,\ er) -\ <P= ep ^ u\ up -<- th)
         * (D :: (dr /,\ er) -/ <P= dq ^ u/ uq -<- ph *
            E :: (dr /,\ er) -\ <P= eq ^ u\ uq -<- ph)
    help rewrite fstQ dr er | sndQ dr er = (dpr , epr) , (dqr , eqr)

  -- can't use the view because tc -- build de Bruijn recursor?
  unify' (b >' D) (ll p ^ th) (ll q ^ ph)
    with unify' D (p ^ th -, b) (q ^ ph -, b)
  ... | no , _ = no , _
  ... | yes r , pr , qr = yes (b \\ r) , help where
    help : (b >' D) :: (b \\ r) <P= (ll p ^ th) *
           (b >' D) :: (b \\ r) <P= (ll q ^ ph)
    help rewrite under\\ b r = pr , qr
  unify' (b >' D) (ll p ^ th) (kk q ^ ph)
    with unify' D (p ^ th -, b) (q ^ ph -^ b)
  ... | no , _ = no , _
  ... | yes r , pr , qr = yes (b \\ r) , help where
    help : (b >' D) :: (b \\ r) <P= (ll p ^ th) *
           (b >' D) :: (b \\ r) <P= (kk q ^ ph)
    help rewrite under\\ b r = pr , qr
  unify' (b >' D) (kk p ^ th) (ll q ^ ph)
    with unify' D (p ^ th -^ b) (q ^ ph -, b)
  ... | no , _ = no , _
  ... | yes r , pr , qr = yes (b \\ r) , help where
    help : (b >' D) :: (b \\ r) <P= (kk p ^ th) *
           (b >' D) :: (b \\ r) <P= (ll q ^ ph)
    help rewrite under\\ b r = pr , qr
  unify' (b >' D) (kk p ^ th) (kk q ^ ph)
    with unify' D (p ^ th -^ b) (q ^ ph -^ b)
  ... | no , _ = no , _
  ... | yes r , pr , qr = yes (b \\ r) , help where
    help : (b >' D) :: (b \\ r) <P= (kk p ^ th) *
           (b >' D) :: (b \\ r) <P= (kk q ^ ph)
    help rewrite under\\ b r = pr , qr
  unify' (DESC.` s) (p0 ^ th) (p1 ^ ph) = {!!}
-}
