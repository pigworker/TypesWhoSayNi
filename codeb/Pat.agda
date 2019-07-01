module Pat where

open import Basics
open import Bwd
open import Thin
open import SynU

module PAT
 {B S : Set}
 (Cn : S -> Set)(Ds : {s : S} -> Cn s -> Syn B S)(b2s : B -> S)
 (Pc : S -> Set)(pc : {s : S} -> Pc s -> Cn s)
 (cq? : {s : S}(b c : Cn s) -> Dec (b ~ c))
 where

 open TERM Cn Ds b2s

 data PatR (s : S)(ga : Bwd B) : Set

 Pat : Sort -> Bwd B -> Set
 Pat D = Rlv D PatR

 data PatR s ga where
   hole : Pat (` s) ga
   _-_  : (c : Pc s)(pr : Pat (Ds (pc c)) ga) -> Pat (` s) ga

 Pam : Sort -> Bwd B -> Set
 Pam D ga = Maybe (Pat D :< ga)

 data _<P=_ {s ga} : (r p : Pat (` s) :< ga) -> Set
 
 Refiny : forall D {ga}(r p : Pat D :< ga) -> Set
 Refiny un'      r p = One
 Refiny (D *' E) (dr </ ur \> er ^ th) (dp </ up \> ep ^ ph) =
   Refiny D (dr ^ u/ ur -<- th) (dp ^ u/ up -<- ph) *
   Refiny E (er ^ u\ ur -<- th) (ep ^ u\ up -<- ph)
 Refiny (b >' D) (ll r ^ th) (ll p ^ ph) =
   Refiny D (r ^ th -, b) (p ^ ph -, b)
 Refiny (b >' D) (ll r ^ th) (kk p ^ ph) = Zero
 Refiny (b >' D) (kk r ^ th) (ll p ^ ph) =
   Refiny D (r ^ th -^ b) (p ^ ph -, b)
 Refiny (b >' D) (kk r ^ th) (kk p ^ ph) =
   Refiny D (r ^ th) (p ^ ph)
 Refiny (` s)    r p = r <P= p

 Refine : forall D {ga}(r p : Pam D ga) -> Set
 Refine D no      _       = One
 Refine D (yes r) no      = Zero
 Refine D (yes r) (yes p) = Refiny D r p

 infix 3 _<P=_
 data _<P=_ {s ga} where
   hole : forall {de}{r : Pat (` s) :< ga}{ph : de <= ga} ->
          <(_& ph =< thin r)> ->
          r <P= hole ^ ph
   _-_  : forall (c : Pc s){r p} -> Refiny (Ds (pc c)) r p ->
          ((c -_) :$ r) <P= ((c -_) :$ p)

 module _ (s : S)(de : Bwd B) where
  data Hole : (D : Sort){ga : Bwd B}(p : Pat D ga) -> Set where
    hole : Hole (` s) {de} hole
    _-_  : forall {r ga} c {pr : Pat (Ds (pc c)) ga} ->
           Hole (Ds (pc c)) pr -> Hole (` r) (c - pr)
    inl  : forall {D E ga0 ga1 ga}{th0 : ga0 <= ga}{th1 : ga1 <= ga}
           {d : Pat D ga0}{c : th0 /u\ th1}{e : Pat E ga1} ->
           Hole D d -> Hole (D *' E) (d </ c \> e)
    inr  : forall {D E ga0 ga1 ga}{th0 : ga0 <= ga}{th1 : ga1 <= ga}
           {d : Pat D ga0}{c : th0 /u\ th1}{e : Pat E ga1} ->
           Hole E e -> Hole (D *' E) (d </ c \> e)
    kk   : forall {b D ga}{p : Pat D ga} ->
           Hole D p -> Hole (b >' D) (kk p)
    ll   : forall {b D ga}{p : Pat D (ga -, b)} ->
           Hole D p -> Hole (b >' D) (ll p)

 Meta : (D : Sort){ga : Bwd B}(p : Pat D ga) -> S * Bwd B -> Set
 Meta D p (s , de) = Hole s de D p

 module _ (M : S * Bwd B -> Set) where

  data StanR {s : S}{ga : Bwd B} : (p : Pat (` s) ga) -> Set
  Stan : forall (D : Sort){ga : Bwd B}(p : Pat D ga) -> Set
  Stan un'      null          = One
  Stan (D *' E) (d </ c \> e) = Stan D d * Stan E e
  Stan (b >' D) (ll d)        = Stan D d
  Stan (b >' D) (kk d)        = Stan D d
  Stan (` s)    p             = StanR p

  data StanR {s ga} where
    val  : (M !< ` s) ga -> Stan (` s) hole
    _-_  : (c : Pc s){pr : Pat (Ds (pc c)) ga} ->
           Stan (Ds (pc c)) pr ->
           Stan (` s) (c - pr)

  get : forall {D : Sort}{ga}{p : Pat D ga}(m : Stan D p)
        {k} -> Meta D p k -> (M !< ` fst k) (snd k)
  get (val t) hole = t
  get (.c - m) (c - x) = get m x
  get (m , _) (inl x) = get m x
  get (_ , m) (inr x) = get m x
  get m (kk x) = get m x
  get m (ll x) = get m x

  stan : forall D {ga}(p : Pat D ga)(pi : Stan D p) -> (M !< D) ga
  stan un'      null           <> = null ^ []
  stan (D *' E) (p </ c \> r)  (pi , rh) =
    stan D p pi :- u/ c /,\ stan E r rh :- u\ c
  stan (b >' D) (ll p)         pi = b \\ stan D p pi
  stan (b >' D) (kk p)         pi = kk :$ stan D p pi
  stan (` s)    hole      (val t) = t
  stan (` s)    (c - p) (.c - pi) = (pc c -_) :$ stan (Ds (pc c)) p pi

  data Match : forall D {ga}(p : Pat D ga)(pi : Stan D p) -> (M !< D) ga ->
               Set where
    hoMa : forall {s ga}{t : (M !< ` s) ga} -> Match (` s) hole (val t) t
    cnMa : forall {s ga}(c : Pc s){p : Pat (Ds (pc c)) ga}
           {pi : Stan (Ds (pc c)) p}{t : (M !< Ds (pc c)) ga} ->
           Match (Ds (pc c)) p pi t ->
           Match (` s) (c - p) (c - pi) ((pc c -_) :$ t)
    unMa : Match un' null <> (null ^ [])
    prMa : forall {D E ga ga0 ga1}{ph0 : ga0 <= ga}{ph1 : ga1 <= ga}
           {pd : Pat D ga0}{pu : ph0 /u\ ph1}{pe : Pat E ga1}
           {pid : Stan D pd}{pie : Stan E pe}
           {de0 de1}{td : (M ! D) de0}{te : (M ! E) de1}
           {th0 : de0 <= ga0}{th1 : de1 <= ga1}
           {de}{th : de <= ga}{ps0 : de0 <= de}{ps1 : de1 <= de}
           {tu : ps0 /u\ ps1} ->
           Square (ps0 ^ th) (th0 ^ ph0) -> Match D pd pid (td ^ th0) ->
           Square (ps1 ^ th) (th1 ^ ph1) -> Match E pe pie (te ^ th1) ->
           Match (D *' E) (pd </ pu \> pe) (pid , pie) (td </ tu \> te ^ th)
    kkMa : forall {b D ga}{p : Pat D ga}{pi : Stan D p}{t : (M !< D) ga} ->
           Match D p pi t -> Match (b >' D) (kk p) pi (kk :$ t)
    llMa : forall {b D ga}{p : Pat D (ga -, b)}{pi : Stan D p}
           {t : (M !< D) (ga -, b)} ->
           Match D p pi t -> Match (b >' D) (ll p) pi (b \\ t) -- green slime

  stanMa : forall D {ga}(p : Pat D ga) pi -> Match D p pi (stan D p pi)
  stanMa un' null <> = unMa
  stanMa (D *' E) (pd </ pu \> pe) (pid , pie)
    with stan D pd pid | stanMa D pd pid | stan E pe pie | stanMa E pe pie
  ... | td ^ th0 | dh | te ^ th1 | eh
    with th0 -<- u/ pu | th0 -&- u/ pu | th1 -<- u\ pu | th1 -&- u\ pu
  ... | ch0 | v0 | ch1 | v1 with ch0 /+\ ch1
  ... | (! ps0 , th , ps1) , w0 , w1 , tu = prMa (w0 ^ v0) dh (w1 ^ v1) eh
  stanMa (b >' D) (ll p) pi = llMa (stanMa D p pi)
  stanMa (b >' D) (kk p) pi = kkMa (stanMa D p pi)
  stanMa (` s) hole (val t) = hoMa
  stanMa (` s) (c - p) (.c - pi) = cnMa c (stanMa _ p pi)


  Stam : forall D {ga} (p : Pam D ga) -> Set
  Stam D no            = Zero
  Stam D (yes (p ^ _)) = Stan D p

  -- this is insufficiently coherent
  reifine : forall D {ga}(r p : Pam D ga) ->
    Refine D r p -> Stam D r -> Stam D p
  reifine D no p rp ()
  reifine D (yes x) no () rh
  reifine D (yes r) (yes p) rp rh = {!!}
 
