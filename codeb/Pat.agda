module Pat where

open import Basics
open import Bwd
open import Thin
open import SynU

module PAT
 {B S : Set}
 (Cn : S -> Set)(Ds : {s : S} -> Cn s -> Syn B S)(b2s : B -> S)
 (Pc : S -> Set)(pc : {s : S} -> Pc s -> Cn s)
 (cq? : {s : S}(b c : Cn s) -> Dec (b == c))
 where

 open TERM Cn Ds b2s

 data PatR (s : S)(ga : Bwd B) : Set

 Pat : Sort -> Bwd B -> Set
 Pat D = Rlv D PatR

 data PatR s ga where
   hole : Pat (` s) ga
   _-_  : (c : Pc s)(pr : Pat (Ds (pc c)) ga) -> Pat (` s) ga
   nope : PatR s ga

 

 module _ (s : S)(de : Bwd B) where
  data Hole : (D : Sort){ga : Bwd B}(p : Pat D ga) -> Set where
    hole : Hole (` s) {de} hole
    _-_  : {r : S}{ga : Bwd B}(c : Pc r){pr : Pat (Ds (pc c)) ga} ->
           Hole (Ds (pc c)) pr -> Hole (` r) (c - pr)
    inl  : forall {D E}{ga0 ga1 ga}{th0 : ga0 <= ga}{th1 : ga1 <= ga}
           {d : Pat D ga0}{c : Cover th0 th1}{e : Pat E ga1} ->
           Hole D d -> Hole (D *' E) (d <^ c ^> e)
    inr  : forall {D E}{ga0 ga1 ga}{th0 : ga0 <= ga}{th1 : ga1 <= ga}
           {d : Pat D ga0}{c : Cover th0 th1}{e : Pat E ga1} ->
           Hole E e -> Hole (D *' E) (d <^ c ^> e)
    kk   : forall {b D}{ga}{p : Pat D ga} ->
           Hole D p -> Hole (b >' D) (kk p)
    ll   : forall {b D}{ga}{p : Pat D (ga -, b)} ->
           Hole D p -> Hole (b >' D) (ll p)

 Meta : (D : Sort){ga : Bwd B}(p : Pat D ga) -> S * Bwd B -> Set
 Meta D p (s , de) = Hole s de D p

 module _ (M : S * Bwd B -> Set) where

  data StanR {s : S}{ga : Bwd B} : (p : Pat (` s) ga) -> Set
  Stan : forall (k : Sort){ga : Bwd B}(p : Pat k ga) -> Set
  Stan (un') null = One
  Stan (D *' E) (d <^ c ^> e) = Stan D d * Stan E e
  Stan (b >' D) (ll d) = Stan D d
  Stan (b >' D) (kk d) = Stan D d
  Stan (` s) p = StanR p
  
  data StanR {s} {ga} where
    val  : (M !^ ` s) ga -> Stan (` s) hole
    _-_  : (c : Pc s){pr : Pat (Ds (pc c)) ga} ->
           Stan (Ds (pc c)) pr ->
           Stan (` s) (c - pr)
    nope : Stan (` s) nope

  get : forall {D : Sort}{ga}{p : Pat D ga}(m : Stan D p)
        {k} -> Meta D p k -> (M !^ ` fst k) (snd k)
  get (val t) hole = t
  get (.c - m) (c - x) = get m x
  get (m , _) (inl x) = get m x
  get (_ , m) (inr x) = get m x
  get m (kk x) = get m x
  get m (ll x) = get m x
