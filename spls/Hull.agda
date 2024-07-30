module Hull where

open import Basics
open import Eq
open import Atom
open import Bwd
open import All
open import Cats
open import Pat
open import Ref
open import Term
open import Action
open import Thin
open import Supp
open import ActCats

open Monoidal (OPEMON {One})
open Cat (OPE {One})
open Act THIN

thinMatch : forall {M de ga ga'}(p : Pat ga)(th : ga <= ga')
  (pi' : Env M (de ,P (p ^P th))) ->
  Sg (Env M (de ,P p)) \ pi -> ((p %P pi) ^ (oi ^+ th)) == ((p ^P th) %P pi')
thinMatch (!!! a) th (!!! .a) = !!! a , refl
thinMatch (p &&& q) th (pi' &&& chi') with thinMatch p th pi' | thinMatch q th chi'
... | pi , q0 | chi , q1 = pi &&& chi , _&_ $= q0 =$= q1
thinMatch (\\\ q) th (\\\ chi') with thinMatch q (th su) chi'
... | chi , q0 = \\\ chi , \\_ $= q0
thinMatch (??? _ ph) th (??? t) = ??? t ,
  ((t ^ (oi ^+ ph)) ^ (oi ^+ th))
    =[ thinco t _ _ >=
  (t ^ ((oi ^+ ph) -< (oi ^+ th)))
    =[ (t ^_) $= (
        ((oi ^+ ph) -< (oi ^+ th))
          =[ moco oi ph oi th >=
        ((oi -< oi) ^+ (ph -< th))
          =[ (_^+ (ph -< th)) $= idcoC _ >=
        (oi ^+ (ph -< th))
          [QED]) >=
  (t ^ (oi ^+ (ph -< th)))
    [QED] 

refineMatch : forall {M de ga}{p' p : Pat ga}(r : p' <P= p)(pi' : Env M (de ,P p')) ->
  Sg (Env M (de ,P p)) \ pi -> (p %P pi) == (p' %P pi')
refineMatch (!!! a) (!!! .a) = !!! a , refl
refineMatch (r0 &&& r1) (pi' &&& chi') with refineMatch r0 pi' | refineMatch r1 chi'
... | pi , q0 | chi , q1 = pi &&& chi , _&_ $= q0 =$= q1
refineMatch (\\\ r) (\\\ chi') with refineMatch r chi'
... | chi , q = \\\ chi , \\_ $= q
refineMatch (??? {th = th} p refl) pi' with thinMatch p th pi'
... | pi , q = ??? (p %P pi) , q

data Match {M ga} : Pat ga -> Term M ga lib chk -> Set where
  !!!_ : forall a -> Match (!!! a) (! a)
  _&&&_ : forall {p q s t} -> Match p s -> Match q t -> Match (p &&& q) (s & t)
  \\\_ : forall {q t} -> Match q t -> Match (\\\ q) (\\ t)
  ??? : forall {x}{de}{th : de <= ga}{t t'} -> t <[ th ]= t' -> Match (??? x th) t'

match : forall {M ga de}(p : Pat de)(pi : Env M (ga ,P p)) -> Match (ga ,P p) (p %P pi)
match (!!! a) (!!! .a) = !!! a
match (p &&& q) (pi &&& chi) = match p pi &&& match q chi
match (\\\ q) (\\\ chi) = \\\ match q chi
match (??? _ th) (??? t) = ??? (thinR t (oi ^+ th))

matchQ : forall {M ga de}(p : Pat de)(pi : Env M (ga ,P p))(t : Term M (ga -+ de) lib chk)
 -> (p %P pi) == t -> Match (ga ,P p) t
matchQ p pi _ refl = match p pi

holeU : forall {ga de}{x}(th : ga <= de)(p : Pat de) -> ??? x th ~~ p
holeU {ga}{de} th p = (th ?P p) ^P th , ??? (th ?P p) refl , squeezeRefine th p

matchU : forall {M ga de}(p : Pat de)(ss : Env M (ga ,P p))
                         (q : Pat de)(ts : Env M (ga ,P q)) ->
                         p %P ss == q %P ts -> p ~~ q
matchU {ga = ga} (!!! .a) (!!! .a) (!!! a) (!!! .a) refl = !!! a , !!! a , !!! a
matchU {ga = ga} (!!! a) (!!! .a) (_ &&& _) (_ &&& t_) ()
matchU {ga = ga} (!!! a) (!!! .a) (\\\ q) (\\\ ts) ()
matchU {ga = ga} p ss (??? _ th) ts e with holeU th p
... | u , r0 , r1 = u , r1 , r0
matchU {ga = ga} (p &&& q) (ss &&& _) (!!! a) (!!! .a) ()
matchU {ga = ga} (p &&& q) (ss &&& ts) (p' &&& q') (ss' &&& ts') e = termNoConf e \ e -> termNoConf e \ e0 e1 ->
  let u0 , r0 , r1 = matchU p ss p' ss' e0 in
  let u1 , r2 , r3 = matchU q ts q' ts' e1 in
  u0 &&& u1 , r0 &&& r2 , r1 &&& r3
matchU {ga = ga} (p &&& q) (_ &&& _) (\\\ _) (\\\ ts) ()
matchU {ga = ga} (\\\ p) (\\\ ss) (!!! a) (!!! .a) ()
matchU {ga = ga} (\\\ p) (\\\ ss) (_ &&& _) (_ &&& _) ()
matchU {ga = ga} (\\\ p) (\\\ ss) (\\\ q) (\\\ ts) e = termNoConf e \ e -> termNoConf e \ e ->
  let u , r0 , r1 = matchU p ss q ts e in \\\ u , \\\ r0 , \\\ r1
matchU {ga = ga} (??? _ th) (??? s) q ts e = holeU th q

matchUnique : forall {M ga de}(p : Pat de)(ss ts : Env M (ga ,P p))
                 ->    p %P ss == p %P ts -> ss == ts
matchUnique (!!! a) (!!! .a) (!!! .a) z = refl
matchUnique (p &&& q) (ss &&& ss') (ts &&& ts') z = termNoConf z \ z -> termNoConf z \ z0 z1 ->
  _&&&_ $= matchUnique p ss ts z0 =$= matchUnique q ss' ts' z1
matchUnique (\\\ p) (\\\ ss) (\\\ ts) z = termNoConf z \ z -> termNoConf z \ z ->
  \\\_ $= matchUnique p ss ts z
matchUnique (??? _ th) (??? s) (??? t) z = ??? $= thinMonoTerm s t (oi ^+ th) z
