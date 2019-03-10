module Par where

open import Basics
open import Eq
open import Fun
open import Bwd
open import All
open import Atom
open import Pat
open import Term
open import Thin
open import Deriv
open import Stab
open import Supp
open import Hull
open import ActCats

data Star {X}(R : X -> X -> Set)(x : X) : X -> Set where
  [] : Star R x x
  _,-_ : forall {y z} -> R x y -> Star R y z -> Star R x z

_*+_ : forall {X}{R : X -> X -> Set}{x0 x1 x2} ->
       Star R x0 x1 -> Star R x1 x2 -> Star R x0 x2
[] *+ rs' = rs'
(r ,- rs) *+ rs' = r ,- (rs *+ rs')

infixr 40 _*+_

bind* : forall {X Y}(f : X -> Y){R : X -> X -> Set}{S : Y -> Y -> Set} ->
  ({x0 x1 : X} -> R x0 x1 -> Star S (f x0) (f x1)) ->
  forall {x0 x1} -> Star R x0 x1 -> Star S (f x0) (f x1)
bind* f g [] = []
bind* f g (r ,- rs) = g r *+ bind* f g rs

star : forall {X Y}(f : X -> Y){R : X -> X -> Set}{S : Y -> Y -> Set} ->
  ({x0 x1 : X} -> R x0 x1 -> S (f x0) (f x1)) ->
  forall {x0 x1} -> Star R x0 x1 -> Star S (f x0) (f x1)
star f g = bind* f ((_,- []) ` g) 


pam : forall {M ga}(p : Pat ga)(t : Term M ga lib chk) -> Dec (Match p t)
pam (atom a) (! a') with atomEq? a a'
pam (atom a) (! a') | #0 , r = #0 , \ { (atom a) -> r refl }
pam (atom a) (! .a) | #1 , refl = #1 , atom a
pam (atom a) (_ & _) = #0 , \ ()
pam (atom a) (\\ _) = #0 , \ ()
pam (atom a) (thnk _) = #0 , \ ()
pam (atom a) (_ ?- _) = #0 , \ ()
pam (p - q) (! _) = #0 , \ ()
pam (p - q) (s & t) with pam p s | pam q t
pam (p - q) (s & t) | #0 , pr | qb , qr = #0 , \ { (cons py _) -> pr py }
pam (p - q) (s & t) | #1 , pr | #0 , qr = #0 , \ { (cons _ qy) -> qr qy }
pam (p - q) (s & t) | #1 , pr | #1 , qr = #1 , cons pr qr
pam (p - q) (\\ _) = #0 , \ ()
pam (p - q) (thnk t) = #0 , \ ()
pam (p - q) (_ ?- _) = #0 , \ ()
pam (\\\ q) (! _) = #0 , \ ()
pam (\\\ q) (_ & _) = #0 , \ ()
pam (\\\ q) (\\ t) with pam q t
pam (\\\ q) (\\ t) | #0 , r = #0 , \ { (abst y) -> r y }
pam (\\\ q) (\\ t) | #1 , r = #1 , abst r
pam (\\\ q) (thnk _) = #0 , \ ()
pam (\\\ q) (_ ?- _) = #0 , \ ()
pam (hole th) t with thickR? th t
pam (hole th) t | #0 , z = #0 , \ { (hole x) -> z (_ , x) }
pam (hole th) t | #1 , s , st = #1 , hole st


module PARALLEL (TH : TypeTheory) where

  open TYPETHEORY TH
  open STABTHIN TH
  open TypeTheory TH
  open BetaRule

  parThnk : forall {M ga}{e e' : Term M ga lib syn} -> e => e' -> [ e ] => [ e' ]
  parThnk (vari i) = thnk (vari i)
  parThnk (mets x) = thnk (mets x)
  parThnk (elim e s) = thnk (elim e s)
  parThnk (radi t T) = t
  parThnk (beta x ts Ts ss) = thnk (beta x ts Ts ss)

  reflPar : forall {M ga d}(t : Term M ga lib d) -> t => t
  reflParThnk : forall {M ga}(n : Term M ga ess syn) -> essl n => essl n
  reflParz : forall {M}{ga de}(ez : All (\ _ -> Term M ga lib syn) de) ->
    ez =z> ez
  reflParP : forall {M ga de}{p : Pat de}(ts : Env M (ga ,P p)) -> ts =P> ts
  reflParP {p = atom a} (atom .a) = atom a
  reflParP {p = p - q} (cons ss ts) = cons (reflParP ss) (reflParP ts)
  reflParP {p = \\\ q} (abst ts) = abst (reflParP ts)
  reflParP {p = hole th} (hole t) = hole (reflPar t)

  reflPar (! a) = atom a
  reflPar (s & t) = cons (reflPar s) (reflPar t)
  reflPar (\\ t) = abst (reflPar t)
  reflPar {d = syn} (essl n) = reflParThnk n
  reflPar (thnk n) = thnk (reflParThnk n)
  reflPar (t :: T) = radi (reflPar t) (reflPar T)
  reflPar (x ?- ez) = x ?- reflParz ez
  reflParThnk (vari i) = vari i
  reflParThnk (elim e s) = elim (reflPar e) (reflPar s)
  reflParThnk (mets x) = mets x
  reflParz [] = []
  reflParz (ez -, e) = reflParz ez -, reflPar e

  redPar : forall {M ga d}{t t' : Term M ga lib d} -> t ~> t' -> t => t'
  redParz : forall {M ga de}{ez ez' : All (\ _ -> Term M ga lib syn) de} ->
              ez ~z> ez' -> ez =z> ez'
  redPar (car s) = cons (redPar s) (reflPar _)
  redPar (cdr t) = cons (reflPar _) (redPar t)
  redPar (abst t) = abst (redPar t)
  redPar (thnk t) = thnk (redPar t)
  redPar (targ e) = elim (redPar e) (reflPar _)
  redPar (elim s) = elim (reflPar _) (redPar s)
  redPar (term t) = radi (redPar t) (reflPar _)
  redPar (type T) = radi (reflPar _) (redPar T)
  redPar (meta ez) = _ ?- redParz ez
  redPar (beta x ts Ts ss) = beta x (reflParP ts) (reflParP Ts) (reflParP ss)
  redParz (llll ez) = redParz ez -, reflPar _
  redParz (rrrr e) = reflParz _ -, redPar e

  redThnk : forall {M ga}{e e' : Term M ga lib syn} ->
        e ~> e' -> Star _~>_ [ e ] [ e' ]
  redThnk (targ e) = thnk (targ e) ,- []
  redThnk (elim e) = thnk (elim e) ,- []
  redThnk (term e) = e ,- []
  redThnk (type e) = []
  redThnk (beta x ts Ts ss) = thnk (beta x ts Ts ss) ,- []

  parReds : forall {M ga d}{t t' : Term M ga lib d} -> t => t' -> Star _~>_ t t'
  parRedsz : forall {M ga de}{ez ez' : All (\ _ -> Term M ga lib syn) de} ->
    ez =z> ez' -> Star _~z>_ ez ez'
  parRedsP : forall {M ga de}{p : Pat de}{ts ts' : Env M (ga ,P p)} ->
    ts =P> ts' -> Star _~>_ (p %P ts) (p %P ts')
  parReds (atom a) = []
  parReds (cons s t) = star (_& _) car (parReds s) *+ star (_ &_) cdr (parReds t) 
  parReds (abst t) = star (\\_) abst (parReds t)
  parReds (thnk n) = bind* [_] redThnk (parReds n)
  parReds (vari i) = []
  parReds (mets x) = []
  parReds (elim e s) = star (_$ _) targ (parReds e) *+ star (_ $_) elim (parReds s)
  parReds (radi t T) = star (_:: _) term (parReds t) *+ star (_ ::_) type (parReds T)
  parReds (x ?- ez) = star (x ?-_) meta (parRedsz ez)
  parReds (beta x ts Ts ss) = 
    star (\ t -> (t :: _) $ _) (targ ` term) (parRedsP ts) *+
    star (\ T -> (_ :: T) $ _) (targ ` type) (parRedsP Ts) *+
    star (\ s -> (_ :: _) $ s) elim (parRedsP ss) *+
    (beta x _ _ _ ,- [])
  parRedsz [] = []
  parRedsz (ez -, e) = star (_-, _) llll (parRedsz ez)
                    *+ star (_ -,_) rrrr (parReds e)
  parRedsP {p = atom a} (atom .a) = []
  parRedsP {p = p - q} (cons ss ts) =
    star (_& _) car (parRedsP ss) *+ star (_ &_) cdr (parRedsP ts)
  parRedsP {p = \\\ q} (abst ts) = star (\\_) abst (parRedsP ts)
  parRedsP {p = hole th} (hole t) =
    star (_^ (oi ^+ th)) (\ t -> redThin t (oi ^+ th)) (parReds t)

  Parallelogram : forall {M ga d} ->
    (R S : Term M ga lib d -> Term M ga lib d -> Set) -> Set
  Parallelogram R S = forall {t t0 t1} -> R t t0 -> S t t1 ->
    Sg _ \ t' -> S t0 t' * R t1 t'

  module CONFLUENCE (pard : forall {M ga d} -> Parallelogram {M}{ga}{d} _=>_ _=>_) where

    stripLemma : forall {M ga d} -> Parallelogram {M}{ga}{d} _=>_ (Star _=>_)
    stripLemma s [] = _ , [] , s
    stripLemma s (t ,- ts) with pard s t
    ... | _ , t' , s' with stripLemma s' ts
    ... | _ , ts' , s'' = _ , t' ,- ts' , s''

    pardStar : forall {M ga d} -> Parallelogram {M}{ga}{d} (Star _=>_) (Star _=>_)
    pardStar [] ts = _ , ts , []
    pardStar (s ,- ss) ts with stripLemma s ts
    ... | _ , ts' , s' with pardStar ss ts'
    ... | _ , ts'' , ss' = _ , ts'' , s' ,- ss'

    confluence : forall {M ga d} -> Parallelogram {M}{ga}{d} (Star _~>_) (Star _~>_)
    confluence ss ts with pardStar (star _ redPar ss) (star _ redPar ts)
    ... | _ , ts' , ss' = _ , bind* _ parReds ts' , bind* _ parReds ss'

  parThick : forall {M de ga d}(t0 : Term M de lib d)(th : de <= ga)
    {t1 : Term M ga lib d} -> (t0 ^ th) => t1 ->
    Sg _ \ t1' -> t0 => t1' * t1 == (t1' ^ th)
  parzThick : forall {M de ga n}(ez0 : All (\ _ -> Term M de lib syn) n)
    (th : de <= ga)
    {ez1 : All (\ _ -> Term M ga lib syn) n} ->
    Act.actz THIN ez0 (refl , th) =z> ez1 ->
    Sg _ \ ez1' -> ez0 =z> ez1' * ez1 == Act.actz THIN ez1' (refl , th)
  parPThick : forall {M ga ga' de}(p : Pat de)(pi0 : Env M (ga ,P p))
    (th : ga <= ga')
    {pi1' : Env M (ga' ,P p)} ->
    ActWeak.acte THINWEAK pi0 th =P> pi1' ->
    Sg _ \ pi1 -> pi0 =P> pi1 * pi1' == ActWeak.acte THINWEAK pi1 th
  parThick (! a) th (atom .a) = _ , atom a , refl
  parThick (s0 & t0) th (cons s t) with parThick s0 th s | parThick t0 th t
  ... | s1 , s' , refl | t1 , t' , refl = _ , cons s' t' , refl
  parThick (\\ t0) th (abst t) with parThick t0 (th su) t
  ... | t1 , t' , refl = _ , abst t' , refl
  parThick (# i) th (vari .(i -< th)) = _ , vari _ , refl
  parThick (essl n0 $ s0) th (elim n s)
    with parThick (essl n0) th n | parThick s0 th s
  ... | n1 , n' , refl | s1 , s' , refl = _ , elim n' s' , refl
  parThick ((t0 :: T0) $ s0) th t = help _ _ _ refl refl refl t where
    help : forall t0' T0' s0' {t1} ->
           t0' == (t0 ^ th) -> T0' == (T0 ^ th) -> s0' == (s0 ^ th) ->
           ((t0' :: T0') $ s0') => t1 ->
           Sg _ \ t1' ->
           (((t0 :: T0) $ s0) => t1') * t1 == (t1' ^ th)
    help ._ ._ ._ qt qT qs (beta {R} x {ts0} {Ts = Ts0} {ss = ss0} ts Ts ss)
      with thickEnv (betaIntro R) t0 th ts0 qt
         | thickEnv (betaType R) T0 th Ts0 qT
         | thickEnv (betaElim R) s0 th ss0 qs
    ... | ts1 , refl , refl | Ts1 , refl , refl | ss1 , refl , refl
      with parPThick (betaIntro R) ts1 th ts
         | parPThick (betaType R) Ts1 th Ts
         | parPThick (betaElim R) ss1 th ss
    ... | ts2 , ts' , refl | Ts2 , Ts' , refl | ss2 , ss' , refl
      = _ , beta x ts' Ts' ss' , sym (instThinLemma (redTerm R :: redType R) [] (cons (cons ts2 Ts2) ss2) th)
    help ._ ._ ._ refl refl refl (elim (radi t T) s)
      with parThick t0 th t | parThick T0 th T | parThick s0 th s
    ... | t1 , t' , refl | T1 , T' , refl | s1 , s' , refl
        = _ , elim (radi t' T') s' , refl
  parThick (essl (mets x)) th (mets .x) = _ , mets x , refl
  parThick (thnk n0) th (thnk n) with parThick (essl n0) th n
  ... | n1 , n' , refl = _ , thnk n' , sym (Act.actThunk THIN n1 (refl , th))
  parThick (t0 :: T0) th (radi t T) with parThick t0 th t | parThick T0 th T
  ... | t1 , t' , refl | T1 , T' , refl = _ , radi t' T' , refl
  parThick (x ?- ez0) th (.x ?- ez) with parzThick ez0 th ez
  ... | ez1 , ez' , refl = _ , x ?- ez' , refl
  parzThick [] th [] = [] , [] , refl
  parzThick (ez0 -, e0) th (ez -, e) with parzThick ez0 th ez | parThick e0 th e
  ... | ez1 , ez' , refl | e1 , e' , refl = _ , ez' -, e' , refl
  parPThick (atom a) (atom .a) th (atom .a) = atom a , atom a , refl
  parPThick (p - q) (cons pi0 chi0) th (cons pi chi) with parPThick p pi0 th pi | parPThick q chi0 th chi
  ... | pi1 , pi' , refl | chi1 , chi' , refl = cons pi1 chi1 , cons pi' chi' , refl
  parPThick (\\\ q) (abst chi0) th (abst chi) with parPThick q chi0 th chi
  ... | chi1 , chi' , refl = abst chi1 , abst chi' , refl
  parPThick (hole {de} ph) (hole t0) th (hole t) with parThick t0 (th ^+ oi {S = de}) t
  ... | t1 , t' , refl = _ , hole t' , refl

  parStan : forall {M ga de}(p : Pat de)(pi : Env M (ga ,P p)) r -> (p %P pi) => r ->
    Sg _ \ chi -> r == (p %P chi) * pi =P> chi
  parStan (atom a) (atom .a) .(! a) (atom .a) = atom a , refl , atom a
  parStan (p - q) (cons pip piq) .(_ & _) (cons px qx)
    with parStan p pip _ px | parStan q piq _ qx
  ... | chip , refl , pipg | chiq , refl , piqg
      = cons chip chiq , refl , cons pipg piqg
  parStan (\\\ q) (abst pi) .(\\ _) (abst x)
    with parStan q pi _ x
  ... | chi , refl , pig = abst chi , refl , abst pig
  parStan (hole th) (hole t) r x with parThick t (oi ^+ th) x
  ... | t' , y , refl = hole t' , refl , hole y

  parProj : forall {M ga de}(i : <> <- ga)
    {sg sg' : [ M ! ga ]/ de} -> sg =z> sg' ->
    project i sg => project i sg'
  parProj (i no) (sg -, _) = parProj i sg
  parProj (i su) (_ -, x) = x

  parCat : forall {M ga n m}
    {ez ez' : All (\ _ -> Term M ga lib syn) n} -> ez =z> ez' ->
    {fz fz' : All (\ _ -> Term M ga lib syn) m} -> fz =z> fz' ->
    (ez :+ fz) =z> (ez' :+ fz')
  parCat ez [] = ez
  parCat ez (fz -, f) = parCat ez fz -, f

  parVarz : forall {M ga de}(th : ga <= de) -> all (_^ th) (idsb {M = M}) =z> all (_^ th) idsb
  parVarz {M} {[]} {de} th = []
  parVarz {M} {ga -, <>} {de} th
    rewrite sym (allCo (_^ (oi no)) (_^ th) (_^ ((oi no) -< th))
                  (\ t -> sym (thinco t _ _)) (idsb {ga}{M}))
          = parVarz _ -, vari _



  parThin : forall {M ga de d}{t t' : Term M ga lib d} -> t => t' ->
    (th : ga <= de) -> (t ^ th) => (t' ^ th)
  parzThin : forall {M ga de n}{ez ez' : [ M ! n ]/ ga} -> ez =z> ez' ->
    (th : ga <= de) -> all (_^ th) ez =z> all (_^ th) ez'
  parpThin : forall {M ga ga' de}(p : Pat de)
    {ts0 ts1 : Env M (ga ,P p)} -> ts0 =P> ts1 ->
    (th : ga <= ga') ->
    ActWeak.acte THINWEAK ts0 th =P> ActWeak.acte THINWEAK ts1 th
    
  parThin (atom a) th = atom a
  parThin (cons s t) th = cons (parThin s th) (parThin t th)
  parThin (abst t) th = abst (parThin t (th su))
  parThin (thnk {e = e} n) th
    rewrite Act.actThunk THIN e (refl , th)
          = parThnk (parThin n th)
  parThin (vari i) th = vari _
  parThin (mets x) th = mets x
  parThin (elim e s) th = elim (parThin e th) (parThin s th)
  parThin (radi t T) th = radi (parThin t th) (parThin T th)
  parThin (_?-_ x {ez0} {ez1} ez) th
    rewrite Act.actzAll THIN ez0 (refl , th)
          | Act.actzAll THIN ez1 (refl , th)
          = x ?- parzThin ez th
  parThin (beta {R} x {ts0} {ts1} {Ts0} {Ts1} {ss0} {ss1} ts Ts ss) th
    rewrite plugThinLemma (betaIntro R) ts0 th
          | plugThinLemma (betaType R) Ts0 th
          | plugThinLemma (betaElim R) ss0 th
          | instThinLemma (redTerm R) [] (cons (cons ts1 Ts1) ss1) th
          | instThinLemma (redType R) [] (cons (cons ts1 Ts1) ss1) th
          = beta x (parpThin (betaIntro R) ts th)
                   (parpThin (betaType R) Ts th)
                   (parpThin (betaElim R) ss th)
  parzThin [] th = []
  parzThin (ez -, e) th = parzThin ez th -, parThin e th
  parpThin (atom a) (atom .a) th = atom a
  parpThin (p - q) (cons ss ts) th = cons (parpThin p ss th) (parpThin q ts th)
  parpThin (\\\ q) (abst ts) th = abst (parpThin q ts th)
  parpThin (hole {de} ph) (hole t) th = hole (parThin t (th ^+ oi {S = de}))

  parSbst : forall {M ga de d}{t t' : Term M ga lib d} -> t => t' ->
    {sg sg' : [ M ! ga ]/ de} -> sg =z> sg' ->
    (t / sg) => (t' / sg')
  parnSbst : forall {M ga de}{n : Term M ga ess syn}{e} -> essl n => e ->
    {sg sg' : [ M ! ga ]/ de} -> sg =z> sg' ->
    (essl n / sg) => (e / sg')
  parzSbst : forall {M ga de n}{ez ez' : [ M ! n ]/ ga} -> ez =z> ez' ->
    {sg sg' : [ M ! ga ]/ de} -> sg =z> sg' ->
    Act.actz SBST ez (refl , sg) =z> Act.actz SBST ez' (refl , sg')
  parpSbst : forall {M ga de de'}(p : Pat de')
    {ts0 ts1 : Env M (ga ,P p)} -> ts0 =P> ts1 ->
    {sg0 sg1 : [ M ! ga ]/ de} -> sg0 =z> sg1 ->
    ActWeak.acte SBSTWEAK ts0 sg0 =P> ActWeak.acte SBSTWEAK ts1 sg1
  parSbst (atom a) sg = atom a
  parSbst (cons s t) sg = cons (parSbst s sg) (parSbst t sg)
  parSbst (abst t) sg = abst (parSbst t (parzThin sg _ -, vari _))
  parSbst (thnk {e = e} n) {sg' = sg'} sg rewrite Act.actThunk SBST e (refl , sg')
    = parThnk (parnSbst n sg)
  parSbst {d = syn} {t = essl n} e sg = parnSbst e sg
  parSbst (radi t T) sg = radi (parSbst t sg) (parSbst T sg)
  parSbst (x ?- ez) sg = x ?- parzSbst ez sg
  parnSbst (vari i) sg = parProj i sg
  parnSbst (mets x) sg = mets x
  parnSbst (elim e s) sg = elim (parSbst e sg) (parSbst s sg)
  parnSbst (beta {R} x {ts0} {ts1} {Ts0} {Ts1} {ss0} {ss1} ts Ts ss) {sg0} {sg1} sg
    rewrite plugSbstLemma0 (betaIntro R) ts0 sg0
          | plugSbstLemma0 (betaType R) Ts0 sg0
          | plugSbstLemma0 (betaElim R) ss0 sg0
          | instSbstLemma0 (redTerm R) [] (cons (cons ts1 Ts1) ss1) sg1
          | instSbstLemma0 (redType R) [] (cons (cons ts1 Ts1) ss1) sg1
    = beta x (parpSbst (betaIntro R) ts sg)
             (parpSbst (betaType R) Ts sg)
             (parpSbst (betaElim R) ss sg)
  parzSbst [] sg = []
  parzSbst (ez -, e) sg = parzSbst ez sg -, parSbst e sg
  parpSbst (atom a) (atom .a) sg = atom a
  parpSbst (p - q) (cons ss ts) sg = cons (parpSbst p ss sg) (parpSbst q ts sg) 
  parpSbst (\\\ q) (abst ts) sg = abst (parpSbst q ts sg)
  parpSbst (hole {de} th) (hole t) sg
    = hole (parSbst t (parCat (parzThin sg _) (parVarz {ga = de} _)))

  parProje : forall {M ga de de'}{p : Pat de'}(x : de <P- p){pi pi' : Env M (ga ,P p)} ->
    pi =P> pi' -> proje ga x pi => proje ga x pi'
  parProje hole (hole x) = x
  parProje (car x) (cons pi _) = parProje x pi
  parProje (cdr x) (cons _ pi) = parProje x pi
  parProje (abst x) (abst pi) = parProje x pi

  parStab : forall {M ga de d}
            {p : Pat []}(t : Term ([] , p) de lib d){pi pi' : Env M (ga ,P p)} ->
            pi =P> pi' -> (t % ([] , pi)) => (t % ([] , pi'))
  parnStab : forall {M ga de}
             {p : Pat []}(n : Term ([] , p) de ess syn){pi pi' : Env M (ga ,P p)} ->
             pi =P> pi' -> (essl n % ([] , pi)) => (essl n % ([] , pi'))
  parzStab : forall {M ga de n}
             {p : Pat []}(ez : All (\ _ -> Term ([] , p) de lib syn) n){pi pi' : Env M (ga ,P p)} ->
             pi =P> pi' -> Act.actz INST ez (_ , refl , [] , pi) =z> Act.actz INST ez (_ , refl , [] , pi')
  parStab (! a) pi = atom a
  parStab (s & t) pi = cons (parStab s pi) (parStab t pi)
  parStab (\\ t) pi = abst (parStab t pi)
  parStab {d = syn} (essl n) pi = parnStab n pi
  parStab (thnk n) pi = parThnk (parnStab n pi)
  parStab (t :: T) pi = radi (parStab t pi) (parStab T pi)
  parStab (x ?- ez) pi = parSbst (parProje x pi) (parCat (parVarz _) (parzStab ez pi))
  parnStab (vari i) pi = vari _
  parnStab (elim e s) pi = elim (parStab e pi) (parStab s pi)
  parnStab (mets ()) pi
  parzStab [] pi = []
  parzStab (ez -, e) pi = parzStab ez pi -, parStab e pi

  noAmbiguity : forall {X}(R : X -> X -> Set)(rs : forall x y -> R x y -> R y x)
                (xz : Bwd X)(xzA : Pairwise (\ x y -> R x y -> Zero) xz)
                {x y : X}(r : R x y)(i : x <- xz)(j : y <- xz) ->
                Sg (x == y) \ { refl -> i == j }
  noAmbiguity R rs .(_ -, _) xzA r (i no) (j no) with noAmbiguity R rs _ (xzA ` _no) r i j
  ... | refl , refl = refl , refl
  noAmbiguity R rs .(_ -, _) xzA r (i no) (j su) = naughty (xzA (i su) r)
  noAmbiguity R rs .(_ -, _) xzA r (i su) (j no) = naughty (xzA (j su) (rs _ _ r))
  noAmbiguity R rs .(_ -, _) xzA r (i su) (j su) = refl , _su $= oeU i j

  betaInv : forall {b}(x : b <- computation){M ga}
            {t T s : Term M ga lib chk} ->
            (pit : Env M (ga ,P betaIntro b))(piT : Env M (ga ,P betaType b))(pis : Env M (ga ,P betaElim b)) ->
            (betaIntro b %P pit) == t -> (betaType b %P piT) == T -> (betaElim b %P pis) == s ->
            {P : Term M ga lib syn -> Set} ->
            ((pit' : Env M (ga ,P betaIntro b))(piT' : Env M (ga ,P betaType b))(pis' : Env M (ga ,P betaElim b)) ->
             pit =P> pit' -> piT =P> piT' -> pis =P> pis' -> P (((betaIntro b %P pit') :: (betaType b %P piT')) $ (betaElim b %P pis'))) ->
            ((pit' : Env M (ga ,P betaIntro b))(piT' : Env M (ga ,P betaType b))(pis' : Env M (ga ,P betaElim b)) ->
             pit =P> pit' -> piT =P> piT' -> pis =P> pis' -> P ((redTerm b :: redType b) % ([] , cons (cons pit' piT') pis'))) ->            
            (r : Term M ga lib syn) -> ((t :: T) $ s) => r -> P r
  betaInv {b} x pit piT pis qt qT qs pno pgo .(_ :: _) (beta {b'} y {ts} {Ts = Ts} {ss = ss} pitr piTr pisr)
    with noAmbiguity _ (\ x y r -> sym~~ _ _ r)
           computation computationUnambiguous
           (matchU ((betaIntro b - betaType b) - betaElim b) (cons (cons pit piT) pis)
                   ((betaIntro b' - betaType b') - betaElim b') (cons (cons ts Ts) ss)
                   (_&_ $= (_&_ $= qt =$= qT) =$= qs))
           x y
  ... | refl , refl
    with matchUnique (betaIntro b') pit ts qt | matchUnique (betaType b') piT Ts qT | matchUnique (betaElim b') pis ss qs
  ... | refl | refl | refl = pgo _ _ _ pitr piTr pisr
  betaInv {b} x pit piT pis refl refl refl pno pgo .((_ :: _) $ _) (elim (radi tr Tr) sr)
    with parStan (betaIntro b) pit _ tr | parStan (betaType b) piT _ Tr | parStan (betaElim b) pis _ sr
  ... | chit , refl , pitg | chiT , refl , piTg | chis , refl , pisg = pno _ _ _ pitg piTg pisg

  dev : forall {M ga ga' d}{t : Term M ga lib d}{t' : Term M ga' lib d}{th : ga <= ga'} ->
    t <[ th ]= t' ->
    Sg _ \ dt -> t => dt *
    (forall rt -> t => rt -> rt => dt)
  devn : forall {M ga ga'}{n : Term M ga ess syn}{n' : Term M ga' ess syn}{th : ga <= ga'} ->
    n <[ th ]= n' ->
    Sg _ \ de -> essl n => de *
    (forall re -> essl n => re -> re => de)
  devz : forall {M ga ga' n}{ez : All (\ _ -> Term M ga lib syn) n}{ez' : All _ n}{th : ga <= ga'} ->
    ez <[ th ]z= ez' ->
    Sg _ \ dez -> ez =z> dez *
    (forall rez -> ez =z> rez -> rez =z> dez)
  go : forall {M ga ga'}{t T s : Term M ga lib chk}{t' T' s' : Term M ga' lib chk}{th : ga <= ga'} ->
    t <[ th ]= t' -> T <[ th ]= T' -> s <[ th ]= s' ->
    (bz : Bwd BetaRule) -> bz <= computation ->
    (forall {b}(x : b <- computation) ->
      Match (ga ,P cons (cons (betaIntro b) (betaType b)) (betaElim b)) ((t & T) & s) -> b <- bz) ->
    Sg _ \ d -> ((t :: T) $ s) => d * (forall r -> ((t :: T) $ s) => r -> r => d)
  devo : forall {M ga ga' de}{t : Term M (ga -+ de) lib chk}{t' : Term M (ga' -+ de) lib chk}{th : (ga -+ de) <= (ga' -+ de)} ->
    t <[ th ]= t' -> (p : Pat de) -> Match (ga ,P p) t ->
    Sg (Env M (ga ,P p)) \ pit -> t == p %P pit *
    Sg _ \ pid -> pit =P> pid *
    (forall pir -> pit =P> pir -> pir =P> pid)
  dev (thnk n) with devn n
  ... | dn , rn , un = [ dn ] , thnk rn , \ { _ (thnk xn) -> parThnk (un _ xn) }
  dev {d = syn} (essl n) = devn n
  dev (essl (atom a)) = ! a , atom a , \ { _ (atom a) -> atom a }
  dev (essl (cons s t)) with dev s | dev t
  ... | ds , rs , us | dt , rt , ut = ds & dt , cons rs rt , \ { _ (cons xs xt) -> cons (us _ xs) (ut _ xt) }
  dev (essl (abst t)) with dev t
  ... | dt , rt , ut = \\ dt , abst rt , \ { _ (abst xt) -> abst (ut _ xt) }
  dev (t :: T) with dev t | dev T
  ... | dt , rt , ut | dT , rT , uT = dt :: dT , radi rt rT , \ { _ (radi xt xT) -> radi (ut _ xt) (uT _ xT) }
  dev (x ?- ez) with devz ez
  ... | dez , rez , uez = x ?- dez , x ?- rez , \ { _ (_ ?- xez) -> _ ?- uez _ xez }
  devn (vari i) = # _ , vari _ , \ { _ (vari _) -> vari _ }
  devn (elim (essl n) s) with devn n | dev s
  ... | dn , rn , un | ds , rs , us = essl (elim dn ds) , elim rn rs , \ { _ (elim xn xs) -> elim (un _ xn) (us _ xs) }
  devn (elim (t :: T) s) = go t T s computation oi \ x _ -> x
  devn (mets x) = _ , mets x , \ { _ (mets _) -> mets _ }
  devz [] = [] , [] , \ { _ [] -> [] }
  devz (ez -, e) with devz ez | dev e
  ... | dez , rez , uez | de , re , ue = dez -, de , rez -, re , \ { _ (xez -, xe) -> uez _ xez -, ue _ xe }
  go t T s [] be bc with dev t | dev T | dev s
  ... | dt , rt , ut | dT , rT , uT | ds , rs , us = (dt :: dT) $ ds , elim (radi rt rT) rs , 
    \ { _ (elim (radi xt xT) xs) -> elim (radi (ut _ xt) (uT _ xT)) (us _ xs)
      ; _ (beta {R} x {ts = ts}{Ts = Ts}{ss = ss} _ _ _) ->
        naughty (busted (bc x (match (cons (cons (betaIntro R) (betaType R)) (betaElim R)) (cons (cons ts Ts) ss)))) }
  go {ga = ga} {t = t0} {T0} {s0} t T s (bz -, b) be bc
    with pam (ga ,P cons (cons (betaIntro b) (betaType b)) (betaElim b)) ((t0 & T0) & s0)
  go {ga = ga} {t = t0} {T0} {s0} t T s (bz -, b) be bc | #0 , n =
    go t T s bz ((oi no) -< be) (help computation bc) where
      help : forall cz ->
        (forall {b'}(x : b' <- cz) ->
          Match (ga ,P cons (cons (betaIntro b') (betaType b')) (betaElim b')) ((t0 & T0) & s0) -> b' <- (bz -, b)) ->
        forall {b'}(x : b' <- cz) ->
          Match (ga ,P cons (cons (betaIntro b') (betaType b')) (betaElim b')) ((t0 & T0) & s0) -> b' <- bz
      help ._ cc x m with cc x m
      help ._ cc x m | w no = w
      help ._ cc x m | w su = naughty (n m)
  go {ga = ga} {t = t0} {T0} {s0} t T s (bz -, b) be bc | #1 , cons (cons tm Tm) sm
    with devo t (betaIntro b) tm | devo T (betaType b) Tm | devo s (betaElim b) sm
  ... | pitt , refl , pidt , pitdt , pitu
      | pitT , refl , pidT , pitdT , piTu
      | pits , refl , pids , pitds , pisu
      = ((redTerm b :: redType b) % ([] , cons (cons pidt pidT) pids))
      , (beta ((oe su) -< be) pitdt pitdT pitds)
      , betaInv ((oe su) -< be) pitt pitT pits refl refl refl
        (\ pit' piT' pis' rt rT rs -> beta (((oe su) -< be)) (pitu _ rt) (piTu _ rT) (pisu _ rs))
        \ pit' piT' pis' rt rT rs -> parStab (redTerm b :: redType b) (cons (cons (pitu _ rt) (piTu _ rT)) (pisu _ rs))
  devo t (hole th) (hole x) with dev (x +t t)
  devo t (hole th) (hole {t = t0} x) | d , td , du = hole t0 , nihtR x , hole d , hole td , \ { _ (hole y) -> hole (du  _ y) }
  devo (essl (atom .a)) (atom a) (atom .a) = atom a , refl , atom a , atom a , \ { _ (atom a) -> atom a }
  devo (essl (cons s t)) (p - q) (cons ps qt) with devo s p ps | devo t q qt
  ... | spi , refl , schi , sr , us | tpi , refl , tchi , tr , ut
    = cons spi tpi , refl , cons schi tchi , cons sr tr
    , \ { _ (cons ys yt) -> cons (us _ ys) (ut _ yt) }
  devo (essl (abst t)) (\\\ q) (abst qt) with devo t q qt
  ... | tpi , refl , tchi , tr , ut
      = abst tpi , refl , abst tchi , abst tr
      , \ { _ (abst yt) -> abst (ut _ yt) }

  development : forall {M ga d}(t : Term M ga lib d) ->
    Sg _ \ dt -> t => dt * (forall rt -> t => rt -> rt => dt)
  development t = dev (thinR t oi)

  open CONFLUENCE (\ {M}{ga}{d}{t} t0 t1 -> let t' , _ , u = development t in _ , u _ t0 , u _ t1) public
