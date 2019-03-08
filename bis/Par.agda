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

module PARALLEL (TH : TypeTheory) where

  open TYPETHEORY TH
  open STABTHIN TH
  open TypeTheory TH
  open BetaRule

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

  pam : forall {M ga de}(p : Pat de)(t : Term M (ga -+ de) lib chk) ->
    Dec (Sg (Env M (ga ,P p)) \ ts -> (p %P ts) == t)
  pam (atom a) (! a') with atomEq? a a'
  pam (atom a) (! a') | #0 , r = #0 , \ { (atom a , refl) -> r refl }
  pam (atom a) (! .a) | #1 , refl = #1 , atom a , refl
  pam (p - q) (s & t) with pam p s | pam q t
  pam (p - q) (s & t) | #0 , rp | bq , rq
    = #0 , \ { (cons ss ts , refl) -> rp (ss , refl) }
  pam (p - q) (s & t) | #1 , ss , sq | #0 , rq
    = #0 , \ { (cons ss ts , refl) -> rq (ts , refl) }
  pam (p - q) (.(p %P ss) & .(q %P ts)) | #1 , ss , refl | #1 , ts , refl
    = #1 , (cons ss ts) , refl
  pam (\\\ q) (\\ t) with pam q t
  pam (\\\ q) (\\ t) | #0 , r = #0 , \ { (abst ts , refl) -> r (ts , refl) }
  pam (\\\ q) (\\ .(q %P ts)) | #1 , ts , refl = #1 , abst ts , refl
  pam (atom a) (_ & _) = #0 , \ { (atom a , ()) }
  pam (atom a) (\\ _) = #0 , \ { (atom a , ()) }
  pam (atom a) (thnk _) = #0 , \ { (atom a , ()) }
  pam (atom a) (x ?- _) = #0 , \ { (atom a , ()) }
  pam (p - q) (! _) = #0 , \ { (cons _ _ , ()) }
  pam (p - q) (\\ _) = #0 , \ { (cons _ _ , ()) }
  pam (p - q) (thnk _) = #0 , \ { (cons _ _ , ()) }
  pam (p - q) (_ ?- _) = #0 , \ { (cons _ _ , ()) }
  pam (\\\ q) (! _) = #0 , \ { (abst _ , ()) }
  pam (\\\ q) (_ & _) = #0 , \ { (abst _ , ()) }
  pam (\\\ q) (thnk _) = #0 , \ { (abst _ , ()) }
  pam (\\\ q) (_ ?- _) = #0 , \ { (abst _ , ()) }
  pam (hole th) t with support t
  pam (hole th) .(t' ^ ph) | _ , ph , t' , refl , u with thick? (oi ^+ th) ph
  pam (hole th) .(t' ^ ph) | _ , ph , t' , refl , u | #0 , r
    = #0 , \ { (hole t , a) -> 
      let th' , tr = u _ (oi ^+ th) t (sym a) in
      r (th' , triDet tr (mkTri th' (oi ^+ th))) }
  pam (hole th) .(t' ^ (ph' -< (oi ^+ th)))
    | _ , ._ , t' , refl , u | #1 , ph' , refl
    = #1 , hole (t' ^ ph') , thinco t' ph' (oi ^+ th)

  dev : forall {M ga l d}(t : Term M ga l d) -> Term M ga lib d
  devz : forall {M ga de}(ez : All (\ _ -> Term M ga lib syn) de) ->
    All (\ _ -> Term M ga lib syn) de
  devBeta : forall {M ga}(bz : Bwd BetaRule)
    (t T s : Term M ga lib chk) -> Term M ga lib syn
  pamDev : forall {M ga de}(p : Pat de)(t : Term M (ga -+ de) lib chk) ->
    One + Env M (ga ,P p)
  dev (atom a) = ! a
  dev (cons s t) = dev s & dev t
  dev (abst t) = \\ dev t
  dev (vari i) = # i
  dev (elim (essl e) s) = dev e $ dev s
  dev (elim (t :: T) s) = devBeta computation t T s
  dev (essl t) = dev t
  dev (thnk n) = [ dev n ]
  dev (t :: T) = dev t :: dev T
  dev (x ?- ez) = x ?- devz ez
  dev (mets x) = essl (mets x)
  devz [] = []
  devz (ez -, e) = devz ez -, dev e
  devBeta [] t T s = (dev t :: dev T) $ dev s
  devBeta (bz -,
    record { betaIntro = q
           ; betaType = Q
           ; betaElim = p
           ; redTerm = t'
           ; redType = T' })
    t T s with pamDev q t | pamDev Q T | pamDev p s
  ... | #1 , ts | #1 , Ts | #1 , ss = (t' % ([] , pi)) :: (T' % ([] , pi))
    where pi = cons (cons ts Ts) ss
  ... | b0 , r0 | b1 , r1 | b2 , r2 = devBeta bz t T s
  pamDev (atom a) (! a') with atomEq? a a'
  pamDev (atom a) (! a') | #0 , r = #0 , <>
  pamDev (atom a) (! .a) | #1 , refl = #1 , atom a
  pamDev (p - q) (s & t) with pamDev p s | pamDev q t
  ... | #1 , ss | #1 , ts = #1 , cons ss ts
  ... | _ | _ = #0 , <>
  pamDev (\\\ q) (\\ t)  with pamDev q t
  ... | #1 , ts = #1 , abst ts
  ... | _ = #0 , <>
  pamDev (hole th) t with support t
  ... | _ , th' , _ , _ , _ with thick? (oi ^+ th) th'
  ... | #0 , _ = #0 , <>
  ... | #1 , _ with support (dev t) -- yuk
  ... | _ , ph , t' , q , u with thick? (oi ^+ th) ph -- will say yes
  ... | #0 , _ = #0 , <>
  ... | #1 , ph' , _ = #1 , hole (t' ^ ph')
  pamDev _ t = #0 , <>
