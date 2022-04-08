module Tm where

open import Basics
open import Bwd
open import SmolCat
open import Thin

Sco = Bwd One
infixl 30 _+b_
_+b_ : Sco -> Two -> Sco
ga +b ff = ga
ga +b tt = ga -, <>

data Ki : Set where
  tm : Ki
  sb : Sco -> Ki

data LL : Ki -> Ki -> Set where
  tm : LL tm tm
  sb : forall {ga} -> LL (sb ga) (sb (ga -, <>))

module TERM (A : Set)(M : Sco -> Set) where
  open SmolCat.SmolCat (THIN One)

  infix 20 _-|_
  data _-|_ : Ki -> Sco -> Set where
    var     : tm -| [] -, <>
    `_      : A -> tm -| []
    _\\_    : forall {ga}(b : Two) -> tm -| ga +b b -> tm -| ga
    _#$_    : forall {de} -> M de -> [ sb de -|_ -:> tm -|_ ]
    []      : sb [] -| []
    _</_!_\>_ : forall {j k}{gal ga gar}{th : gal <= ga}{ph : gar <= ga}
           -> j -| gal -> LL j k -> th /u\ ph -> tm -| gar
           -> k -| ga

  infixr 20 _<^_^>_
  _<^_^>_ : forall {j k ga}
         -> j -|_ :^ ga -> LL j k -> tm -|_ :^ ga -> k -|_ :^ ga
  s ^ th <^ l ^> t ^ ph = let (_ , _ , ps , _) , _ , u , _ = cop (_ , th , ph) in
    (s </ l ! u \> t) ^ ps

  _</~\>_ : forall  {j k}{l : LL j k}{ga}
      {s0'@(s0 ^ th0) s1'@(s1 ^ th1) : j -|_ :^ ga}
      {t0'@(t0 ^ ph0) t1'@(t1 ^ ph1) : tm -|_ :^ ga}
      {u0 : th0 /u\ ph0}{u1 : th1 /u\ ph1} ->
      s0' ~ s1' -> t0' ~ t1' ->
      (s0 </ l ! u0 \> t0) ~ (s1 </ l ! u1 \> t1)
  r~ </~\> r~ = (!~ (_ </ _ !_\> _)) ~$~ copQ _ _

  _<^~^>_ : forall  {j k}{l : LL j k}{ga}
      {a@(ga0 , ps0) b@(ga1 , ps1) : < _<= ga >}
      {s0'@(s0 ^ th0) : j -|_ :^ ga0}{s1'@(s1 ^ th1) : j -|_ :^ ga1}
      {t0'@(t0 ^ ph0) : tm -|_ :^ ga0}{t1'@(t1 ^ ph1) : tm -|_ :^ ga1}
      {u0 : th0 /u\ ph0}{u1 : th1 /u\ ph1} ->
      (s0' ^& ps0) ~ (s1' ^& ps1) -> (t0' ^& ps0) ~ (t1' ^& ps1) ->
      ((s0 </ l ! u0 \> t0) ^ ps0) ~ ((s1 </ l ! u1 \> t1) ^ ps1)
  _<^~^>_ {a = ga0 , ps0} {ga1 , ps1} {s0 ^ th0} {s1 ^ th1} {t0 ^ ph0} {t1 ^ ph1} sq tq
    with comp th0 ps0 | comp ph0 ps0
  _<^~^>_ {ga = _} {ga0 , ps0} {ga1 , ps1} {s0 ^ th0} {.s0 ^ th1} {t0 ^ ph0} {.t0 ^ ph1}{u0}{u1} r~ r~
    | .(th1 & ps1) , v0 | .(ph1 & ps1) , w0
    with _ , v1 <- comp th1 ps1 | _ , w1 <- comp ph1 ps1
       | r~ <- CopQ (_ , v1 , u1 , w1) (_ , v0 , u0 , w0)
       = r~
      
  is : forall {ga} -> sb ga -| ga
  is {[]} = []
  is {ga -, <>} = is </ sb ! lll -^, <> \> var

module _ {A : Set}{M : Sco -> Set} where

  open SmolCat.SmolCat (THIN One)
  open TERM A M public

  _?$_ : forall {xi de ga}
      -> xi <= de -> sb de -| ga -> sb xi -|_ :^ ga
  (th -^ y) ?$ (sg </ sb ! u \> t) = (th ?$ sg) ^& luth u
  (th -, x) ?$ (sg </ sb ! u \> t) = ((th ?$ sg) ^& luth u) <^ sb ^> t ^ ruth u
  [] ?$ sg = [] ^ no

  io?$ : forall {de ga} (sg : sb de -| ga)
      -> (io ?$ sg) ~ (sg ^ io)
  io?$ [] = r~
  io?$ (sg </ sb ! u \> t)
    rewrite io?$ sg | triQ (absl (luth u))
      | CopQ (cop (_ , luth u , ruth u)) (_ , absr _  , u , absr _)
      = r~

  no?$ : forall {de ga}(sg : sb de -| ga)
      -> (no ?$ sg) ~ ([] ^ no)
  no?$ [] = r~
  no?$ (sg </ sb ! u \> t) rewrite no?$ sg | triQ (no& (luth u)) = r~

  _?$is : forall {de ga}(th : de <= ga) -> (th ?$ is) ~ (is ^ th)
  (th -^ y) ?$is rewrite th ?$is | triQ (absr th) = r~
  (th -, x) ?$is rewrite th ?$is | triQ (absr th) | copL th = r~
  [] ?$is = r~

  relLemma : forall {xi0 xi1 de ga}
      -> {th0 : xi0 <= de}{th1 : xi1 <= de}
      -> th0 /u\ th1
      -> (sg : sb de -| ga)
      -> thinning (th0 ?$ sg) /u\ thinning (th1 ?$ sg)
  relLemma (u -^, <>) (sg </ sb ! w \> t) =
    let _ ^ psl = luth u ?$ sg ; _ ^ psr = ruth u ?$ sg in
    let _ , vl = comp psl (luth w) ; _ , vr = comp psr (luth w) in
    copRot (_ , vl , relLemma u sg , vr) w
  relLemma (u -,^ .<>) (sg </ sb ! w \> t) = 
    let _ ^ psl = luth u ?$ sg ; _ ^ psr = ruth u ?$ sg in
    let _ , vl = comp psl (luth w) ; _ , vr = comp psr (luth w) in
    copSwap (copRot (_ , vr , copSwap (relLemma u sg) , vl) w)
  relLemma (u -, <>) (sg </ sb ! w \> t) =
    let _ ^ psl = luth u ?$ sg ; _ ^ psr = ruth u ?$ sg in
    let chl , vl = comp psl (luth w) ; chr , vr = comp psr (luth w) in
    copDis (_ , vl , relLemma u sg , vr) w
  relLemma [] [] = []

  data [_$_]~_ : forall {k de ga} -> k -| de -> sb de -| ga -> k -| ga -> Set
    where
    var : forall {ga}{t : tm -| ga} -> [ var $ [] </ sb ! rrr \> t ]~ t
    `_  : forall a -> [ ` a $ [] ]~ ` a
    ff\\_ : forall {de ga}{t : tm -| de}{sg : sb de -| ga}{t' : tm -| ga}
         -> [ t $ sg ]~ t'
         -> [ ff \\ t $ sg ]~ (ff \\ t')
    tt\\_ : forall {de ga}{t : tm -| de -, <>}{sg : sb de -| ga}{t' : tm -| ga -, <>}
         -> [ t $ sg </ sb ! lll -^, <> \> var ]~ t'
         -> [ tt \\ t $ sg ]~ (tt \\ t')
    _#$_    : forall {xi de ga}(m : M xi)
              {rh : sb xi -| de}{sg : sb de -| ga}{rh' : sb xi -| ga}
           -> [ rh $ sg ]~ rh'
           -> [ m #$ rh $ sg ]~ (m #$ rh')
    []    : [ [] $ [] ]~ []
    _</_\>_ : forall {j k}{l : LL j k}{de ga}{sg : sb de -| ga}
             {(s ^ th) : j -|_ :^ de}{(t ^ ph) : tm -|_ :^ de}{u : th /u\ ph}
             {(s' ^ th') : j -|_ :^ ga}{(t' ^ ph') : tm -|_ :^ ga}
             {sgl sgr}
          -> ((th ?$ sg) ~ (sgl ^ th')) * [ s $ sgl ]~ s'
          -> (u' : th' /u\ ph')
          -> ((ph ?$ sg) ~ (sgr ^ ph')) * [ t $ sgr ]~ t'
          -> [ s </ l ! u \> t $ sg ]~ (s' </ l ! u' \> t')

  subU : forall {k de ga}{t : k -| de}{sg : sb de -| ga}(a b : < [ t $ sg ]~_ >) -> a ~ b
  subU (_ , var) (_ , var) = r~
  subU (_ , (` a)) (_ , (` .a)) = r~
  subU (_ , (ff\\ a)) (_ , (ff\\ b)) with r~ <- subU (_ , a) (_ , b) = r~
  subU (_ , (tt\\ a)) (_ , (tt\\ b)) with r~ <- subU (_ , a) (_ , b) = r~
  subU (_ , (m #$ a)) (_ , (.m #$ b)) with r~ <- subU (_ , a) (_ , b) = r~
  subU (_ , []) (_ , []) = r~
  subU {sg = sg} (_ , _</_\>_ {u = u} (aq , a) u' (bq , b)) (_ , ((cq , c) </ u'' \> (dq , d)))
    = {!!}

  _$is : forall {k de}(t : k -| de) -> [ t $ is ]~ t
  var $is = var
  (` a) $is = ` a
  (ff \\ t) $is = ff\\ (t $is)
  (tt \\ t) $is = tt\\ (t $is)
  (m #$ rh) $is = m #$ (rh $is)
  [] $is = []
  (s </ l ! u \> t) $is = 
    ((luth u ?$is) , (s $is)) </ u \> ((ruth u ?$is) , (t $is))

  is$ : forall {ga de}(sg : sb ga -| de) -> [ is $ sg ]~ sg
  is$ [] = []
  is$ (sg </ sb ! u \> t) =
    ((
      ((io ?$ sg) ^& luth u) ~[ (!~ (_^& luth u)) ~$~ io?$ sg >
      sg ^ (io & luth u) ~[ (!~ (sg ^_)) ~$~ triQ (absl _) >
      sg ^ luth u [QED]
    ) , is$ sg)
    </ u \>
    (help
    , var)
    where
    help : (((no ?$ sg) ^& luth u) <^ sb ^> t ^ ruth u) ~
            ([] </ sb ! rrr \> t) ^ ruth u
    help rewrite no?$ sg | triQ (no& (luth u)) | copR (ruth u) = r~

  tm-co : forall {k de ga xi}
    {t0 : k -| de}{sg : sb de -| ga}{t1 : k -| ga}{ta : sb ga -| xi}{t2 : k -| xi}
    {up : sb de -| xi}
    -> [ t0 $ sg ]~ t1 -> [ t1 $ ta ]~ t2
    -> [ sg $ ta ]~ up -> [ t0 $ up ]~ t2
  tm-co {ta = ta} var t12 ((r~ , sg) </ u' \> (r~ , t))
    with no ?$ ta | no?$ ta | io ?$ ta | io?$ ta
  tm-co {ta = ta} var t12 ((r~ , []) </ u' \> (r~ , t)) | _ | r~ | _ | r~
    with r~ <- subU (_ , t12) (_ , t)
    rewrite copQ u' rrr = var
  tm-co (` a) (` .a) [] = ` a
  tm-co (ff\\ t01) (ff\\ t12) stu = ff\\ tm-co t01 t12 stu
  tm-co {xi = xi}{ta = ta} (tt\\ t01) (tt\\ t12) stu = tt\\ tm-co t01 t12
    ((fulp , stu)
    </ (lll -^, <>) \>
    (gulp , var $is))
    where
    fulp : ((io ?$ ta) ^& (io -^ <>)) ~ ta ^ io -^ <>
    fulp rewrite io?$ ta | triQ (absl (io{_}{xi})) = r~
    gulp : (((no ?$ ta) ^& (io -^ <>)) <^ sb ^> var ^ (no -, <>))
         ~ is ^ (no -, <>)
    gulp rewrite no?$ ta | triQ (no& (io {_}{xi}))
          | CopQ (cop (xi , no , no)) (([] , [] , no , []) , no& _ , [] , no& _)
          = r~
  tm-co (m #$ t01) (.m #$ t12) stu = m #$ tm-co t01 t12 stu
  tm-co [] [] [] = []
  tm-co (x </ u' \> x₁) t12 stu = {!!}

  sub : forall {k de ga}(t : k -| de)(sg : sb de -| ga) -> < [ t $ sg ]~_ >
  fst (sub var ([] </ sb ! u \> t)) with r~ <- isRRR u = t
  snd (sub var ([] </ sb ! u \> t))
    with r~ <- isRRR u
       | r~ <- noU (luth u) no
       | r~ <- ioU (ruth u) io
       | r~ <- copQ u rrr
       = var
  sub (` a) [] = _ , ` a
  sub (ff \\ t) sg = let _ , t' = sub _ _ in _ , ff\\ t'
  sub (tt \\ t) sg = let _ , t' = sub _ _ in _ , tt\\ t'
  sub (m #$ rh) sg = let _ , rh' = sub _ _ in _ , m #$ rh'
  sub [] [] = _ , []
  sub (s </ l ! u \> t) sg =
    let sgl ^ _ = luth u ?$ sg ; sgr ^ _ = ruth u ?$ sg in
    let _ , s' = sub s sgl ; _ , t' = sub t sgr in
    _ , ((r~ , s') </ relLemma u sg \> (r~ , t'))

  _$_ : forall {k de ga} -> k -| de -> sb de -| ga -> k -| ga
  t $ sg = fst (sub t sg)


{-
module _ where
module _ {A : Set}{M : Bwd One -> Set} where
  open SmolCat.SmolCat (THIN One)

  wklem : forall {ga de al}(sg : Sb A M ga de)(ta : Sb A M de al)
      -> ((sg -$ ta) -/ lll -^, <> \, var)
       ~ ((sg -/ lll -^, <> \, var) -$ (ta -/ lll -^, <> \, var))
  wklem sg ta = {!!}

  tm-co : forall {ga de al}
    (t : Tm A M ga)(sg : Sb A M ga de)(ta : Sb A M de al)
    -> (t $ (sg -$ ta)) ~ ((t $ sg) $ ta)
  sb-co : forall {xi ga de al}
    (rh : Sb A M xi ga)(sg : Sb A M ga de)(ta : Sb A M de al)
    -> (rh -$ (sg -$ ta)) ~ ((rh -$ sg) -$ ta)
  tm-co var ([] -/ x \, t) ta with r~ <- isRRR x
    rewrite noU (luth x) no | ioU (ruth x) io -- | no?$ ta
    = help (no ?$ ta) (no?$ ta) (io ?$ ta) (io?$ ta) (relLemma x ta)
    where
    help : (nota : Sb A M [] :^ _) -> nota ~ [] ^ no ->
           (iota : Sb A M _ :^ _) -> iota ~ ta ^ io ->
           (y : thinning nota /u\ thinning iota) →
           (var $ (([] -$ thing nota) -/ y \, (t $ thing iota))) ~ (t $ ta)
    help _ r~ _ r~ y with r~ <- isRRR y = r~
  tm-co (` x) [] [] = r~
  tm-co (s </ u \> t) sg ta = {!!}
  tm-co (ff \\ t) sg ta rewrite tm-co t sg ta = r~
  tm-co (tt \\ t) sg ta = (!~ (tt \\_)) ~$~ (
    (t $ ((sg -$ ta) -/ lll -^, <> \, var)) ~[ (!~ (t $_)) ~$~ wklem sg ta >
    (t $ ((sg -/ lll -^, <> \, var) -$ (ta -/ lll -^, <> \, var))) ~[ tm-co t _ _ >
    ((t $ (sg -/ lll -^, <> \, var)) $ (ta -/ lll -^, <> \, var)) [QED])
  tm-co (m #$ rh) sg ta rewrite sb-co rh sg ta = r~
  sb-co [] [] [] = r~
  sb-co (rh -/ u \, t) sg ta = {!!}
-}
