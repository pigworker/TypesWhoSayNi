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

  is : forall {ga} -> sb ga -| ga
  is {[]} = []
  is {ga -, <>} = is </ sb ! lll -^, <> \> var

module _ {A : Set}{M : Sco -> Set} where

  open SmolCat.SmolCat (THIN One)
  open TERM A M public

  data [_?$_]~[_^_] : forall {xi de ga up}
    (th : xi <= de)(sg : sb de -| ga)(ta : sb xi -| up)(ph : up <= ga)
    -> Set where
    _-^_ : forall {xi de ga up gal gar}{chl : gal <= ga}{chr : gar <= ga}
      {u : chl /u\ chr}{t : tm -| gar}{om : up <= ga}
      {th : xi <= de}{sg : sb de -| gal}{ta : sb xi -| up}{ph : up <= gal}
      -> [ th ?$ sg ]~[ ta ^ ph ]
      -> [ ph & chl ]~ om
      -> [ (th -^ <>) ?$ (sg </ sb ! u \> t) ]~[ ta ^ om ]
    _-,_ : forall {xi de ga up gal gar}
      {chl : gal <= ga}{chr : gar <= ga}
      {u : chl /u\ chr}{t : tm -| gar}{om : up <= ga}
      {th : xi <= de}{sg : sb de -| gal}{ta : sb xi -| up}{ph : up <= gal}
      -> [ th ?$ sg ]~[ ta ^ ph ]
      -> ((_ , C) : [ ph & chl ]~ om * Cop (_ , om , chr))
      -> [ (th -, <>) ?$ (sg </ sb ! u \> t) ]~[ ta </ sb ! cover C \> t ^ slack C ]
    [] : [ [] ?$ [] ]~[ [] ^ [] ]

  selSbQ : forall {xi de ga}
    {th : xi <= de}{sg : sb de -| ga}
    (a b : (sb xi -|_ :^ ga) >< \ (ta ^ ph) -> [ th ?$ sg ]~[ ta ^ ph ])
    -> a ~ b
  selSbQ (_ , (a -^ v)) (_ , (b -^ w))
    with r~ <- selSbQ (_ , a) (_ , b)
       | r~ <- compQ (_ , v) (_ , w)
       = r~
  selSbQ (_ , (a -, (at , aC@(av /| au |\ aw))))
         (_ , (b -, (bt , bC@(bv /| bu |\ bw))))
    with r~ <- selSbQ (_ , a) (_ , b)
       | r~ <- compQ (_ , at) (_ , bt)
       | r~ <- CopQ aC bC
       = r~
  selSbQ (_ , []) (_ , []) = r~

  doctor : forall {xi de ga}(th : xi <= de)(sg : sb de -| ga) ->
    (sb xi -|_ :^ ga) >< \ (ta ^ ph) ->
    [ th ?$ sg ]~[ ta ^ ph ]
  doctor (th -^ y) (sg </ sb ! u \> t) = let _ , a = doctor th sg in
    _ , a -^ snd (comp _ _)
  doctor (th -, x) (sg </ sb ! u \> t) = let _ , a = doctor th sg in
    _ , a -, (snd (comp _ _) , cop _)
  doctor [] [] = _ , []

  _?$_ : forall {xi de ga}
      -> xi <= de -> sb de -| ga -> sb xi -|_ :^ ga
  th ?$ sg = fst (doctor th sg)

  ioDr : forall {de ga}(sg : sb de -| ga) -> [ io ?$ sg ]~[ sg ^ io ]
  ioDr [] = []
  ioDr (sg </ sb ! u \> t) = ioDr sg -, (absl _ , absr _ /| u |\ absr _)

  noDr : forall {de ga}(sg : sb de -| ga) -> [ no ?$ sg ]~[ [] ^ no ]
  noDr [] = []
  noDr (sg </ sb ! u \> t) = noDr sg -^ no& _

  coDr : forall {de0 de1 de ga0 ga1 ga}
           {th0 : de0 <= de1}{th1 : de1 <= de}{th : de0 <= de}
           {ph0 : ga0 <= ga1}{ph1 : ga1 <= ga}{ph : ga0 <= ga} 
           {sg0 : sb de0 -| ga0}{sg1 : sb de1 -| ga1}{sg : sb de -| ga}
           -> [ th0 & th1 ]~ th
           -> [ th1 ?$ sg ]~[ sg1 ^ ph1 ]
           -> [ th0 ?$ sg1 ]~[ sg0 ^ ph0 ]
           -> [ ph0 & ph1 ]~ ph
           -> [ th ?$ sg ]~[ sg0 ^ ph ]
  coDr (v -^ .<>) (d1 -^ r1) d0 w
    with _ , a , b <- asso02 (_ , w , r1)
    = coDr v d1 d0 a -^ b
  coDr (v -^, .<>) (d1 -, (r1 , s1 /| u1 |\ t1)) (d0 -^ r0) w
    with _ , a , b <- asso03 (_ , r0 , s1)
       | _ , c , e <- asso02 (_ , a , r1)
       | r~ <- compQ (_ , b) (_ , w)
    = (coDr v d1 d0 c) -^ e
  coDr (v -, .<>) (d1 -, (r1 , s1 /| u1 |\ t1)) (d0 -, (r0 , s0 /| u0 |\ t0)) w
    with _ , a , b <- asso03 (_ , r0 , s1)
       | _ , c , e <- asso02 (_ , a , r1)
       | _ , f , g <- asso03 (_ , s0 , w)
       | _ , h , i <- asso03 (_ , t0 , w)
       | r~ <- compQ (_ , b) (_ , g)
       | r~ <- compQ (_ , i) (_ , t1)
    = coDr v d1 d0 c -, (e , f /| u0 |\ h)
  coDr [] [] [] [] = []

  drIs : forall {xi de}(th : xi <= de) -> [ th ?$ is ]~[ is ^ th ]
  drIs (th -^ y) = drIs th -^ (absr _ -^ y)
  drIs (th -, x) = drIs th -,
    ((absr _ -^ x) , absl _ -^, x /| lll -^, <> |\ no& _ -, x)
  drIs [] = []

  roof : forall {xi0 xi1 de ga up0 up1}
      -> {th0 : xi0 <= de}{th1 : xi1 <= de}{ph0 : up0 <= ga}{ph1 : up1 <= ga}
      -> {sg : sb de -| ga}{ta0 : sb xi0 -| up0}{ta1 : sb xi1 -| up1}
      -> [ th0 ?$ sg ]~[ ta0 ^ ph0 ]
      -> th0 /u\ th1
      -> [ th1 ?$ sg ]~[ ta1 ^ ph1 ]
      -> ph0 /u\ ph1
  roof (_-^_ {u = au} a x) (u -^, .<>) (b -, (bt , bC)) =
    copGluR (x /| roof a u b |\ bt) bC au
  roof (_-,_ {u = au} a (at , aC)) (u -,^ .<>) (b -^ x) =
    covSwap (copGluR (copSwap (at /| roof a u b |\ x)) aC au)
  roof (_-,_ {u = au} a (at , aC)) (u -, .<>) (b -, (bt , bC)) =
    copDis aC bC (at /| roof a u b |\ bt) au
  roof [] [] [] = []

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
          -> [ th ?$ sg ]~[ sgl ^ th' ] * [ s $ sgl ]~ s'
          -> (u' : th' /u\ ph')
          -> [ ph ?$ sg ]~[ sgr ^ ph' ] * [ t $ sgr ]~ t'
          -> [ s </ l ! u \> t $ sg ]~ (s' </ l ! u' \> t')

  subQ : forall {k de ga}{t : k -| de}{sg : sb de -| ga}(a b : < [ t $ sg ]~_ >) -> a ~ b
  subQ (_ , var) (_ , var) = r~
  subQ (_ , (` a)) (_ , (` .a)) = r~
  subQ (_ , (ff\\ a)) (_ , (ff\\ b)) with r~ <- subQ (_ , a) (_ , b) = r~
  subQ (_ , (tt\\ a)) (_ , (tt\\ b)) with r~ <- subQ (_ , a) (_ , b) = r~
  subQ (_ , (m #$ a)) (_ , (.m #$ b)) with r~ <- subQ (_ , a) (_ , b) = r~
  subQ (_ , []) (_ , []) = r~
  subQ (_ , _</_\>_ {u = u} (aq , a) ab (bq , b)) (_ , ((cq , c) </ cd \> (dq , d)))
    with r~ , r~ <- selSbQ (_ , aq) (_ , cq) , selSbQ (_ , bq) (_ , dq)
       | r~ , r~ <- subQ (_ , a) (_ , c) , subQ (_ , b) (_ , d)
       | r~ <- covQ ab cd
    = r~

  sub : forall {k de ga}(t : k -| de)(sg : sb de -| ga) -> < [ t $ sg ]~_ >
  fst (sub var ([] </ sb ! u \> t))
     with r~ , _ <- isRRRdammit u = t
  snd (sub var ([] </ sb ! u \> t))
     with r~ , r~ , r~ , r~ <- isRRRdammit u = var
  sub (` x) [] = _ , ` x
  sub (ff \\ t) sg = let _ , t' = sub t sg in _ , ff\\ t'
  sub (tt \\ t) sg = let _ , t' = sub t (sg </ sb ! lll -^, <> \> var) in
    _ , tt\\ t'
  sub (m #$ rh) sg = let _ , ta = sub rh sg in _ , m #$ ta
  sub [] [] = _ , []
  sub (s </ k ! u \> t) sg =
    let _ , ssg = doctor (luth u) sg in
    let _ , s' = sub _ _ in
    let _ , tsg = doctor (ruth u) sg in
    let _ , t' = sub _ _ in
    _ , ((ssg , s') </ roof ssg u tsg \> (tsg , t'))

  _$is : forall {k de}(t : k -| de) -> [ t $ is ]~ t
  var $is = var
  (` a) $is = ` a
  (ff \\ t) $is = ff\\ (t $is)
  (tt \\ t) $is = tt\\ (t $is)
  (m #$ rh) $is = m #$ (rh $is)
  [] $is = []
  (s </ l ! u \> t) $is = (drIs _ , (s $is)) </ u \> (drIs _ , (t $is))

  is$ : forall {ga de}(sg : sb ga -| de) -> [ is $ sg ]~ sg
  is$ [] = []
  is$ (sg </ sb ! u \> t) =
    ((ioDr sg -^ absl _) , (is$ sg)) </ u \>
    (noDr sg -, (no& _ , no& _ /| rrr |\ absl _) , var)

  drCo : forall {de ga xi}
      {sg : sb de -| ga}{ta : sb ga -| xi}{up : sb de -| xi}
    {(_ , th) : < _<= de >}{(_ , ph) : < _<= ga >}{(_ , ps) : < _<= xi >}
      {sg' ta' up'}
    -> [ sg $ ta ]~ up
    -> [ th ?$ sg ]~[ sg' ^ ph ]
    -> [ ph ?$ ta ]~[ ta' ^ ps ]
    -> [ sg' $ ta' ]~ up'
    -> [ th ?$ up ]~[ up' ^ ps ]
  drCo [] [] [] [] = []
  drCo ((q0 , c0) </ u0 \> (q1 , c1)) d0 d1 e = {!luth u0!}

  tm-co : forall {k de ga xi}
    {t0 : k -| de}{sg : sb de -| ga}{t1 : k -| ga}{ta : sb ga -| xi}{t2 : k -| xi}
    {up : sb de -| xi}
    -> [ t0 $ sg ]~ t1 -> [ t1 $ ta ]~ t2
    -> [ sg $ ta ]~ up -> [ t0 $ up ]~ t2
  tm-co var r ((a , []) </ u' \> (c , d))
    with r~ <- selSbQ (_ , c) (_ , ioDr _)
       | r~ <- selSbQ (_ , a) (_ , noDr _)
       | r~ <- covQ u' rrr
       | r~ <- subQ (_ , r) (_ , d)
       = var
  tm-co (` a) (` .a) [] = ` a
  tm-co (ff\\ l) (ff\\ r) c = ff\\ tm-co l r c
  tm-co (tt\\ l) (tt\\ r) c =
    tt\\ (tm-co l r
      ((ioDr _ -^ (absr _ -^ <>) , c)
       </ lll -^, <> \>
       (noDr _ -, (no& _ , (no& _ -^, <>) /| rrr |\ no& _ -, <>) , var)))
  tm-co (m #$ l) (.m #$ r) c = m #$ tm-co l r c
  tm-co [] [] [] = []
  tm-co ((th , sg) </ u \> (th' , s)) ((ph , ta) </ w \> (ph' , t)) c =
    {!tm-co sg ta !}


{-
  sel-fac : forall
    {de0 de1 de2}{th01 : de0 <= de1}{th12 : de1 <= de2}{th02 : de0 <= de2}
    {ga0 ga2}{ph02 : ga0 <= ga2}
    {sg0 sg2}
    -> [ th01 & th12 ]~ th02
    -> [ th02 ?$ sg2 ]~[ sg0 ^ ph02 ]
    -> < ga0 <=_ *: _<= ga2 > >< \ (_ , ph01 , ph12)
    -> [ ph01 & ph12 ]~ ph02
    *  < [ th01 ?$_]~[ sg0 ^ ph01 ] *: [ th12 ?$ sg2 ]~[_^ ph12 ] >
  sel-fac {th01 = th01}{th12 = th12} {sg2 = sg2} v x
    with sg1 ^ ph12 , y <- doctor th12 sg2
       | sg0' ^ ph01 , z <- doctor th01 sg1
       = {!!}
    
-}  
    
{-
  sel-co : forall {de ga xi}
      {sg : sb de -| ga}{ta : sb ga -| xi}{up : sb de -| xi}
    {(_ , th) : < _<= de >}{(_ , ph) : < _<= ga >}{(_ , ps) : < _<= xi >}
      {sg' ta'}
    -> [ sg $ ta ]~ up
    -> [ th ?$ sg ]~[ sg' ^ ph ]
    -> [ ph ?$ ta ]~[ ta' ^ ps ]
    -> < [ sg' $ ta' ]~_ *: [ th ?$ up ]~[_^ ps ] >
  sel-co [] [] [] = _ , [] , []
  sel-co ((sgq , sg) </ u \> s) (a -^ x) b
    with _ , w , _ , c , d <- sel-fac x b
       | r~ <- selSbQ (_ , sgq) (_ , d)
       | _ , up' , ps' <- sel-co sg a c
       = _ , up' , ps' -^ w
  sel-co (sg </ u \> s) (a -, (x , av /| au |\ aw)) b = {!!}
-}
{-
  thin-co : forall {de' de ga xi}(th : de' <= de)
       {sg : sb de -| ga}{ta : sb ga -| xi}{up : sb de -| xi}
    -> [ sg $ ta ]~ up
    -> {(ga' , ph) : < _<= ga >}{sg' : sb de' -| ga'}
    -> (th ?$ sg) ~ (sg' ^ ph)
    -> {a@(xi' , ps) : < _<= xi >}{ta' : sb ga' -| xi'}
    -> (ph ?$ ta) ~ (ta' ^ ps)
    -> {b@(xi'' , ch) : < _<= xi >}{up' : sb de' -| xi''}
    -> (th ?$ up) ~ (up' ^ ch)
    -> (a ~ b) >< \ { r~ -> [ sg' $ ta' ]~ up' }
  thin-co [] [] r~ r~ r~ = r~ , []
  thin-co (th -^ .<>) (_</_\>_ {l = sb} {u = u} (aq , a) u' (bq , b)) r~ q r~
    = {!thin-co th a r~ r~ r~!}
  thin-co (th -, x) ((aq , a) </ u' \> (bq , b)) p q r = {!!}
    

  tm-co : forall {k de ga xi}
    {t0 : k -| de}{sg : sb de -| ga}{t1 : k -| ga}{ta : sb ga -| xi}{t2 : k -| xi}
    {up : sb de -| xi}
    -> [ t0 $ sg ]~ t1 -> [ t1 $ ta ]~ t2
    -> [ sg $ ta ]~ up -> [ t0 $ up ]~ t2
  tm-co {ta = ta} var t12 ((r~ , sg) </ u' \> (r~ , t))
    with no ?$ ta | no?$ ta | io ?$ ta | io?$ ta
  tm-co {ta = ta} var t12 ((r~ , []) </ u' \> (r~ , t)) | _ | r~ | _ | r~
    with r~ <- subQ (_ , t12) (_ , t)
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
  tm-co (_</_\>_ {u = u} (aq , a) u' (bq , b)) ((cq , c) </ u'' \> (dq , d)) stu
    with r~ , stul <- thin-co (luth u) stu aq cq r~
       | r~ , stur <- thin-co (ruth u) stu bq dq r~
    = (r~ , tm-co a c stul) </ u'' \> (r~ , tm-co b d stur)

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

-}

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
