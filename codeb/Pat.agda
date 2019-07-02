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
 (pci : {s : S}(b c : Pc s) -> pc b ~ pc c -> b ~ c)
 where

 open TERM Cn Ds b2s

 data PatR (s : S)(ga : Bwd B) : Set

 Pat : Sort -> Bwd B -> Set
 Pat D = Rlv D PatR

 data PatR s ga where
   hole : Pat (` s) ga
   _-_  : (c : Pc s)(pr : Pat (Ds (pc c)) ga) -> Pat (` s) ga

 data RfnR {s ga de}(ph : ga <= de) : Pat (` s) de -> Pat (` s) ga -> Set
 
 Rfn : forall D {ga de}(ph : ga <= de) -> Pat D de -> Pat D ga -> Set
 Rfn un'      ph p      r      = One
 Rfn (D *' E) ph (pd </ pu \> pe) (rd </ ru \> re) =
   (_ *\ \ ph0 -> Rfn D ph0 pd rd * Square (ph0 ^ u/ pu) (u/ ru ^ ph)) *
   (_ *\ \ ph1 -> Rfn E ph1 pe re * Square (ph1 ^ u\ pu) (u\ ru ^ ph))
 Rfn (b >' D) ph (ll p) (ll r) = Rfn D (ph -, b) p r
 Rfn (b >' D) ph (kk p) (ll r) = Zero
 Rfn (b >' D) ph (ll p) (kk r) = Rfn D (ph -^ b) p r
 Rfn (b >' D) ph (kk p) (kk r) = Rfn D ph p r
 Rfn (` s)    ph p      r      = RfnR ph p r
 
 data RfnR {s ga de} ph where
   hole : forall {r} -> RfnR ph hole r
   _-_  : forall c {p r} -> Rfn (Ds (pc c)) ph p r ->
          RfnR ph (c - p) (c - r)

 restrict : forall D {ga de}(ph : ga <= de)(p : Pat D de) -> < Rfn D ph p >
 restrict un' [] null = null , <>
 restrict (D *' E) ph (pd </ pu \> pe) = 
   let ! ! (sd , _) , (se , _) , u = ph <u pu
       rd , rpd = restrict D _ pd ; re , rpe = restrict E _ pe
   in  rd </ u \> re , (! rpd , sd) , ! rpe , se
 restrict (b >' D) ph (ll p) = let r , rp = restrict D (ph -, b) p in
   ll r , rp
 restrict (b >' D) ph (kk p) = let r , rp = restrict D ph p in kk r , rp
 restrict (` s) ph hole = hole , hole
 restrict (` s) ph (c - p) = let r , rp = restrict (Ds (pc c)) ph p in
   c - r , c - rp

 Mat : Sort -> Bwd B -> Set
 Mat D ga = Maybe (Pat D :< ga)

 MRfn : forall D {ga}(p r : Mat D ga) -> Set
 MRfn D _              no             = One
 MRfn D (yes (p ^ ph)) (yes (r ^ th)) =
   _ *\ \ ps -> ps & ph =< th * Rfn D ps p r
 MRfn D no             (yes r)        = Zero

 

 unify : forall D {ga}(p q : Mat D ga) -> < MRfn D p :* MRfn D q >
 unify^ : forall D {ga ga0 ga1 ga'}
   {ph : ga0 <= ga}{ps : ga1 <= ga}{ph' : ga' <= ga0}{ps' : ga' <= ga1}
   (p : Pat D ga0)(q : Pat D ga1){s : Square (ph' ^ ph) (ps' ^ ps)} ->
   Pullback s ->
   Mat D ga' *\ \
     { (yes (r ^ ch)) -> Rfn D (ch -<- ph') p r * Rfn D (ch -<- ps') q r
     ; no -> One }
 unify D no  _ = no , _
 unify D _  no = no , _
 unify D (yes (p ^ ph)) (yes (q ^ ps)) with ph \^/ ps
 ... | ph' ^ ps' , s@(om , vp , vq) , s^ with unify^ D p q s^
 ... | no , _ = no , _
 ... | yes r , pr , qr
     = yes (r :- fst s) , thin r <& vp ^ pr , thin r <& vq ^ qr
 unify^ un' null null s^ = yes (null ^ noth) , _
 unify^ (D *' E) {ph = ph}{ps}{ph'}{ps'} (pd </ pu \> pe) (qd </ qu \> qe) s^
   with u/ pu -<- ph | u/ qu -<- ps | puller s^ (u/ pu -&- ph) (u/ qu -&- ps)
      | u\ pu -<- ph | u\ qu -<- ps | puller s^ (u\ pu -&- ph) (u\ qu -&- ps)
 ... | phd | psd | kad ^ lad , (mud , tdp , tdq)  , ds^ , omd , ad , xe , bd
     | phe | pse | kae ^ lae , (mue , tep , teq) , es^ , ome , ae , ye , be
   with unify^ D pd qd ds^ | unify^ E pe qe es^
 ... | no , _ | _      = no , _
 ... | _      | no , _ = no , _
 ... | yes (rd ^ chd) , pdh , qdh | yes (re ^ che) , peh , qeh
   with chd -<- omd | chd -&- omd | che -<- ome | che -&- ome
      | chd -<- omd /+\ che -<- ome
 ... | nud | wad | nue | wae | (! thrd , ch , thre) , wd , we , ru
   = yes (rd </ ru \> re ^ ch)
   , ( pdh ^ flipSq (stkSq (chd -&- kad) (ch -&- ph') (wd ^ wad) ad)
     , peh ^ flipSq (stkSq (che -&- kae) (ch -&- ph') (we ^ wae) ae))
   , ( qdh ^ flipSq (stkSq (chd -&- lad) (ch -&- ps') (wd ^ wad) bd)
     , qeh ^ flipSq (stkSq (che -&- lae) (ch -&- ps') (we ^ wae) be))
 unify^ (b >' D) (ll p) (ll q) s^ = {!!}
 unify^ (b >' D) (ll p) (kk q) s^ = {!!}
 unify^ (b >' D) (kk p) (ll q) s^ = {!!}
 unify^ (b >' D) (kk p) (kk q) s^ = {!!}
 unify^ (` s) {ps' = ps'} hole q s^ with restrict (` s) ps' q
 ... | r , qr = yes (r ^ idth)
              , hole , (qr [ RfnR $~ sym (id< ps') ~$~ r~ ~$~ r~ >)
 unify^ (` s) {ph' = ph'} p hole s^ with restrict (` s) ph' p
 ... | r , pr = yes (r ^ idth)
              , (pr [ RfnR $~ sym (id< ph') ~$~ r~ ~$~ r~ >) , hole
 unify^ (` s) (c - p) (d - q) s^ with cq? (pc c) (pc d)
 unify^ (` s) (c - p) (d - q) s^ | inl _ = no , _
 unify^ (` s) (c - p) (d - q) s^ | inr x with pci c d x
 ... | r~ with unify^ (Ds (pc c)) p q s^
 ... | no , _ = no , _
 ... | yes r , g , h = yes ((c -_) :$ r) , (c - g) , (c - h)

{-
 unify : forall D {ga}(p q : Mat D ga) -> < MRfn D p :* MRfn D q >
 unify^ : forall D {ga ga0 ga1 ga'}
   {ph : ga0 <= ga}{ps : ga1 <= ga}{ph' : ga' <= ga0}{ps' : ga' <= ga1}
   (p : Pat D ga0)(q : Pat D ga1){s : Square (ph' ^ ph) (ps' ^ ps)} ->
   Pullback s -> < MRfn D (yes (p ^ ph)) :* MRfn D (yes (q ^ ps)) >
 unify D no  _ = no , _
 unify D _  no = no , _
 unify D (yes (p ^ ph)) (yes (q ^ ps)) with ph \^/ ps
 ... | ph' ^ ps' , s , s^ = {!!}
 unify^ un' {ph' = []} {[]} null null s^ =
   (yes (null ^ noth)) , (no& _ ^ <> , no& _ ^ <>)
 unify^ (D *' E) {ph = ph} {ps} (pd </ pu \> pe) (qd </ qu \> qe) s^
   with u/ pu -<- ph | u/ qu -<- ps | puller s^ (u/ pu -&- ph) (u/ qu -&- ps)
      | u\ pu -<- ph | u\ qu -<- ps | puller s^ (u\ pu -&- ph) (u\ qu -&- ps)
 ... | phd | psd | ! ! ds^ , ! ad , xe , bd
     | phe | pse | ! ! es^ , ! ae , ye , be
   with unify^ D pd qd ds^ | unify^ E pe qe es^
 ... | no , _ | _      = no , _
 ... | _      | no , _ = no , _
 ... | yes (rd ^ chd) , vpd ^ prd , vqd ^ qrd
     | yes (re ^ che) , vpe ^ pre , vqe ^ qre
   with chd /+\ che
 ... | (! _ , ch , _) , wd , we , ru
   = yes (rd </ ru \> re ^ {!!})
   , (! {!!} , prd ^ {!!} , pre ^ {!!})
   , (! {!!} , qrd ^ {!!} , qre ^ {!!})
 unify^ (b >' D) p q s^ = {!!}
 unify^ (` s) p q s^ = {!!}
-}

{-
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
           {pd : Pat D ga0}{pu : ph0 /u\ ph1}{pe : Pat E ga1}{pid pie}
           {td : (M !< D) ga0}{te : (M !< E) ga1}{t : (M !< D *' E) ga}
           {ps0 : _ <= ga}{ps1 : _ <= ga} ->
           thin td & ph0 =< ps0 -> thin te & ph1 =< ps1 ->
           Pr (thing td ^ ps0) (thing te ^ ps1) t ->
           Match D pd pid td -> Match E pe pie te ->
           Match (D *' E) (pd </ pu \> pe) (pid , pie) t
    kkMa : forall {b D ga}{p : Pat D ga}{pi : Stan D p}{t : (M !< D) ga} ->
           Match D p pi t -> Match (b >' D) (kk p) pi (kk :$ t)
    llMa : forall {b D ga}{p : Pat D (ga -, b)}{pi : Stan D p}
           {t : (M !< D) (ga -, b)} ->
           Match D p pi t -> Match (b >' D) (ll p) pi (b \\ t) -- green slime

  _~Ma~_ : forall {D ga}{p : Pat D ga}{pi : Stan D p}{t0 t1 : (M !< D) ga} ->
           Match D p pi t0 -> Match D p pi t1 -> t0 ~ t1
  hoMa ~Ma~ hoMa = r~
  cnMa c m ~Ma~ cnMa .c n with m ~Ma~ n ; ... | r~ = r~
  unMa ~Ma~ unMa = r~
  prMa wd we mp md me ~Ma~ prMa vd ve np nd ne
    with md ~Ma~ nd | me ~Ma~ ne ; ... | r~ | r~
    with wd ~&~ vd | we ~&~ ve ; ... | r~ | r~ = mp ~Pr~ np
  kkMa m ~Ma~ kkMa n with m ~Ma~ n ; ... | r~ = r~
  llMa m ~Ma~ llMa n with m ~Ma~ n ; ... | r~ = r~

  stanMa : forall D {ga}(p : Pat D ga) pi -> Match D p pi (stan D p pi)
  stanMa un' null <> = unMa
  stanMa (D *' E) (pd </ pu \> pe) (pid , pie)
    with stan D pd pid | stanMa D pd pid | stan E pe pie | stanMa E pe pie
  ... | td ^ th0 | dh | te ^ th1 | eh
    with th0 -<- u/ pu | th0 -&- u/ pu | th1 -<- u\ pu | th1 -&- u\ pu
  ... | ch0 | v0 | ch1 | v1 with ch0 /+\ ch1
  ... | (! ps0 , th , ps1) , w0 , w1 , tu
      = prMa v0 v1 (mkPr w0 tu w1) dh eh
  stanMa (b >' D) (ll p) pi = llMa (stanMa D p pi)
  stanMa (b >' D) (kk p) pi = kkMa (stanMa D p pi)
  stanMa (` s) hole (val t) = hoMa
  stanMa (` s) (c - p) (.c - pi) = cnMa c (stanMa _ p pi)

  rfn : forall D {ga}
           (r : Pat D ga){rh}{t : (M !< D) ga} -> Match D r rh t ->
           forall {de}(ph : ga <= de)(p : Pat D de) -> Rfn D ph r p ->
           _ *\ \ th -> Stan D p *\ \ pi ->
           thin t & ph =< th * Match D p pi (thing t ^ th)
  rfn un' null unMa [] null <> = ! ! [] , unMa
  rfn (D *' E) (rd </ ru \> re) {t = t}
    (prMa {td = td ^ th0} {te ^ th1}{_}{ps2}{ps3} vd ve
      (mkPr { ! ch0 , th , ch1} xd tu xe) md me)
    ph (pd </ pu \> pe) ((ph0 , rpd , ad ^ bd) , (ph1 , rpe , ae ^ be))
    with rfn D rd md ph0 pd rpd | rfn E re me ph1 pe rpe | th -&- ph
  ... | ps0 , pid , wd , dh | ps1 , pie , we , eh | y
    with stkSq wd y (xd ^ vd) (bd ^ ad) | stkSq we y (xe ^ ve) (be ^ ae)
  ... | fd ^ gd | fe ^ ge
    = ! (pid , pie) , y , prMa gd ge (mkPr fd tu fe) dh eh
  rfn (b >' D) (ll r) (llMa m) ph (ll p) rp
    with rfn D r m (ph -, b) p rp
  ... | .(_ -, b) , pi , w -, .b , h = ! ! w , llMa h
  ... | .(_ -^ b) , pi , w -^, .b , h = ! ! w , llMa h
  rfn (b >' D) (kk r) (kkMa m) ph (ll p) rp
    with rfn D r m (ph -^ b) p rp
  ... | .(_ -^ b) , pi , w -^ .b , h = ! ! w , llMa h
  rfn (b >' D) (kk r) (kkMa m) ph (kk p) rp
    with rfn D r m ph p rp ; ... | th , pi , w , h = ! ! w , kkMa h
  rfn (b >' D) (ll _) m ph (kk _) ()
  rfn (` s) r {t = t ^ th} m ph .hole hole = ! ! th -&- ph , hoMa
  rfn (` s) .(c - _) (cnMa .c m) ph .(c - _) (c - rp)
    with rfn (Ds (pc c)) _ m ph _ rp
  ... | th , pi , w , h = ! ! w , cnMa c h
           
-}
