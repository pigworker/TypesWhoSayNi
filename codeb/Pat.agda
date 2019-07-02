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

 data RefineR {s ga de}(ph : ga <= de) : Pat (` s) ga -> Pat (` s) de -> Set
 
 Refine : forall D {ga de}(ph : ga <= de) ->
          Pat D ga -> Pat D de -> Set
 Refine un' ph r p = One
 Refine (D *' E) ph (rd </ ru \> re) (pd </ pu \> pe) =
   (_ *\ \ ph0 -> Refine D ph0 rd pd * Square (ph0 ^ u/ pu) (u/ ru ^ ph)) *
   (_ *\ \ ph1 -> Refine E ph1 re pe * Square (ph1 ^ u\ pu) (u\ ru ^ ph))
 Refine (b >' D) ph (ll r) (ll p) = Refine D (ph -, b) r p
 Refine (b >' D) ph (ll r) (kk p) = Zero
 Refine (b >' D) ph (kk r) (ll p) = Refine D (ph -^ b) r p
 Refine (b >' D) ph (kk r) (kk p) = Refine D ph r p
 Refine (` s) ph r p = RefineR ph r p
 
 data RefineR {s ga de} ph where
   hole : forall {r} -> RefineR ph r hole
   _-_  : forall c {r p} -> Refine (Ds (pc c)) ph r p ->
          RefineR ph (c - r) (c - p)

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
-}

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

{-
  get : forall {D : Sort}{ga}{p : Pat D ga}(m : Stan D p)
        {k} -> Meta D p k -> (M !< ` fst k) (snd k)
  get (val t) hole = t
  get (.c - m) (c - x) = get m x
  get (m , _) (inl x) = get m x
  get (_ , m) (inr x) = get m x
  get m (kk x) = get m x
  get m (ll x) = get m x
-}

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

  refine : forall D {ga}
           (r : Pat D ga){rh}{t : (M !< D) ga} -> Match D r rh t ->
           forall {de}(ph : ga <= de)(p : Pat D de) -> Refine D ph r p ->
           _ *\ \ th -> Stan D p *\ \ pi ->
           thin t & ph =< th * Match D p pi (thing t ^ th)
  refine un' null unMa [] null <> = ! ! [] , unMa
  refine (D *' E) (rd </ ru \> re) {t = t}
    (prMa {td = td ^ th0} {te ^ th1}{_}{ps2}{ps3} vd ve
      (mkPr { ! ch0 , th , ch1} xd tu xe) md me)
    ph (pd </ pu \> pe) ((ph0 , rpd , ad ^ bd) , (ph1 , rpe , ae ^ be))
    with refine D rd md ph0 pd rpd | refine E re me ph1 pe rpe | th -&- ph
  ... | ps0 , pid , wd , dh | ps1 , pie , we , eh | y
    with stkSq wd y (xd ^ vd) (bd ^ ad) | stkSq we y (xe ^ ve) (be ^ ae)
  ... | fd ^ gd | fe ^ ge
    = ! (pid , pie) , y , prMa gd ge (mkPr fd tu fe) dh eh
  refine (b >' D) (ll r) (llMa m) ph (ll p) rp
    with refine D r m (ph -, b) p rp
  ... | .(_ -, b) , pi , w -, .b , h = ! ! w , llMa h
  ... | .(_ -^ b) , pi , w -^, .b , h = ! ! w , llMa h
  refine (b >' D) (kk r) (kkMa m) ph (ll p) rp
    with refine D r m (ph -^ b) p rp
  ... | .(_ -^ b) , pi , w -^ .b , h = ! ! w , llMa h
  refine (b >' D) (kk r) (kkMa m) ph (kk p) rp
    with refine D r m ph p rp ; ... | th , pi , w , h = ! ! w , kkMa h
  refine (b >' D) (ll _) m ph (kk _) ()
  refine (` s) r {t = t ^ th} m ph .hole hole = ! ! th -&- ph , hoMa
  refine (` s) .(c - _) (cnMa .c m) ph .(c - _) (c - rp)
    with refine (Ds (pc c)) _ m ph _ rp
  ... | th , pi , w , h = ! ! w , cnMa c h
           
