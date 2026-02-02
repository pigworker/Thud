module Thud where

_-_ : forall {i j k}
  {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  -> (a : A) -> C a (f a)
(f - g) a = g (f a)

module _ {X : Set} where

  data _~_ (x : X) : X -> Set where
    r~ : x ~ x

  _~[_>_ : (x : X){y z : X} -> x ~ y -> y ~ z -> x ~ z
  x ~[ r~ > q = q

  _<_]~_ : (x : X){y z : X} -> y ~ x -> y ~ z -> x ~ z
  x < r~ ]~ q = q

  _[QED] : (x : X) -> x ~ x
  x [QED] = r~

  infixr 2 _~[_>_ _<_]~_
  infixr 3 _[QED]

  rf : (x : X) -> x ~ x
  rf x = r~

  leib : {x y : X} -> x ~ y -> forall {l}(P : X -> Set l) ->
    P x -> P y
  leib r~ P p = p

_~$~_ : {X Y : Set}{f g : X -> Y} -> f ~ g -> {a b : X} -> a ~ b -> f a ~ g b
r~ ~$~ r~ = r~
infixl 4 _~$~_


data Empty : Set where
record Zero : Set where
  field
    .bad : Empty
magic : Zero -> forall {k}{X : Set k} -> X
magic () {k} {X}

record One : Set where
  constructor <>

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

Lt : Nat -> Nat -> Set
Lt x ze = Zero
Lt ze (su y) = One
Lt (su x) (su y) = Lt x y

record Fin (n : Nat) : Set where
  constructor #
  field
    fog : Nat
    {.smaa} : Lt fog n
open Fin public

fs : forall {n} -> Fin n -> Fin (su n)
fs (# n {p}) = # (su n) {p}

_<01>_ : forall {k}{P : Fin 2 -> Set k}
  -> P (# 0)
  -> P (# 1)
  -> (x : Fin 2) -> P x
(p0 <01> p1) (# 0) = p0
(p0 <01> p1) (# 1) = p1

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
infixr 10 _,_ _*_
_*_ _+_ : Set -> Set -> Set
S * T = S >< \ _ -> T
S + T = Fin 2 >< (S <01> T)

<:_:> : {X : Set}(P : X -> Set) -> Set
<: P :> = _ >< P

data UF : Set
ElF : UF -> Set

data UF where
  `0 `1 : UF
  `Fin : Nat -> UF
  _`><_ : (S : UF)(T : ElF S -> UF) -> UF

ElF `0 = Zero
ElF `1 = One
ElF (`Fin n) = Fin n
ElF (S `>< T) = ElF S >< \ s -> ElF (T s)

_`*_ _`+_ : UF -> UF -> UF
S `* T = S `>< \ _ -> T
S `+ T = `Fin 2 `>< (S <01> T)


data _#*_ (n : Nat)(P : Fin n -> Set) : Set
_#*'_ : (n : Nat)(P : Fin n -> Set) -> Set

data _#*_ n P where
  <_> : n #*' P -> n #* P
  
ze #*' P = One
su n #*' P = P (# 0) * (n #* (fs - P))

#\ : {n : Nat}{P : Fin n -> Set} -> ((i : Fin n) -> P i) -> n #* P
#[_]\ : (n : Nat){P : Fin n -> Set} -> ((i : Fin n) -> P i) -> n #*' P
#\ {n} f = < #[ n ]\ f >
#[ ze ]\ f = <>
#[ su n ]\ f = f (# 0) , #\ (fs - f)

_#$_ : {n : Nat}{P : Fin n -> Set} -> n #* P -> (i : Fin n) -> P i
#[_]_$_ : (n : Nat){P : Fin n -> Set} -> n #*' P -> (i : Fin n) -> P i
_#$_ {n} < f > i = #[ n ] f $ i
#[ su n ] p , ps $ # ze = p
#[ su n ] p , ps $ # (su i) {l} = ps #$ (# i {l})

_#$~_ : {n : Nat}{P : Fin n -> Set} (f : n #* P)(g : (i : Fin n) -> P i) -> Set
f #$~ g = forall i -> (f #$ i) ~ g i

beta# : (n : Nat){P : Fin n -> Set}(f : (i : Fin n) -> P i)
  -> #\ f #$~ f 
beta# (su n) f (# ze) = r~
beta# (su n) f (# (su i) {l}) = beta# n (fs - f) (# i {l})

data _#>_ (S : UF)(T : ElF S -> Set) : Set
_#>'_ : (S : UF)(T : ElF S -> Set) -> Set

data _#>_ S T where
  <_> : S #>' T -> S #> T

`0 #>' T = One
`1 #>' T = T <>
`Fin n #>' T = n #* T
(R `>< S) #>' T = R #> \ r -> S r #> \ s -> T (r , s)

\\ : {S : UF}{T : ElF S -> Set} -> ((s : ElF S) -> T s) -> S #> T
[_]\ : (S : UF){T : ElF S -> Set} -> ((s : ElF S) -> T s) -> S #>' T
\\ {S} f = < [ S ]\ f >
[ `0 ]\ f = <>
[ `1 ]\ f = f <>
[ `Fin n ]\ f = #\ f 
[ R `>< S ]\ f = <( [ R ]\ \ r -> \\ \ s -> f (r , s) )>

_$$_ : {S : UF}{T : ElF S -> Set} -> S #> T -> ((s : ElF S) -> T s)
[_]_$_ : (S : UF){T : ElF S -> Set} -> S #>' T -> ((s : ElF S) -> T s)
_$$_ {S} < f > s = [ S ] f $ s
[ `1 ] t $ <> = t
[ `Fin n ] f $ s = f #$ s
[ R `>< S ] < f > $ (r , s) = ([ R ] f $ r) $$ s

infixl 50 _$$_

_$~_ : {S : UF}{T : ElF S -> Set}(f : S #> T)(g : (s : ElF S) -> T s) -> Set
_$~_ {S} f g = (s : ElF S) -> (f $$ s) ~ g s

beta : {S : UF}{T : ElF S -> Set}(f : (s : ElF S) -> T s) -> (\\ f) $~ f
beta' : (S : UF){T : ElF S -> Set}(f : (s : ElF S) -> T s)
  -> (s : ElF S) -> ([ S ] ([ S ]\ f) $ s) ~ f s
beta {S} f = beta' S f
beta' `1 f <> = r~
beta' (`Fin n) f i = beta# n f i
beta' (R `>< S) f (r , s) =
  (([ R ] ([ R ]\ \ r -> \\ \ s -> f (r , s)) $ r) $$ s)
    ~[ rf (_$$ s) ~$~ beta' R (\ r -> \\ \ s -> f (r , s)) r >
  ((\\ \ s -> f (r , s)) $$ s)
    ~[ beta' (S r) _ _ >
  f (r , s) [QED]

eta : {S : UF}{T : ElF S -> Set}(f : S #> T) -> f $~ \ s -> f $$ s
eta f s = r~

record Ctn : Set where
  constructor _<!_
  field
    Sh : UF
    Po : ElF Sh -> UF
  [!_!] : Set -> Set
  [!_!] X = ElF Sh >< \ s -> Po s #> \ _ -> X
open Ctn public

data _<*_ (C : Ctn)(X : Set) : Set where
  <_> : [! C !] (C <* X) -> C <* X
  ! : X -> C <* X

Mu : Ctn -> Set
Mu C = C <* Zero

data RecProb : Set where
  [] : RecProb
  _?-_ : (P : UF) -> (ElF P -> RecProb) -> RecProb
  _?-'_ : (P : UF) -> (ElF P -> RecProb) -> RecProb

module _ {C : Ctn}{X : Set} where

  data Rec : C <* X -> Set where
    <_/_> : (s : ElF (Sh C)){k : Po C s #> \ _ -> C <* X}
            -> (r : (p : ElF (Po C s)) -> Rec (k $$ p))
            -> Rec < s , k >
    ! : (x : X) -> Rec (! x)

  RecIn : RecProb -> Set
  RecIn [] = C <* X
  RecIn (P ?- K) = P #> \ p -> RecIn (K p)
  RecIn (P ?-' K) = P #>' \ p -> RecIn (K p)

  RecOut : (r : RecProb) -> RecIn r -> Set
  RecOut [] t = Rec t
  RecOut (P ?- K) f = (p : ElF P) -> RecOut (K p) (f $$ p)
  RecOut (P ?-' K) f =  (p : ElF P) -> RecOut (K p) ([ P ] f $ p)

  recIO : (r : RecProb)(i : RecIn r) -> RecOut r i
  recFin : (n : Nat)(r : Fin n -> RecProb)
    -> (f : n #* \ i -> RecIn (r i))
    -> (i : Fin n) -> RecOut (r i) (f #$ i)
  recIO [] < s , k > = < s / recIO (Po C s ?- \ _ -> []) k >
  recIO [] (! x) = ! x
  recIO (P ?- K) < i > = recIO (P ?-' K) i
  recIO (`0 ?-' K) i () 
  recIO (`1 ?-' K) i <> = recIO (K <>) i
  recIO (`Fin n ?-' K) f i = recFin n K f i
  recIO ((S `>< T) ?-' K) < i > (ps , pt) =
    recIO (S ?-' \ s -> T s ?- \ t -> K (s , t)) i ps pt
  recFin (su n) r < f , _ > (# ze) = recIO (r (# 0)) f
  recFin (su n) r < _ , f > (# (su i) {l}) = recFin n (fs - r) f (# i {l})

  rec : (t : C <* X) -> Rec t
  rec = recIO []

data Subst {C : Ctn}{X Y : Set}(f : X -> C <* Y)
  : C <* X -> C <* Y -> Set
  where
  
  <_/_/_> : (s : ElF (Sh C)){k : Po C s #> \ _ -> C <* X}
    {m : Po C s #> \ _ -> C <* Y}
    {l : ElF (Po C s) -> C <* Y}
    -> m $~ l ->
    (r : (p : ElF (Po C s)) -> Subst f (k $$ p) (l p))
    -> Subst f < s , k > < s , m >
    
  ! : (x : X) -> Subst f (! x) (f x)

subst : {C : Ctn}{X Y : Set}(f : X -> C <* Y)(t : C <* X) -> <: Subst f t :>
subst {C}{X}{Y} f t = help (rec t) where
  help : {t : C <* X} -> Rec t -> (C <* Y) >< Subst f t
  help < s / r > = _ , < s / beta _ / (\ p -> help (r p) .snd) >
  help (! x) = f x , ! x

_>>=_ : {C : Ctn}{X Y : Set}(t : C <* X)(f : X -> C <* Y) -> C <* Y
t >>= f = fst (subst f t)

_-*>_ : Ctn -> Ctn -> Set
(S <! P) -*> C = S #> \ s -> C <* ElF (P s)

module _ {C D : Ctn}(f : C -*> D){X : Set} where

  data Cata : C <* X -> D <* X -> Set where
    <_/_/_> : (s : ElF (Sh C)){k : Po C s #> \ _ -> C <* X}{l : ElF (Po C s) -> D <* X} ->
      (r : (p : ElF (Po C s)) -> Cata (k $$ p) (l p)) ->
      {t : D <* X} -> Subst l (f $$ s) t
      -> Cata < s , k > t
    ! : (x : X) -> Cata (! x) (! x)

  cataHelp : {x : C <* X}(r : Rec x) -> <: Cata x :>
  cataHelp < s / r > = _ , < s / (\ p -> snd (cataHelp (r p))) / snd (subst _ (f $$ s)) >
  cataHelp (! x) = _ , ! x

  cata : C <* X -> D <* X
  cata x = fst (cataHelp (rec x))

module _ {C : Ctn} where

  id* : C -*> C
  id* = \\ \ s -> < s , (\\ \ p -> ! p) >

  idLem : (s : ElF (C .Sh)) ->  < s , \\ ! > ~ (id* $$ s)
  idLem s = < s , \\ ! > < beta' (C .Sh) (\ s -> < s , \\ ! >) s ]~ (id* $$ s) [QED]

  idCata : forall {X}(t : C <* X) -> Cata id* t t
  idCata {X} = rec - idCataHelp where
    idCataHelp : {t : C <* X} -> Rec t -> Cata id* t t
    idCataHelp (<_/_> s {k} r) =
      < s / (\ p -> idCataHelp (r p)) /
        leib (idLem s) (\ z -> Subst (\ z -> k $$ z) z < s , k >)
        < s / (\ _ -> r~) / (\ p -> 
           leib (_ < beta' (C .Po s) ! p ]~ _ [QED]) (\ a -> Subst (\ z -> k $$ z) a (k $$ p))
           (! p)) >
        >
    idCataHelp (! x) = ! x

module _ {C D E : Ctn}(f : C -*> D)(g : D -*> E){X : Set} where

  _-then_ : C -*> E
  _-then_ = \\ \ cs -> cata g (f $$ cs)

  coCata : {c : C <* X}{d : D <* X}{e : E <* X}
    -> Cata f c d -> Cata g d e -> Cata _-then_ c e
  coCata < s / r / x > de
    = < s / (\ p -> coCata (r p) {!!}) / {!!} >
  coCata (! x) (! .x) = ! x

data UD : Set where
  Tt : UD
  Ff : UD
  Aa : (X : UF)(D : ElF X -> UD) -> UD
  Ex : (X : UF)(D : ElF X -> UD) -> UD

Not : UD -> UD
Not Tt = Ff
Not Ff = Tt
Not (Aa X D) = Ex X \ x -> Not (D x)
Not (Ex X D) = Aa X \ x -> Not (D x)

ElD : UD -> Set
ElD Tt = One
ElD Ff = Zero
ElD (Aa X D) = (x : ElF X) -> ElD (D x)
ElD (Ex X D) = ElF X >< \ x -> ElD (D x)

contra : (D : UD) -> ElD (Not D) -> ElD D -> Zero
contra (Aa X D) (x , ndx) d = contra (D x) ndx (d x)
contra (Ex X D) nd (x , dx) = contra (D x) (nd x) dx

decideAa# : (n : Nat)(D : Fin n -> UD) ->
  ((x : Fin n) -> ElD (Not (D x)) + ElD (D x)) ->
  (Fin n >< (\ x -> ElD (Not (D x)))) + ((x : Fin n) -> ElD (D x))
decideAa# ze D d = # 1 , \ ()
decideAa# (su n) D d with d (# 0) | decideAa# n (fs - D) (fs - d)
... | # 0 , x | _ = # 0 , # 0 , x
... | # 1 , x | # 0 , i , z = # 0 , fs i , z 
... | # 1 , x | # 1 , y = # 1 , \ { (# ze) -> x ; (# (su i) {l}) -> y (# i {l}) }

decideAa : (X : UF)(D : ElF X -> UD) ->
  ((x : ElF X) -> ElD (Not (D x)) + ElD (D x)) ->
  (ElF X >< (\ x -> ElD (Not (D x)))) + ((x : ElF X) -> ElD (D x))
decideAa `0 D d = # 1 , \ ()
decideAa `1 D d with d <>
... | # 0 , x = # 0 , <> , x
... | # 1 , x = # 1 , \ _ -> x
decideAa (`Fin n) D d = decideAa# n D d
decideAa (S `>< T) D d
  with decideAa S (\ s -> Aa (T s) \ t -> D (s , t))
    (\ s -> decideAa (T s) (\ t -> D (s , t)) (\ t -> d (s , t)))
... | # 0 , s , t , x = # 0 , (s , t) , x
... | # 1 , r = # 1 , \ (s , t) -> r s t

decideEx# : (n : Nat)(D : Fin n -> UD) ->
  ((x : Fin n) -> ElD (Not (D x)) + ElD (D x)) ->
  ((x : Fin n) -> ElD (Not (D x))) + (Fin n >< \ x -> ElD (D x))
decideEx# ze D d = # 0 , \ ()
decideEx# (su n) D d with d (# 0) | decideEx# n (fs - D) (fs - d)
... | # 0 , x | # 0 , y = # 0 , \ { (# ze) -> x ; (# (su i) {l}) -> y (# i {l}) }
... | # 0 , x | # 1 , i , y = # 1 , fs i , y
... | # 1 , x | _ = # 1 , # 0 , x

decideEx : (X : UF)(D : ElF X -> UD) ->
  ((x : ElF X) -> ElD (Not (D x)) + ElD (D x)) ->
  ((x : ElF X) -> ElD (Not (D x))) + (ElF X >< \ x -> ElD (D x))
decideEx `0 D d = # 0 , \ ()
decideEx `1 D d with d <>
... | # 0 , x = # 0 , \ _ -> x
... | # 1 , x = # 1 , _ , x
decideEx (`Fin n) D d = decideEx# n D d
decideEx (S `>< T) D d
  with decideEx S (\ s -> Ex (T s) \ t -> D (s , t))
    (\ s -> decideEx (T s) (\ t -> D (s , t)) (\ t -> d (s , t)))
... | # 0 , r = # 0 , \ (s , t) -> r s t
... | # 1 , s , t , x = # 1 , (s , t) , x

decide : (D : UD) -> ElD (Not D) + ElD D
decide Tt = # 1 , <>
decide Ff = # 0 , <>
decide (Aa X D) = decideAa X D \ x -> decide (D x)
decide (Ex X D) = decideEx X D \ x -> decide (D x)

decideF : (X : UF) -> (ElF X -> Zero) + ElF X
decideF X with decide (Ex X \ _ -> Tt)
... | # 0 , r = # 0 , r
... | # 1 , x , <> = # 1 , x

eq# : (n : Nat)(a b : Fin n) -> UD >< \ Q -> ElD Q -> a ~ b
eq# (su n) (# ze) (# ze) = Tt , \ _ -> r~
eq# (su n) (# ze) (# (su j)) = Ff , \ ()
eq# (su n) (# (su i)) (# ze) = Ff , \ ()
eq# (su n) (# (su i) {l}) (# (su j) {k}) .fst = eq# n (# i {l}) (# j {k}) .fst
eq# (su n) (# (su i) {l}) (# (su j) {k}) .snd q
  with r~ <- eq# n (# i {l}) (# j {k}) .snd q = r~

eqF : (X : UF)(a b : ElF X) -> UD >< \ Q -> ElD Q -> a ~ b
eqF `1 a b = Tt , \ _ -> r~
eqF (`Fin n) a b = eq# n a b
eqF (S `>< T) (as , at) (bs , bt) with eqF S as bs
... | QS , qs with decide QS
... | # 0 , x = Ff , \ ()
... | # 1 , x with qs x
... | r~ with eqF (T as) at bt
... | QT , qt = QT , \ x -> rf (as ,_) ~$~ qt x

rf# : (n : Nat)(i : Fin n) -> ElD (eq# n i i .fst)
rf# (su n) (# ze) = <>
rf# (su n) (# (su i) {l}) = rf# n (# i {l})

rfF : (X : UF)(x : ElF X) -> ElD (eqF X x x .fst)
rfF `1 <> = <>
rfF (`Fin n) i = rf# n i
rfF (S `>< T) (s , t) with eqF S s s | rfF S s
... | QS , qs | xs with decide QS
... | # 0 , x = contra QS x xs
... | # 1 , x with qs x
... | r~ with eqF (T s) t t | rfF (T s) t
... | QT , qt | xt = xt

finj : {n : Nat}(a b : Fin (n)) -> fs a ~ fs b -> a ~ b
finj a b r~ = r~

avoid : {n : Nat}(x : Fin (su n)) -> Fin n -> Fin (su n) >< \ y -> x ~ y -> Zero
avoid (# ze) (# y {l}) = # (su y) {l} , \ ()
avoid (# (su x)) (# ze) = # ze , \ ()
avoid {su n} (# (su x) {l}) (# (su y) {k}) = 
  let z , r = avoid (# x {l}) (# y {k})
  in  fs z , \ q -> r (finj _ _ q)

data FinQ : {n : Nat} -> Fin n -> Fin n -> Set where
  same# : {n : Nat}{x : Fin n} -> FinQ x x
  diff# : {n : Nat}{x : Fin (su n)}(y : Fin n) -> FinQ x (avoid x y .fst)

finQ : {n : Nat}(x y : Fin n) -> FinQ x y
finQ {su n} (# ze) (# ze) = same#
finQ {su n} (# ze) (# (su y)) = diff# (# y)
finQ {su (su n)} (# (su x)) (# ze) = diff# (# ze)
finQ {su (su n)} (# (su x) {k}) (# (su y) {l}) with finQ {su n} (# x {k}) (# y {l})
... | same# = same#
... | diff# z = diff# (fs z)

fstq : {S : Set}{T : S -> Set}{a b : S >< T} -> a ~ b -> a .fst ~ b .fst
fstq r~ = r~

sndq : {S : Set}{T : S -> Set}{s : S}{a b : T s} -> _~_ {S >< T} (s , a) (s , b) -> a ~ b
sndq r~ = r~

_-not_ : (X : UF)(x : ElF X) -> UF >< \ W -> ElF W -> ElF X >< \ y -> x ~ y -> Zero
`1 -not x = `0 , \ ()
`Fin (su n) -not x = `Fin n , avoid x
(S `>< T) -not (s , t) = 
  let R , rs = S -not s in let U , ut = T s -not t in
  ((R `>< \ r -> T (rs r .fst)) `+ U) , \
  { (# 0 , r , t) -> (rs r . fst , t) , (fstq - rs r .snd)
  ; (# 1 , u) -> (s , ut u .fst) , (sndq - ut u .snd)
  }

data UFQ (X : UF)(x : ElF X) : ElF X -> Set where
  same : UFQ X x x
  diff : (y : ElF ((X -not x) .fst)) -> UFQ X x ((X -not x) .snd y .fst)

ufQ : (X : UF)(x y : ElF X) -> UFQ X x y
ufQ `1 <> <> = same
ufQ (`Fin n) i j with finQ i j
... | same# = same
... | diff# y = diff y
ufQ (S `>< T) (xs , xt) (ys , yt) with ufQ S xs ys
... | diff y = diff (# 0 , y , yt)
... | same with ufQ (T xs) xt yt
... | diff y = diff (# 1 , y)
... | same = same

_`#*_ : (n : Nat)(T : Fin n -> UF) -> UF
ze `#* T = `1
su n `#* T = T (# 0) `* (n `#* (fs - T))

_`#>_ : (S : UF)(T : ElF S -> UF) -> UF
`0 `#> T = `1
`1 `#> T = T <>
`Fin n `#> T = n `#* T
(R `>< S) `#> T = R `#> \ r -> S r `#> \ s -> T (r , s) 

out# : (n : Nat){T : Fin n -> UF} -> ElF (n `#* T) -> n #* (T - ElF)
out# ze ts = < <> >
out# (su n) (t , ts) = < (t , out# n ts) >

out : {S : UF}{T : ElF S -> UF} -> ElF (S `#> T) -> S #> (T - ElF)
out {`0} {T} f = < <> >
out {`1} {T} t = < t >
out {`Fin n} {T} ts = \\ \ i -> out# n ts #$ i
out {R `>< S} {T} f = \\ \ (r , s) -> out {S r} (out {R} f $$ r) $$ s

inn# : (n : Nat){T : Fin n -> UF} -> n #* (T - ElF) -> ElF (n `#* T)
inn# ze ts = <>
inn# (su n) < t , ts > = t , inn# n ts

inn :  {S : UF}{T : ElF S -> UF} -> S #> (T - ElF) -> ElF (S `#> T)
inn {`0} {T} f = <>
inn {`1} {T} < t > = t
inn {`Fin n} {T} < ts > = inn# n ts
inn {R `>< S} {T} < f > = inn {R} (\\ \ r -> inn {S r} (\\ \ s -> f $$ r $$ s))

decideMu : (C : Ctn) -> (Mu C -> Zero) + Mu C
decideMu (S <! P) with decideF (S `>< \ s -> P s `#> \ p -> `0)
... | # 1 , s , k = # 1 , < s , (\\ \ p -> magic (out {P s} k $$ p)) >
... | # 0 , r = # 0 , (rec - loop) where
  loop : {x : (S <! P) <* Zero} -> Rec x -> Zero
  loop < s / k > with decideF (P s)
  ... | # 0 , b = magic (r (s , inn {P s} (\\ b)))
  ... | # 1 , p = loop (k p)

BTree : Ctn
BTree .Sh = `Fin 2
BTree .Po (# 0) = `0
BTree .Po (# 1) = `Fin 2

