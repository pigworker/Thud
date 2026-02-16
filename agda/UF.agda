module UF where

open import Basics

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

-- bleu et vert for vectors
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

extIn# : {n : Nat}{P : Fin n -> Set}{f f' : n #* P}{g g' : (i : Fin n) -> P i}
  -> f #$~ g -> f' #$~ g' -> ((i : Fin n) -> g i ~ g' i)
  -> f ~ f'
extIn#' : (n : Nat){P : Fin n -> Set}{f f' : n #*' P}{g g' : (i : Fin n) -> P i}
  -> (forall i -> (#[ n ] f $ i)  ~ g i)
  -> (forall i -> (#[ n ] f' $ i)  ~ g' i)
  -> ((i : Fin n) -> g i ~ g' i)
  -> f ~ f'
extIn# {n} {f = < f >}{< f' >} a b q = rf <_> ~$~ extIn#' n a b q
extIn#' ze a b q = r~
extIn#' (su n) a b q =
  rf _,_
  ~$~ (_ ~[ a (# 0) > _ ~[ q (# 0) > _ < b (# 0) ]~ _ [QED])
  ~$~ extIn# (fs - a) (fs - b) (fs - q)

data _#>_ (S : UF)(T : ElF S -> Set) : Set   -- bleu
_#>'_ : (S : UF)(T : ElF S -> Set) -> Set    -- et vert

data _#>_ S T where  -- bleu is a rigid type constructor
  -- bleu wraps vert
  <_> : S #>' T -> S #> T

-- vert computes compounds with bleu components
`0        #>' T = One
`1        #>' T = T <>
`Fin n    #>' T = n #* T
(R `>< S) #>' T = R #> \ r -> S r #> \ s -> T (r , s)

-- bleu lambda needs no type annotation
\\ : {S : UF}{T : ElF S -> Set} -> ((s : ElF S) -> T s) -> S #> T
-- vert lambda must have an explicit domain
[_]\ : (S : UF){T : ElF S -> Set} -> ((s : ElF S) -> T s) -> S #>' T
\\ {S} f = < [ S ]\ f >
[ `0 ]\ f = <>
[ `1 ]\ f = f <>
[ `Fin n ]\ f = #\ f 
[ R `>< S ]\ f = <( [ R ]\ \ r -> \\ \ s -> f (r , s) )>

-- likewise bleu application
_$$_ : {S : UF}{T : ElF S -> Set} -> S #> T -> ((s : ElF S) -> T s)
-- likewise vert application
[_]_$_ : (S : UF){T : ElF S -> Set} -> S #>' T -> ((s : ElF S) -> T s)
_$$_ {S} < f > s = [ S ] f $ s
[ `1 ] t $ <> = t
[ `Fin n ] f $ s = f #$ s
[ R `>< S ] f $ (r , s) = f $$ r $$ s

infixl 50 _$$_

-- tabulation, the relation
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

{- Suppose f tabulates g and f' tabulates g'.
   If g and g' agree *pointwise*, then f and f' agree *exactly*.
-}
extIn : {S : UF}{T : ElF S -> Set}{f f' : S #> T}{g g' : (s : ElF S) -> T s}
  -> f $~ g -> f' $~ g' -> ((s : ElF S) -> g s ~ g' s)
  -> f ~ f'
extIn' : (S : UF){T : ElF S -> Set}{f f' : S #>' T}{g g' : (s : ElF S) -> T s}
  -> ((s : ElF S) → ([ S ] f $ s) ~ g s)
  -> ((s : ElF S) → ([ S ] f' $ s) ~ g' s)
  -> ((s : ElF S) -> g s ~ g' s)
  -> f ~ f'
extIn {S} {f = < f >} {< f' >} a b q = rf <_> ~$~ extIn' S a b q
extIn' `0 a b q = r~
extIn' `1 a b q with r~ <- a <> | r~ <- b <> = q <>
extIn' (`Fin n) a b q = extIn# a b q
extIn' (S `>< T) {f = f}{f'}{g}{g'} a b q =
  extIn {S} {g = f $$_}{f' $$_} (\ _ -> r~) (\ _ -> r~)
    \ s -> extIn {T s} {g = (s ,_) - g}{(s ,_) - g'}
             ((s ,_) - a) ((s ,_) - b) ((s ,_) - q)

-- the internal versions

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


-- TODO: prove inn and out are mutually inverse
