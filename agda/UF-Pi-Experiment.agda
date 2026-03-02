module UF-Pi-Experiment where

{-
Exploring the blind alley of making a code for Pi in UF...

It's a bad idea, because it forces us to explain how to
construct functions from function spaces by *iterated*
currying.

We could index UF by *order* (in the sense of higher-order
functions) and observe that currying decreases order,
but it doesn't really buy us any convenience.

Mostly, this file exists to remind us what to say when
people ask us why there isn't a code for Pi in UF.
-}

open import Basics

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


data UF : Set
ElF : UF -> Set
_#>_ : (S : UF) -> (ElF S -> Set) -> Set

data UF where
  `0 `1 : UF
  `Fin : Nat -> UF
  _`><_ _`->_ : (S : UF)(T : ElF S -> UF) -> UF

ElF `0 = Zero
ElF `1 = One
ElF (`Fin n) = Fin n
ElF (S `>< T) = ElF S >< \ s -> ElF (T s)
ElF (S `-> T) = S #> \ s -> ElF (T s)

`0 #> T = One
`1 #> T = T <>
`Fin n #> T = n #* T
(R `>< S) #> T = R #> \ r -> S r #> \ s -> T (r , s)
(R `-> S) #> T = {!!}
-- this is why we *compute* Pi

