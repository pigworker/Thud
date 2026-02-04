module Basics where


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

fstq : {S : Set}{T : S -> Set}{a b : S >< T} -> a ~ b -> a .fst ~ b .fst
fstq r~ = r~

sndq : {S : Set}{T : S -> Set}{s : S}{a b : T s} -> _~_ {S >< T} (s , a) (s , b) -> a ~ b
sndq r~ = r~

