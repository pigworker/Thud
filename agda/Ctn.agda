module Ctn where

open import Basics
open import UF

{- Containers with finite shapes and positions.
   Questions include whether we should allow shapes to be data, not just finite.
   At the moment, Ctn is not closed under the free monad construction.
   Fine for now, but maybe unpleasing.
-}
record Ctn : Set where
  constructor _<!_
  field
    Sh : UF
    Po : ElF Sh -> UF
  [!_!] : Set -> Set
  [!_!] X = ElF Sh >< \ s -> Po s #> \ _ -> X
open Ctn public

{- What are the morphisms? -}


{- Every container gives a free monad in Set.
   (If we allowed shapes to be data, we could have a free monad in *Ctn*.)
-}
data _<*_ (C : Ctn)(X : Set) : Set where
  -- one layer of C structure with subterms
  <_> : [! C !] (C <* X) -> C <* X
  -- a variable
  ! : X -> C <* X

{- The least fixpoint of C is the closed C terms. -}
Mu : Ctn -> Set
Mu C = C <* Zero

{- In order to compute with these things, we need the
   recursivity view.
-}

{- This thing encodes the context in which recIO, below,
   operates. See RecIn and RecOut for their meaning.
-}
data RecProb : Set where
  -- top level problem
  [] : RecProb
  -- problem family bleu
  _?-_ : (P : UF) -> (ElF P -> RecProb) -> RecProb
  -- problem family vert
  _?-'_ : (P : UF) -> (ElF P -> RecProb) -> RecProb

module _ {C : Ctn}{X : Set} where

  data Rec : C <* X -> Set where
    <_/_> : (s : ElF (Sh C)){k : Po C s #> \ _ -> C <* X}
            -> (r : (p : ElF (Po C s)) -> Rec (k $$ p))
            --      ^^^^^^^^^^^^^^^^^^ projection at a position
            -> Rec < s , k >
    ! : (x : X) -> Rec (! x)

  RecIn : RecProb -> Set
  RecIn []        = C <* X
  RecIn (P ?- K)  = P #> \ p -> RecIn (K p)
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

{- Now pick a C and let's get that free monad structure.
-}

module _ {C : Ctn} where

  module _ {X Y : Set}(f : X -> C <* Y) -- pick a Kleisli arrow
    where

    {- First, define Kleisli extension relationally. -}
    data Subst : C <* X -> C <* Y -> Set
      where

      <_/_> : (s : ElF (Sh C)){k : Po C s #> \ _ -> C <* X}
        {m : Po C s #> \ _ -> C <* Y}
        (r : (p : ElF (Po C s)) -> Subst (k $$ p) (m $$ p))
        --   ^^^^^^ access by projection!
        -> Subst < s , k > < s , m >

      ! : (x : X) -> Subst (! x) (f x)

    {- Next, show it's computable. -}
    subst : (t : C <* X) -> <: Subst t :>
    subst = rec - help where
      help : {t : C <* X} -> Rec t -> (C <* Y) >< Subst t
      help < s / r > =
        let j = \ p -> fst (help (r p)) in
        let jq = \ p -> snd (help (r p)) in

        < s , \\ j > ,
        < s / (\ p -> leib (_ < beta' (Po C s) j p ]~ _ [QED]) (Subst _) (jq p)) >
      help (! x) = f x , ! x

  _>>=_ : {X Y : Set}(t : C <* X)(f : X -> C <* Y) -> C <* Y
  t >>= f = fst (subst f t)

  -- >>= is functional!
  substFun : {X Y : Set}{f g : X -> C <* Y}(t : C <* X) ->
    (fg : (x : X) -> f x ~ g x) ->
    {u v : C <* Y} -> Subst f t u -> Subst g t v -> u ~ v
  substFun t q < s / r > < .s / u > = rf ((s ,_) - <_>)
    ~$~ extIn (\ _ -> r~) (\ _ -> r~) (\ p -> substFun _ q (r p) (u p))
  substFun t q (! x) (! .x) = q x

  -- we get one monad law for free (! x >>= k ~ k x)

  -- here's the other monad law for !
  substId : {X : Set}{f : X -> C <* X}(fi : (x : X) -> ! x ~ f x)
    -> {t u : C <* X} -> Subst f t u -> t ~ u
  substId fi < s / r > =
    rf ((s ,_) - <_>) ~$~ extIn (\ _ -> r~) (\ _ -> r~) (\ p -> substId fi (r p))
  substId fi (! x) = fi x

  -- and here's associativity
  substAsso : {X Y Z : Set}{f : X -> C <* Y}{g : Y -> C <* Z}{h : X -> C <* Z}
    -> ((x : X) -> Subst g (f x) (h x))
    -> {r : C <* X}{s : C <* Y}{t : C <* Z}
    -> Subst f r s -> Subst g s t -> Subst h r t
  substAsso q < s / i > < .s / j > = < s / (\ p -> substAsso q (i p) (j p)) >
  substAsso q (! x) st with r~ <- substFun _ (\ _ -> r~) st (q x) = ! x


