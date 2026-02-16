module Cata where

open import Basics
open import UF
open import Ctn


-- TEMPLATES FOR FOLDS
-- aka Kleisli arrows in the free monad monad
_-*>_ : Ctn -> Ctn -> Set
(S <! P) -*> C = S #> \ s -> C <* ElF (P s)
    -- for each input shape, say where in the output to slot the recursive output for each input position


module _ {C D : Ctn}(f : C -*> D){X : Set} where

  -- Morally, this is Kleisli extension for the free monad monad!

  -- First, define it relationally
  data Cata : C <* X -> D <* X -> Set where
    <_/_/_> : (s : ElF (Sh C)){k : Po C s #> \ _ -> C <* X}  -- shape and subterms
      {l : ElF (Po C s) -> D <* X} ->
      -- ^^^ our collection of recursively computed outputs for subterm in each position
      (r : (p : ElF (Po C s)) -> Cata (k $$ p) (l p)) ->
       --  ^^^^^^^^ projection-based access
      {t : D <* X} -> Subst l (f $$ s) t  -- substitute recursive output in template for given shape
      -> Cata < s , k > t
    ! : (x : X) -> Cata (! x) (! x)   -- variables stay put

  -- it's computable
  cataHelp : {x : C <* X}(r : Rec x) -> <: Cata x :>
  cataHelp < s / r > = _ , < s / (\ p -> snd (cataHelp (r p))) / snd (subst _ (f $$ s)) >
  cataHelp (! x) = _ , ! x

  cata : C <* X -> D <* X
  cata x = fst (cataHelp (rec x))

  -- it's functional
  cataFun : {x : C <* X}{y z : D <* X} -> Cata x y -> Cata x z -> y ~ z
  cataFun < s / r / x > < .s / t / y > =
    substFun _ (\ p -> cataFun (r p) (t p))
      x y
  cataFun (! x) (! .x) = r~

module _ {C : Ctn} where

  -- identity Kleisli arrows in the free monad monad

  id* : C -*> C
  id* = \\ \ s -> < s , \\ ! >

  idLem : (s : ElF (C .Sh)) ->  < s , \\ ! > ~ (id* $$ s)
  idLem s = < s , \\ ! > < beta' (C .Sh) (\ s -> < s , \\ ! >) s ]~ (id* $$ s) [QED]

  idCata : forall {X}(t : C <* X) -> Cata id* t t
  idCata {X} = rec - idCataHelp where
    idCataHelp : {t : C <* X} -> Rec t -> Cata id* t t
    idCataHelp (<_/_> s {k} r) =
      < s / (\ p -> idCataHelp (r p)) /
        leib (idLem s) (\ z -> Subst (\ z -> k $$ z) z < s , k >)
        < s / (\ p -> leib (_ < beta' (C .Po s) ! p ]~ _ [QED])
                      (\ a -> Subst (\ z -> k $$ z) a (k $$ p))
                      (! p)) >
        >
    idCataHelp (! x) = ! x

module _ {X Y : Set}{C D : Ctn}{f : X -> C <* Y}{g : C -*> D} where

  -- "bind" for the free monad monad

  substCata : {a : C <* X}{b : C <* Y} -> Subst f a b
           -> {d : D <* Y} -> Cata g b d
           -> {h : X -> D <* Y}
           -> (fh : (x : X) -> Cata g (f x) (h x))
           -> {c : D <* X} -> Cata g a c
           -> Subst h c d
  substCata < s / r0 > < .s / r1 / x1 > {h} fh {c} < .s / r2 / x2 >
    with e , q <- subst h c
    with v <- substAsso (\ p -> substCata (r0 p) (r1 p) fh (r2 p)) x2 q
    with r~ <- substFun _ (\ _ -> r~) x1 v
    = q
  substCata (! x) gbd fh (! .x) with r~ <- cataFun g (fh x) gbd = ! x

module _ {C D E : Ctn}(f : C -*> D)(g : D -*> E){X : Set} where

  -- Kleisli composition for the free monad monad

  _-then_ : C -*> E
  _-then_ = \\ \ cs -> cata g (f $$ cs)

  coCata : {c : C <* X}{d : D <* X}{e : E <* X}
    -> Cata f c d -> Cata g d e -> Cata _-then_ c e
  coCata (<_/_/_> s {k} {l} r x) d =
    let j = \ p -> cataHelp g (rec (l p)) in
    let c , m = cataHelp g (rec (f $$ s)) in
    < s / (\ p -> coCata (r p) (snd (j p))) /
      leib (c < beta' (C .Sh) ((f $$_) - cata g) s ]~
            ([ C .Sh ] [ C .Sh ]\ ((f $$_) - cata g) $ s)
            [QED])
        (\ t -> Subst _ t _) (substCata x d (j - snd) m)
      >
  coCata (! x) (! .x) = ! x
