module Control.Category.Tensor where

import Prelude

import Data.Bifunctor (bimap)
import Data.Either (Either(..), either)
import Data.Either.Nested (type (\/))
import Data.Maybe (Maybe(..))
import Data.Op (Op(..))
import Data.Profunctor (arr)
import Data.Profunctor.Star (Star(..))
import Data.These (These(..))
import Data.These as These
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple (swap) as T
import Data.Tuple.Nested (type (/\), (/\))

-- {{{ GBIFUNCTOR

class (Category p, Category q) <= GBifunctor p q r t | t r -> p q
  where
  gbimap :: ∀ a b c d. p a b -> q c d -> r (t a c) (t b d)

grmap :: ∀ p q r t a b b'. GBifunctor p q r t => q b b' -> r (t a b) (t a b')
grmap = gbimap identity

glmap :: ∀ p q r t a a' b. GBifunctor p q r t => p a a' -> r (t a b) (t a' b)
glmap = flip gbimap identity

instance gbifunctorFlip :: GBifunctor (->) (->) (->) t => GBifunctor Op Op Op t
  where
  gbimap (Op f) (Op g) = Op $ gbimap f g

instance gbifunctorTuple :: GBifunctor (->) (->) (->) Tuple
  where
  gbimap = bimap

instance gbifunctorEither :: GBifunctor (->) (->) (->) Either
  where
  gbimap = bimap

instance gbifunctorThese :: GBifunctor (->) (->) (->) These
  where
  gbimap = bimap

instance gbifunctorThesePointed :: GBifunctor (Star Maybe) (Star Maybe) (Star Maybe) These
  where
  gbimap (Star f) (Star g) = Star $ bimap f g >>> These.these (map This) (map That) These.maybeThese

-- }}}

type Iso p a b = { fwd :: p a b, bwd :: p b a }

flipIso :: ∀ a b. Iso (->) a b -> Iso Op a b
flipIso { fwd, bwd } = { fwd: Op bwd, bwd: Op fwd }

-- {{{ ASSOCIATIVE

class (Category p, GBifunctor p p p t) <= Associative t p
  where
  assoc :: ∀ a b c. Iso p (t a (t b c)) (t (t a b) c)

instance associativeFlip :: Associative t (->) => Associative t Op
  where
  assoc = flipIso assoc

instance associativeStar ::
  ( Monad m
  , Associative t (->)
  , GBifunctor (Star m) (Star m) (Star m) t
  ) =>
  Associative t (Star m)
  where
  assoc = let { fwd, bwd } = assoc in { fwd: arr fwd, bwd: arr bwd }

instance associativeTuple :: Associative Tuple (->)
  where
  assoc =
    { fwd: \(a /\ b /\ c) -> (a /\ b) /\ c
    , bwd: \((a /\ b) /\ c) -> a /\ b /\ c
    }

instance associativeEither :: Associative Either (->)
  where
  assoc =
    { fwd: either (Left <<< Left) (either (Left <<< Right) Right)
    , bwd: either (either Left (Right <<< Left)) (Right <<< Right)
    }

instance associativeThese :: Associative These (->)
  where
  assoc = { fwd, bwd }
    where
    fwd = These.these (This >>> This) (glmap That) (Both >>> glmap)
    bwd = These.these (grmap This) (That >>> That) (flip $ flip Both >>> grmap)


-- }}}

-- {{{ TENSOR

class Associative t p <= Tensor t i p | t -> i
  where
  lunit :: ∀ a. Iso p (t i a) a
  runit :: ∀ a. Iso p (t a i) a

instance tensorFlip :: Tensor t i (->) => Tensor t i Op
  where
  lunit = flipIso lunit
  runit = flipIso runit

instance tensorStar :: (Monad m, Tensor t i (->), Associative t (Star m)) => Tensor t i (Star m)
  where
  lunit = let { fwd, bwd } = lunit in { fwd: arr fwd, bwd: arr bwd }
  runit = let { fwd, bwd } = runit in { fwd: arr fwd, bwd: arr bwd }

instance tensorTuple :: Tensor Tuple Unit (->)
  where
  lunit = { fwd: snd, bwd: Tuple unit }
  runit = { fwd: fst, bwd: flip Tuple unit }

instance tensorEither :: Tensor Either Void (->)
  where
  lunit = { fwd: either absurd identity, bwd: Right }
  runit = { fwd: either identity absurd, bwd: Left }

instance tensorThese :: Tensor These Void (->)
  where
  lunit = { fwd, bwd }
    where
    fwd = These.these absurd identity absurd
    bwd = That

  runit = { fwd, bwd }
    where
    fwd = These.these identity absurd (flip absurd)
    bwd = This

-- }}}

-- {{{ SYMMETRIC

class Associative t p <= Symmetric t p
  where
  swap :: ∀ a b. p (t a b) (t b a)

instance symmetricFlip :: Symmetric t (->) => Symmetric t Op
  where
  swap = Op swap

instance symmetricStar :: (Monad m, Symmetric t (->), Associative t (Star m)) => Symmetric t (Star m)
  where
  swap = arr swap

instance symmetricTuple :: Symmetric Tuple (->)
  where
  swap = T.swap

instance symmetricEither :: Symmetric Either (->)
  where
  swap = either Right Left

instance symmetricThese :: Symmetric These (->)
  where
  swap = These.these That This (flip Both)

-- }}}

-- {{{ CARTESIAN

class (Symmetric t p, Tensor t i p) <= Cartesian t i p | i -> t, t -> i
  where
  diagonal :: ∀ a. p a (t a a)
  terminal :: ∀ a. p a i

dup :: ∀ a. a -> a /\ a
dup a = a /\ a

instance cartesianTuple :: Cartesian Tuple Unit (->)
  where
  diagonal = dup
  terminal = const unit

merge :: ∀ a. a \/ a -> a
merge = either identity identity

instance cartesianEither :: Cartesian Either Void Op
  where
  diagonal = Op $ merge
  terminal = Op $ absurd

instance cartesianThese :: Cartesian These Void (Star Maybe)
  where
  diagonal = arr $ join Both
  terminal = Star $ const Nothing

-- }}}
