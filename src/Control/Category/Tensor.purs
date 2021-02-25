module Control.Category.Tensor where

import Prelude

import Data.Bifunctor (bimap)
import Data.Either (Either(..), either)
import Data.Either.Nested (type (\/))
import Data.Op (Op(..))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple (swap) as T
import Data.Tuple.Nested (type (/\), (/\))

type Iso p a b = { fwd :: p a b, bwd :: p b a }

flipIso :: ∀ a b. Iso (->) a b -> Iso Op a b
flipIso { fwd, bwd } = { fwd: Op bwd, bwd: Op fwd }

class (Category p, Category q) <= GBifunctor p q t
  where
  gbimap :: ∀ a b c d. p a b -> p c d -> q (t a c) (t b d)

class (Category p, GBifunctor p p t) <= Associative t p
  where
  assoc :: ∀ a b c. Iso p (t a (t b c)) (t (t a b) c)

instance gbifunctorFlip :: GBifunctor (->) (->) t => GBifunctor Op Op t
  where
  gbimap (Op f) (Op g) = Op $ gbimap f g

instance associativeFlip :: Associative t (->) => Associative t Op
  where
  assoc = flipIso assoc

instance gbifunctorTuple :: GBifunctor (->) (->) Tuple
  where
  gbimap = bimap

instance associativeTuple :: Associative Tuple (->)
  where
  assoc =
    { fwd: \(a /\ b /\ c) -> (a /\ b) /\ c
    , bwd: \((a /\ b) /\ c) -> a /\ b /\ c
    }

instance gbifunctorEither :: GBifunctor (->) (->) Either
  where
  gbimap = bimap

instance associativeEither :: Associative Either (->)
  where
  assoc =
    { fwd: either (Left <<< Left) (either (Left <<< Right) Right)
    , bwd: either (either Left (Right <<< Left)) (Right <<< Right)
    }

class Associative t p <= Tensor t i p | t -> i, i -> t
  where
  lunit :: ∀ a. Iso p (t i a) a
  runit :: ∀ a. Iso p (t a i) a

instance tensorFlip :: Tensor t i (->) => Tensor t i Op
  where
  lunit = flipIso lunit
  runit = flipIso runit

instance tensorTuple :: Tensor Tuple Unit (->)
  where
  lunit = { fwd: snd, bwd: Tuple unit }
  runit = { fwd: fst, bwd: flip Tuple unit }

instance tensorEither :: Tensor Either Void (->)
  where
  lunit = { fwd: either absurd identity, bwd: Right }
  runit = { fwd: either identity absurd, bwd: Left }

class Associative t p <= Symmetric t p
  where
  swap :: ∀ a b. p (t a b) (t b a)

instance symmetricFlip :: Symmetric t (->) => Symmetric t Op
  where
  swap = Op swap

instance symmetricTuple :: Symmetric Tuple (->)
  where
  swap = T.swap

instance symmetricEither :: Symmetric Either (->)
  where
  swap = either Right Left

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
