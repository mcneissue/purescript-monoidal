module Control.Category.Tensor where

import Prelude

import Data.Bifunctor (class Bifunctor)
import Data.Either (Either(..), either)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple (swap) as T
import Data.Tuple.Nested ((/\))

type Iso p a b = { fwd :: p a b, bwd :: p b a }

class (Bifunctor t, Category p) <= Associative t p
  where
  assoc :: forall a b c. Iso p (t a (t b c)) (t (t a b) c)

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

class Associative t p <= Tensor t i p | t -> i, i -> t
  where
  lunit :: forall a. Iso p (t i a) a
  runit :: forall a. Iso p (t a i) a

instance tensorTuple :: Tensor Tuple Unit (->)
  where
  lunit = { fwd: snd, bwd: Tuple unit }
  runit = { fwd: fst, bwd: flip Tuple unit }

instance tensorEither :: Tensor Either Void (->)
  where
  lunit = { fwd: either absurd identity, bwd: Right }
  runit = { fwd: either identity absurd, bwd: Left }

class (Bifunctor t, Category p) <= Symmetric t p
  where
  swap :: forall a b. p (t a b) (t b a)

instance symmetricTuple :: Symmetric Tuple (->)
  where
  swap = T.swap

instance symmetricEither :: Symmetric Either (->)
  where
  swap = either Right Left
