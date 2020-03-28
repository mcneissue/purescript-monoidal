module Control.Category.Tensor where

import Prelude

import Data.Bifunctor (class Bifunctor)
import Data.Either (Either(..), either)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple.Nested ((/\))

type Iso p a b = { fwd :: p a b, bwd :: p b a }

class (Bifunctor t, Category p) <= Associative t p
  where
  assoc :: forall a b c. Iso p (t a (t b c)) (t (t a b) c)

instance associativeCartesian :: Associative Tuple (->)
  where
  assoc =
    { fwd: \(a /\ b /\ c) -> (a /\ b) /\ c
    , bwd: \((a /\ b) /\ c) -> a /\ b /\ c
    }

instance associativeCocartesian :: Associative Either (->)
  where
  assoc =
    { fwd: either (Left <<< Left) (either (Left <<< Right) Right)
    , bwd: either (either Left (Right <<< Left)) (Right <<< Right)
    }

class Associative t p <= Tensor t i p | t -> i, i -> t
  where
  lunit :: forall a. Iso p (t i a) a
  runit :: forall a. Iso p (t a i) a

instance tensorCartesian :: Tensor Tuple Unit (->)
  where
  lunit = { fwd: snd, bwd: Tuple unit }
  runit = { fwd: fst, bwd: flip Tuple unit }

instance tensorCocartesian :: Tensor Either Void (->)
  where
  lunit = { fwd: either absurd identity, bwd: Right }
  runit = { fwd: either identity absurd, bwd: Left }
