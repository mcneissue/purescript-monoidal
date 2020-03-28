module Data.Profunctor.Lazy where

import Data.Unit (Unit)

class Lazy p where
  defer :: forall x y. (Unit -> p x y) -> p x y
