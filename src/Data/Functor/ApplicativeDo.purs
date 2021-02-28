module Data.Functor.ApplicativeDo (module P, apply, pure) where

import Prelude

import Prelude (map) as P
import Data.Functor.Monoidal (class Semigroupal, class Unital, combine, introduce)
import Data.Tuple (Tuple, uncurry)
import Data.Tuple.Nested ((/\))

apply :: ∀ f a b. Semigroupal (->) Tuple Tuple f => Functor f => f (a -> b) -> f a -> f b
apply ff fa = map (uncurry ($)) $ combine $ ff /\ fa

pure :: ∀ f a. Unital (->) Unit Unit f => Functor f => a -> f a
pure a = map (\(_ :: Unit) -> a) $ introduce unit
