module Data.Trifunctor.ApplicativeDo (module P, apply, pure) where

import Prelude

import Prelude (map) as P
import Data.Trifunctor.Monoidal (class Semigroupal, class Unital, combine, introduce)
import Data.Tuple (Tuple, uncurry)
import Data.Tuple.Nested ((/\))

apply :: ∀ t1 t2 f a1 b1 a2 b2 a b. Semigroupal (->) t1 t2 Tuple Tuple f => Functor (f (t1 a1 b1) (t2 a2 b2)) => f a1 a2 (a -> b) -> f b1 b2 a -> f (t1 a1 b1) (t2 a2 b2) b
apply ff fa = map (uncurry ($)) $ combine $ ff /\ fa

pure :: ∀ i1 i2 f a. Unital (->) i1 i2 Unit Unit f => Functor (f i1 i2) => a -> f i1 i2 a
pure a = map (\(_ :: Unit) -> a) $ introduce unit
