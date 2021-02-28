module Data.Bifunctor.ApplicativeDo (module P, apply, pure) where

import Prelude

import Prelude (map) as P
import Data.Bifunctor.Monoidal (class Semigroupal, class Unital, combine, introduce)
import Data.Tuple (Tuple, uncurry)
import Data.Tuple.Nested ((/\))

apply :: ∀ t1 f x y a b. Semigroupal (->) t1 Tuple Tuple f => Functor (f (t1 x y)) => f x (a -> b) -> f y a -> f (t1 x y) b
apply ff fa = map (uncurry ($)) $ combine $ ff /\ fa

pure :: ∀ i1 f a. Unital (->) i1 Unit Unit f => Functor (f i1) => a -> f i1 a
pure a = map (\(_ :: Unit) -> a) $ introduce unit
