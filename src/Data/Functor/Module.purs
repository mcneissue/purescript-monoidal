module Data.Functor.Module where

import Control.Category.Kinds (KHom)

class LeftModule :: ∀ l k1 ko.
  KHom ko
  -> (l -> k1 -> k1)
  -> (k1 -> ko)
  -> Constraint
class LeftModule cat t1 f
  where
  lstrength :: ∀ a x. cat (f a) (f (t1 x a))

class RightModule :: ∀ r k1 ko.
  KHom ko
  -> (k1 -> r -> k1)
  -> (k1 -> ko)
  -> Constraint
class RightModule cat t1 f
  where
  rstrength :: ∀ a x. cat (f a) (f (t1 a x))

class Bimodule :: ∀ k1 ko.
  KHom ko
  -> (k1 -> k1 -> k1)
  -> (k1 -> ko)
  -> Constraint
class (LeftModule cat t1 f, RightModule cat t1 f) <= Bimodule cat t1 f
