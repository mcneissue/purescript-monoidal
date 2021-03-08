module Data.Bifunctor.Module where

import Control.Category.Kinds (KHom)

class RightModule :: ∀ r k1 k2 ko.
  KHom ko
  -> (k1 -> r -> k1)
  -> (k2 -> r -> k2)
  -> (k1 -> k2 -> ko)
  -> Constraint
class RightModule cat t1 t2 f
  where
  lstrength :: ∀ a b x. cat (f a b) (f (t1 a x) (t2 b x))

class LeftModule :: ∀ l k1 k2 ko.
  KHom ko
  -> (l -> k1 -> k1)
  -> (l -> k2 -> k2)
  -> (k1 -> k2 -> ko)
  -> Constraint
class LeftModule cat t1 t2 f
  where
  rstrength :: ∀ a b x. cat (f a b) (f (t1 x a) (t2 x b))

class Bimodule :: ∀ k1 k2.
  KHom k2
  -> (k1 -> k1 -> k1)
  -> (k1 -> k1 -> k1)
  -> (k1 -> k1 -> k2)
  -> Constraint
class (LeftModule cat t1 t2 f, RightModule cat t1 t2 f) <= Bimodule cat t1 t2 f
