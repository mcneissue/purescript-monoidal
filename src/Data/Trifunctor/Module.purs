module Data.Trifunctor.Module where

import Control.Category.Kinds (KHom)

class LeftModule :: ∀ l k1 k2 k3 ko.
  KHom ko
  -> (l -> k1 -> k1)
  -> (l -> k2 -> k2)
  -> (l -> k3 -> k3)
  -> (k1 -> k2 -> k3 -> ko)
  -> Constraint
class LeftModule cat t1 t2 t3 f
  where
  lstrength :: ∀ a b c x. cat (f a b c) (f (t1 x a) (t2 x b) (t3 x c))

class RightModule :: ∀ r k1 k2 k3 ko.
  KHom ko
  -> (k1 -> r -> k1)
  -> (k2 -> r -> k2)
  -> (k3 -> r -> k3)
  -> (k1 -> k2 -> k3 -> ko)
  -> Constraint
class RightModule cat t1 t2 t3 f
  where
  rstrength :: ∀ a b c x. cat (f a b c) (f (t1 a x) (t2 b x) (t3 c x))

class Bimodule :: ∀ ko k1.
  KHom ko
  -> (k1 -> k1 -> k1)
  -> (k1 -> k1 -> k1)
  -> (k1 -> k1 -> k1)
  -> (k1 -> k1 -> k1 -> ko)
  -> Constraint
class (LeftModule cat t1 t2 t3 f, RightModule cat t1 t2 t3 f) <= Bimodule cat t1 t2 t3 f
