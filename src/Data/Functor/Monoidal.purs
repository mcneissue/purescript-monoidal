module Data.Functor.Monoidal where

import Prelude

import Control.Alt (class Alt, alt)
import Control.Category.Tensor (class Associative, class Tensor)
import Control.Plus (class Plus, empty)
import Data.Either (Either(..))
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))

-- {{{ SEMIGROUPAL

class
  ( Associative t1 cat
  , Associative to cat
  ) <=
  Semigroupal cat t1 to f
  where
  combine :: ∀ x x'.
    cat
      (to
        (f     x   )
        (f       x'))
        (f (t1 x x'))

-- }}}

-- {{{ UNITAL

class Unital cat i1 io f
  where
  introduce :: cat io (f i1)

-- }}}

-- {{{ MONOIDAL

class
  ( Tensor t1 i1 cat
  , Tensor to io cat
  , Semigroupal cat t1 to f
  , Unital cat i1 io f
  ) <=
  Monoidal cat t1 i1 to io f

-- }}}

-- {{{ INSTANCES

instance semigroupalApply :: Apply f => Semigroupal (->) Tuple Tuple f
  where
  combine (fa /\ fb) = (/\) <$> fa <*> fb

instance unitalApplicative :: Applicative f => Unital (->) Unit Unit f
  where
  introduce = pure

instance monoidalApplicative :: Applicative f => Monoidal (->) Tuple Unit Tuple Unit f

instance semigroupalAlt :: Alt f => Semigroupal (->) Either Tuple f
 where
 combine (fa /\ fb) = alt (Left <$> fa) (Right <$> fb)

instance unitalPlus :: Plus f => Unital (->) Void Unit f
  where
  introduce = const empty

instance monoidalPlus :: Plus f => Monoidal (->) Either Void Tuple Unit f

-- }}}
