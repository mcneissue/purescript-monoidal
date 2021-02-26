module Data.Bifunctor.Monoidal.Specialized where

import Prelude hiding ((&&),(||))

import Control.Category.Tensor (dup, merge)
import Data.Bifunctor.Monoidal (class Semigroupal, class Unital, combine, introduce)
import Data.Either (Either(..))
import Data.Either.Nested (type (\/))
import Data.Maybe (Maybe, maybe)
import Data.Newtype (un)
import Data.Op (Op(..))
import Data.Profunctor (class Profunctor, dimap, lcmap, rmap)
import Data.Profunctor.Strong (class Strong, first)
import Data.Tuple (Tuple, curry, snd)
import Data.Tuple.Nested (type (/\), (/\))

-- Mux     = (×) (×) (×)
-- Demux   = (+) (+) (×)
-- Switch  = (×) (+) (×)
-- Splice  = (+) (×) (×)
-- Diverge = (+) (+) (+)
-- Trivial = (×) (+) (+)

-- Mux
mux :: ∀ p a b c d. Semigroupal (->) Tuple Tuple Tuple p => p a b -> p c d -> p (a /\ c) (b /\ d)
mux = curry combine

infixr 5 mux as &&

zip :: ∀ p x a b. Profunctor p => Semigroupal (->) Tuple Tuple Tuple p => p x a -> p x b -> p x (a /\ b)
zip x y = lcmap dup $ x && y

-- Demux
demux :: ∀ p a b c d. Semigroupal (->) Either Either Tuple p => p a b -> p c d -> p (a \/ c) (b \/ d)
demux = curry combine

infixr 4 demux as ||

fanin :: ∀ p x a b. Profunctor p => Semigroupal (->) Either Either Tuple p => p a x -> p b x -> p (a \/ b) x
fanin x y = rmap merge $ x || y

-- Switch
switch :: ∀ p a b c d. Semigroupal (->) Tuple Either Tuple p => p a b -> p c d -> p (a /\ c) (b \/ d)
switch = curry combine

infixr 5 switch as &|

union :: ∀ p x a b. Profunctor p => Semigroupal (->) Tuple Either Tuple p => p x a -> p x b -> p x (a \/ b)
union x y = lcmap dup $ x &| y

divide :: ∀ p x a b. Profunctor p => Semigroupal (->) Tuple Either Tuple p => p a x -> p b x -> p (a /\ b) x
divide x y = rmap merge $ x &| y

-- Splice
splice :: ∀ p a b c d. Semigroupal (->) Either Tuple Tuple p => p a b -> p c d -> p (a \/ c) (b /\ d)
splice = curry combine

infixr 5 splice as |&

-- Diverge
diverge :: ∀ p a b c d. Semigroupal (->) Either Either Either p => p a b \/ p c d -> p (a \/ c) (b \/ d)
diverge = combine

contramapMaybe :: ∀ p a b x. Profunctor p => Semigroupal (->) Either Either Either p => (a -> Maybe b) -> p b x -> p a x
contramapMaybe f = dimap (maybe (Right unit) Left <<< f) merge <<< ultraleft

-- {{{ ULTRA STRENGTHS

-- NB: The thing to notice about these is that in a profunctor, there is a "trivially monoidal" tensor on each source category
-- On the contravariant end, this is the (/\) tensor, on the covariant end it is the (\/) tensor. When we take the output tensor
-- to be (\/), we can pick the source tensors in two ways such that precisely one is trivial and one is not. Doing this twice lets
-- us "dodge" a quantified variable past the variables of an actual `p a b`, so that you get a `p a b -> p (t1 a x) (t2 b x)`, i.e.
-- a strength.

zig :: ∀ p t a b x. Profunctor p => Semigroupal (->) Tuple t Either p => p x a \/ p x b -> p x (t a b)
zig = lcmap dup <<< combine

zag :: ∀ p t a b x. Profunctor p => Semigroupal (->) t Either Either p => p a x \/ p b x -> p (t a b) x
zag = rmap merge <<< combine

ultrafirst :: ∀ p a b x y.
  Profunctor p =>
  Semigroupal (->) Tuple Tuple  Either p =>
  p a b -> p (a /\ x) (b /\ y)
ultrafirst = zag <<< Left <<< zig <<< Left

ultrasecond :: ∀ p a b x y.
  Profunctor p =>
  Semigroupal (->) Tuple Tuple  Either p =>
  p a b -> p (x /\ a) (y /\ b)
ultrasecond = zag <<< Right <<< zig <<< Right

ultraleft :: ∀ p a b x y.
  Profunctor p =>
  Semigroupal (->) Either Either Either p =>
  p a b -> p (a \/ x) (b \/ y)
ultraleft = zag <<< Left <<< zig <<< Left

ultraright :: ∀ p a b x y.
  Profunctor p =>
  Semigroupal (->) Either Either Either p =>
  p a b -> p (x \/ a) (y \/ b)
ultraright = zag <<< Right <<< zig <<< Right

-- }}}

-- Comux
comux :: ∀ p a b c d. Semigroupal Op Tuple Tuple Tuple p => p (a /\ c) (b /\ d) -> p a b /\ p c d
comux = un Op combine

undivide :: ∀ p x a b. Profunctor p => Semigroupal Op Tuple Tuple Tuple p => p (a /\ b) x -> p a x /\ p b x
undivide = comux <<< rmap dup

-- Codemux
codemux :: ∀ p a b c d. Semigroupal Op Either Either Tuple p => p (a \/ c) (b \/ d) -> p a b /\ p c d
codemux = un Op combine

partition :: ∀ p x a b. Profunctor p => Semigroupal Op Either Either Tuple p => p x (a \/ b) -> p x a /\ p x b
partition = codemux <<< lcmap merge

-- Coswitch
coswitch :: ∀ p a b c d. Semigroupal Op Either Tuple Tuple p => p (a \/ c) (b /\ d) -> p a b /\ p c d
coswitch = un Op combine

unfanin :: ∀ p x a b. Profunctor p => Semigroupal Op Either Tuple Tuple p => p (a \/ b) x -> p a x /\ p b x
unfanin = coswitch <<< rmap dup

unzip :: ∀ p x a b. Profunctor p => Semigroupal Op Either Tuple Tuple p => p x (a /\ b) -> p x a /\ p x b
unzip = coswitch <<< lcmap merge

-- Cosplice
cosplice :: ∀ p a b c d. Semigroupal Op Tuple Either Tuple p => p (a /\ c) (b \/ d) -> p a b /\ p c d
cosplice = un Op combine

terminal :: ∀ p a. Profunctor p => Unital (->) Unit Unit Unit p => p a Unit
terminal = lcmap (const unit) $ introduce unit

ppure :: ∀ p a. Profunctor p => Unital (->) Unit Unit Unit p => Strong p => p a a
ppure = dimap (unit /\ _) snd $ first $ (introduce unit :: p Unit Unit)

initial :: ∀ p a. Profunctor p => Unital (->) Void Void Unit p => p Void a
initial = rmap absurd $ introduce unit

poly :: ∀ p a b. Profunctor p => Unital (->) Unit Void Unit p => p a b
poly = dimap (const unit) absurd $ introduce unit

mono :: ∀ p. Unital (->) Void Unit Unit p => p Void Unit
mono = introduce unit

