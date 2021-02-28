module Main where

import Prelude

import Data.Bifunctor.ApplicativeDo as F
import Data.Either (Either(..))
import Data.These (These)
import Effect (Effect)
import Effect.Class.Console (logShow)

infixl 6 type These as ⊠

type Result = Either (String ⊠ String ⊠ String) { v1 :: Int, v2 :: Int, v3 :: Int }

test1 :: Result
test1 = F.ado
  v1 <- Left "error 1"
  v2 <- Left "error 2"
  v3 <- Left "error 3"
  in { v1, v2, v3 }

test2 :: Result
test2 = F.ado
  v1 <- Right 1
  v2 <- Left "error 2"
  v3 <- Left "error 3"
  in { v1, v2, v3 }

test3 :: Result
test3 = F.ado
  v1 <- Right 1
  v2 <- Right 2
  v3 <- Right 3
  in { v1, v2, v3 }

main :: Effect Unit
main = do
  logShow $ test1
  logShow $ test2
  logShow $ test3
