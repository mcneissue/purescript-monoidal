{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "monoidal"
, dependencies =
  [ "profunctor"
  , "either"
  , "tuples"
  , "these"
  , "bifunctors"
  , "contravariant"
  , "control"
  , "functors"
  , "maybe"
  , "newtype"
  , "prelude"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "MIT"
, repository = "https://github.com/mcneissue/purescript-monoidal"
}

