{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "monoidal"
, dependencies = [ "profunctor", "either", "tuples", "effect" ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
, license = "MIT"
, repository = "https://github.com/mcneissue/purescript-monoidal"
}

