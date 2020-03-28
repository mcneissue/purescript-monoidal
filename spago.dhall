{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "profunctor-extra"
, dependencies = [ "profunctor", "either", "tuples", "effect" ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
