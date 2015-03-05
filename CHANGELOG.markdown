1.2.1
-----
* Added `phantom` to `Data.Functor.Contravariant`. This combinator was formerly called `coerce` in the `lens` package, but
  GHC 7.8 added a `coerce` method to base with a different meaning.

1.2.0.1
-----
* Fix build on GHC 7.0.4

1.1.1
-----
* Added `Data.Functor.Contravariant.Applicative`

1.0
---
* Removed `Day` convolution. The right adjoint of Day convolution is in `kan-extensions` as the right Kan lift. Moving these there to avoid forcing orphan instances. It also rather dramatically reduces the number of extensions required.
* This requires a first digit bump as it breaks several of my own packages.

0.6.1.1
-------
* Fixed issue with needing `KindSignatures` on older GHCs

0.6.1
-----
* Added covariant `Day` convolution. It isn't contravariant, but it is inspired by the contravariant construction.

0.5.1
-----
* `transformers` 0.4 compatibility

0.5
---
* Added `(>$)`
* Added instances for `GHC.Generics`

0.4.4
-----
* Fixed compatibility with GHC 7.7 and tightened `Safe` Haskell support.

0.4.1
-----
* Added `Day` convolution under `Data.Functor.Contravariant.Day`.

0.3
---
* Added `Backwards` and `Reverse` instances for `transformers` 0.3
* Added `instance (Functor f, Contravariant g) => Contravariant (Compose f g)`. (This is non-canonical, but is necessary to support other packages.)
* Added `Functor` instances to `ComposeFC` and `ComposeCF` for use when modeling phantom type parameters caused mixing `Functor` + `Contravariant`.
