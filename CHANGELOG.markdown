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
