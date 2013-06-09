0.4.1
-----
* Added `Day` convolution under `Data.Functor.Contravariant.Day`.

0.3
---
* Added `Backwards` and `Reverse` instances for `transformers` 0.3
* Added `instance (Functor f, Contravariant g) => Contravariant (Compose f g)`. (This is non-canonical, but is necessary to support other packages.)
* Added `Functor` instances to `ComposeFC` and `ComposeCF` for use when modeling phantom type parameters caused mixing `Functor` + `Contravariant`.
