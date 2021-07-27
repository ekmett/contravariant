1.5.5 [2021.07.27]
------------------
* Fix the build on old GHCs using `transformers-0.6.*`.

1.5.4 [2021.07.25]
------------------
* Allow building with `transformers-0.6.*`.

1.5.3 [2020.12.30]
------------------
* Explicitly mark modules as `Safe`.

1.5.2 [2019.06.03]
------------------
* Mark `Data.Functor.Contravariant` and `Data.Functor.Contravariant.Generic`
  as unconditionally `Trustworthy`.

1.5.1 [2019.05.02]
------------------
* Remove the use of `unsafeCoerce` in `Data.Functor.Contravariant.Generic`. As
  a result, the `safe` flag has been removed, as it is no longer used.

1.5 [2018.07.01]
----------------
* Support building with GHC 8.6, where `Data.Functor.Contravariant` has been
  moved into `base`.

1.4.1 [2018.01.18]
------------------
* Add `Semigroup` and `Monoid` instances for `Predicate`.
* Add lots of documentation explaining `Contravariant`, `Divisible`, and
  `Decidable`.
* Fix some dodgy CPP usage that caused the build to fail on Eta.

1.4
---
* Improved the performance of `Deciding` at the cost of downgrading it to `Trustworthy`.
* Support for GHC 8
* Support for `transformers` 0.5

1.3.3
-----
* Add `instance Monoid m => Divisible (Const m)`

1.3.2
-----
* Add `($<)` operator

1.3.1.1
-------
* Fixed builds on GHC 7.2

1.3.1
-----
* Added `Data.Functor.Contravariant.Generic` on GHC 7.4+

1.3
---
* We've merged the `foreign-var` and `StateVar` packages. Transferring support to `StateVar`.

1.2.2.1
-------
* Fixed redundant import warnings on GHC 7.10.

1.2.2
-----
* Added `foreign-var` support.

1.2.1
-----
* Added `phantom` to `Data.Functor.Contravariant`. This combinator was formerly called `coerce` in the `lens` package, but
  GHC 7.8 added a `coerce` method to base with a different meaning.
* Added an unsupported `-f-semigroups` build flag that disables support for the `semigroups` package.
* Minor documentation improvements.

1.2.0.1
-----
* Fix build on GHC 7.0.4

1.2
-----
* Renamed `Data.Functor.Contravariant.Applicative` to `Data.Functor.Contravariant.Divisible`

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
