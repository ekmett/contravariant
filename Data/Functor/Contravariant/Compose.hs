-- |
-- Module      :  Data.Functor.Contravariant.Compose
-- Copyright   :  (c) Edward Kmett 2010
-- License     :  BSD3
--
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Composition of contravariant functors.

module Data.Functor.Contravariant.Compose 
  ( Compose(..)
  , ComposeFC(..)
  , ComposeCF(..)
  ) where

import Data.Functor.Contravariant

-- | Composition of two contravariant functors
newtype Compose f g a = Compose { getCompose :: f (g a) }

instance (Contravariant f, Contravariant g) => Functor (Compose f g) where
    fmap f (Compose x) = Compose (contramap (contramap f) x)

-- | Composition of covariant and contravariant functors
newtype ComposeFC f g a = ComposeFC { getComposeFC :: f (g a) } 

instance (Functor f, Contravariant g) => Contravariant (ComposeFC f g) where
    contramap f (ComposeFC x) = ComposeFC (fmap (contramap f) x)

-- | Composition of contravariant and covariant functors
newtype ComposeCF f g a = ComposeCF { getComposeCF :: f (g a) } 

instance (Contravariant f, Functor g) => Contravariant (ComposeCF f g) where
    contramap f (ComposeCF x) = ComposeCF (contramap (fmap f) x)

