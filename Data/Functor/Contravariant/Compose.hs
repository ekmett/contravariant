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
  ) where

import Data.Functor.Contravariant

-- | A Contravariant functor composed with another functor type
newtype Compose f g a = Compose { getCompose :: f (g a) }

instance (Contravariant f, Contravariant g) => Functor (Compose f g) where
    fmap f (Compose x) = Compose (contramap (contramap f) x)

instance (Contravariant f, Functor g) => Contravariant (Compose f g) where
    contramap f (Compose x) = Compose (contramap (fmap f) x)

