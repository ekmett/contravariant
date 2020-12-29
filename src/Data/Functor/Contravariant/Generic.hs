{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Safe #-}
#elif __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
#if __GLASGOW_HASKELL__ >= 706
{-# LANGUAGE PolyKinds #-}
#endif
{-# LANGUAGE TypeFamilies #-}
#if __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE EmptyCase #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Contravariant.Generic
-- Copyright   :  (C) 2007-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  ConstraintKinds
--
--
--
----------------------------------------------------------------------------

module Data.Functor.Contravariant.Generic
  ( Deciding(..)
  , Deciding1(..)
  ) where

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import GHC.Generics

-- | This provides machinery for deconstructing an arbitrary 'Generic' instance using a 'Decidable' 'Contravariant' functor.
--
-- /Examples:/
--
-- @
-- gcompare :: 'Deciding' 'Ord' a => a -> a -> 'Ordering'
-- gcompare = 'getComparison' $ 'deciding' (Proxy :: Proxy 'Ord') ('Comparison' 'compare')
-- @
--
-- @
-- geq :: 'Deciding' 'Eq' a => a -> a -> 'Bool'
-- geq = 'getEquivalence' $ 'deciding' (Proxy :: Proxy 'Eq') ('Equivalence' ('=='))
-- @
class (Generic a, GDeciding q (Rep' a)) => Deciding q a where
#ifndef HLINT
  deciding :: Decidable f => p q -> (forall b. q b => f b) -> f a
#endif

instance (Generic a, GG (Rep a), GDeciding q (Rep' a)) => Deciding q a  where
  deciding p q = contramap (swizzle . from) $ gdeciding p q

type Rep' a = Swizzle (Rep a)
type Rep1' f = Swizzle (Rep1 f)
type family Swizzle (r :: * -> *) :: * -> *
type instance Swizzle (M1 i c f) = M1 i c (Swizzle f)
type instance Swizzle V1 = V1
type instance Swizzle U1 = U1
type instance Swizzle Par1 = Par1
type instance Swizzle (Rec1 f) = Rec1 f
type instance Swizzle (K1 i c) = K1 i c
type instance Swizzle (f :+: g) = Swizzle f ::+: Swizzle g
type instance Swizzle (f :*: g) = Swizzle f ::*: Swizzle g
type instance Swizzle (f :.: g) = f :.: Swizzle g

newtype (::+:) f g a = Sum {unSum :: Either (f a) (g a)}
newtype (::*:) f g a = Prod {unProd :: (f a, g a)}

class GG r where
  swizzle :: r p -> Swizzle r p
instance GG f => GG (M1 i c f) where
  swizzle (M1 a) = M1 (swizzle a)
instance GG V1 where swizzle v = v
instance GG U1 where swizzle v = v
instance GG (K1 i c) where swizzle v = v
instance GG Par1 where swizzle v = v
instance GG (Rec1 f) where swizzle v = v
instance (GG f, GG g) => GG (f :+: g) where
  {-# INLINE swizzle #-}
  swizzle (L1 x) = Sum (Left (swizzle x))
  swizzle (R1 x) = Sum (Right (swizzle x))
instance (GG f, GG g) => GG (f :*: g) where
  {-# INLINE swizzle #-}
  swizzle (x :*: y) = Prod (swizzle x, swizzle y)
{-
-- This instance wouldn't be that efficient. But we don't
-- offer instances for compositions anyway.
instance (Functor f, GG g) => GG (f :.: g) where
  swizzle (Comp1 x) = Comp1 (fmap swizzle x)
-}

-- | This provides machinery for deconstructing an arbitrary 'Generic1' instance using a 'Decidable' 'Contravariant' functor.
--
-- /Examples:/
--
-- @
-- gcompare1 :: 'Deciding1' 'Ord' f => (a -> a -> 'Ordering') -> f a -> f a -> 'Ordering'
-- gcompare1 f = 'getComparison' $ 'deciding1' (Proxy :: Proxy 'Ord') ('Comparison' compare) ('Comparison' f)
-- @
--
-- @
-- geq1 :: 'Deciding1' 'Eq' f => (a -> a -> 'Bool') -> f a -> f a -> 'Bool'
-- geq1 f = 'getEquivalence' $ 'deciding1' (Proxy :: Proxy 'Eq') ('Equivalence' ('==')) ('Equivalence' f)
-- @
class (Generic1 t, GDeciding1 q (Rep1' t)) => Deciding1 q t where
#ifndef HLINT
  deciding1 :: Decidable f => p q -> (forall b. q b => f b) -> f a -> f (t a)
#endif

instance (Generic1 t, GDeciding1 q (Rep1' t), GG (Rep1 t)) => Deciding1 q t where
  deciding1 p q r = contramap (swizzle . from1) $ gdeciding1 p q r

class GDeciding q t where
#ifndef HLINT
  gdeciding :: Decidable f => p q -> (forall b. q b => f b) -> f (t a)
#endif

instance GDeciding q U1 where
  gdeciding _ _ = conquer

instance GDeciding q V1 where
  gdeciding _ _ = glose

instance (GDeciding q f, GDeciding q g) => GDeciding q (f ::*: g) where
  gdeciding p q = gdivide (gdeciding p q) (gdeciding p q)

instance (GDeciding q f, GDeciding q g) => GDeciding q (f ::+: g) where
  gdeciding p q = gchoose (gdeciding p q) (gdeciding p q)

#ifndef HLINT
instance q p => GDeciding q (K1 i p) where
#endif
  gdeciding _ q = contramap unK1 q

instance GDeciding q f => GDeciding q (M1 i c f) where
  gdeciding p q = contramap unM1 (gdeciding p q)

class GDeciding1 q t where
#ifndef HLINT
  gdeciding1 :: Decidable f => p q -> (forall b. q b => f b) -> f a -> f (t a)
#endif

instance GDeciding1 q U1 where
  gdeciding1 _ _ _ = conquer

instance GDeciding1 q V1 where
  gdeciding1 _ _ _ = glose

instance (GDeciding1 q f, GDeciding1 q g) => GDeciding1 q (f ::*: g) where
  gdeciding1 p q r = gdivide (gdeciding1 p q r) (gdeciding1 p q r)

instance (GDeciding1 q f, GDeciding1 q g) => GDeciding1 q (f ::+: g) where
  gdeciding1 p q r = gchoose (gdeciding1 p q r) (gdeciding1 p q r)

absurd1 :: V1 a -> b
#if defined(HLINT) || (__GLASGOW_HASKELL__ < 708)
absurd1 x = x `seq` error "impossible"
#else
absurd1 x = case x of
#endif

glose :: Decidable f => f (V1 a)
glose = lose absurd1
{-# INLINE glose #-}

gdivide :: Divisible f => f (g a) -> f (h a) -> f ((g::*:h) a)
gdivide = divide unProd
{-# INLINE gdivide #-}

gchoose :: Decidable f => f (g a) -> f (h a) -> f ((g::+:h) a)
gchoose = choose unSum
{-# INLINE gchoose #-}

#ifndef HLINT
instance q p => GDeciding1 q (K1 i p) where
  gdeciding1 _ q _ = contramap unK1 q
#endif

instance GDeciding1 q f => GDeciding1 q (M1 i c f) where
  gdeciding1 p q r = contramap unM1 (gdeciding1 p q r)

instance GDeciding1 q Par1 where
  gdeciding1 _ _ r = contramap unPar1 r

-- instance GDeciding1 q f => GDeciding1 q (Rec1 f) where gdeciding1 p q r = contramap unRec1 (gdeciding1 p q r)

instance Deciding1 q f => GDeciding1 q (Rec1 f) where
  gdeciding1 p q r = contramap unRec1 (deciding1 p q r)
