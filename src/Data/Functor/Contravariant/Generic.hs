{-# LANGUAGE CPP #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE BangPatterns #-}
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
import Unsafe.Coerce

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
class (Generic a, GDeciding q (Rep a)) => Deciding q a where
#ifndef HLINT
  deciding :: Decidable f => p q -> (forall b. q b => f b) -> f a
#endif

instance (Generic a, GDeciding q (Rep a)) => Deciding q a  where
  deciding p q = contramap from $ gdeciding p q

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
class (Generic1 t, GDeciding1 q (Rep1 t)) => Deciding1 q t where
#ifndef HLINT
  deciding1 :: Decidable f => p q -> (forall b. q b => f b) -> f a -> f (t a)
#endif

instance (Generic1 t, GDeciding1 q (Rep1 t)) => Deciding1 q t where
  deciding1 p q r = contramap from1 $ gdeciding1 p q r

class GDeciding q t where
#ifndef HLINT
  gdeciding :: Decidable f => p q -> (forall b. q b => f b) -> f (t a)
#endif

instance GDeciding q U1 where
  gdeciding _ _ = conquer

instance GDeciding q V1 where
  gdeciding _ _ = glose

instance (GDeciding q f, GDeciding q g) => GDeciding q (f :*: g) where
  gdeciding p q = gdivide (gdeciding p q) (gdeciding p q)

instance (GDeciding q f, GDeciding q g) => GDeciding q (f :+: g) where
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

instance (GDeciding1 q f, GDeciding1 q g) => GDeciding1 q (f :*: g) where
  gdeciding1 p q r = gdivide (gdeciding1 p q r) (gdeciding1 p q r)

instance (GDeciding1 q f, GDeciding1 q g) => GDeciding1 q (f :+: g) where
  gdeciding1 p q r = gchoose (gdeciding1 p q r) (gdeciding1 p q r)

glose :: Decidable f => f (V1 a)
glose = lose unsafeCoerce
{-# INLINE glose #-}

gdivide :: Divisible f => f (g a) -> f (h a) -> f ((g:*:h) a)
gdivide = divide unsafeCoerce
{-# INLINE gdivide #-}

gchoose :: Decidable f => f (g a) -> f (h a) -> f ((g:+:h) a)
gchoose = choose unsafeCoerce
{-# INLINE gchoose #-}

#ifndef HLINT
instance q p => GDeciding1 q (K1 i p) where
#endif
  gdeciding1 _ q _ = contramap unK1 q

instance GDeciding1 q f => GDeciding1 q (M1 i c f) where
  gdeciding1 p q r = contramap unM1 (gdeciding1 p q r)

instance GDeciding1 q Par1 where
  gdeciding1 _ _ r = contramap unPar1 r

-- instance GDeciding1 q f => GDeciding1 q (Rec1 f) where gdeciding1 p q r = contramap unRec1 (gdeciding1 p q r)

instance Deciding1 q f => GDeciding1 q (Rec1 f) where
  gdeciding1 p q r = contramap unRec1 (deciding1 p q r)
