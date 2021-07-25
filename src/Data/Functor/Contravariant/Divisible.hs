{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Safe #-}
#elif __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif

#if !(MIN_VERSION_transformers(0,6,0))
{-# OPTIONS_GHC -fno-warn-deprecations #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Contravariant.Divisible
-- Copyright   :  (C) 2014-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- This module supplies contravariant analogues to the 'Applicative' and 'Alternative' classes.
----------------------------------------------------------------------------
module Data.Functor.Contravariant.Divisible
  (
  -- * Contravariant Applicative
    Divisible(..), divided, conquered, liftD
  -- * Contravariant Alternative
  , Decidable(..), chosen, lost
  -- * Mathematical definitions
  -- ** Divisible
  -- $divisible

  -- *** A note on 'conquer'
  -- $conquer

  -- ** Decidable
  -- $decidable
  ) where

import Control.Applicative
import Control.Applicative.Backwards
import Control.Arrow
import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.RWS.Lazy as Lazy
import qualified Control.Monad.Trans.RWS.Strict as Strict
import Control.Monad.Trans.Reader
import qualified Control.Monad.Trans.State.Lazy as Lazy
import qualified Control.Monad.Trans.State.Strict as Strict
import qualified Control.Monad.Trans.Writer.Lazy as Lazy
import qualified Control.Monad.Trans.Writer.Strict as Strict

import Data.Functor.Compose
import Data.Functor.Constant
import Data.Functor.Contravariant
import Data.Functor.Product
import Data.Functor.Reverse
import Data.Void

#if !(MIN_VERSION_transformers(0,6,0))
import Control.Monad.Trans.Error
import Control.Monad.Trans.List
import Data.Either
#endif

#if MIN_VERSION_base(4,8,0)
import Data.Monoid (Alt(..))
#else
import Data.Monoid (Monoid(..))
#endif

#if MIN_VERSION_base(4,7,0) || defined(MIN_VERSION_tagged)
import Data.Proxy
#endif

#ifdef MIN_VERSION_StateVar
import Data.StateVar
#endif

#if __GLASGOW_HASKELL__ >= 702
#define GHC_GENERICS
import GHC.Generics
#endif

--------------------------------------------------------------------------------
-- * Contravariant Applicative
--------------------------------------------------------------------------------

-- |
--
-- A 'Divisible' contravariant functor is the contravariant analogue of 'Applicative'.
--
-- Continuing the intuition that 'Contravariant' functors consume input, a 'Divisible'
-- contravariant functor also has the ability to be composed "beside" another contravariant
-- functor.
--
-- Serializers provide a good example of 'Divisible' contravariant functors. To begin
-- let's start with the type of serializers for specific types:
--
-- @
-- newtype Serializer a = Serializer { runSerializer :: a -> ByteString }
-- @
--
-- This is a contravariant functor:
--
-- @
-- instance Contravariant Serializer where
--   contramap f s = Serializer (runSerializer s . f)
-- @
--
-- That is, given a serializer for @a@ (@s :: Serializer a@), and a way to turn
-- @b@s into @a@s (a mapping @f :: b -> a@), we have a serializer for @b@:
-- @contramap f s :: Serializer b@.
--
-- Divisible gives us a way to combine two serializers that focus on different
-- parts of a structure. If we postulate the existance of two primitive
-- serializers - @string :: Serializer String@ and @int :: Serializer Int@, we
-- would like to be able to combine these into a serializer for pairs of
-- @String@s and @Int@s. How can we do this? Simply run both serializers and
-- combine their output!
--
-- @
-- data StringAndInt = StringAndInt String Int
--
-- stringAndInt :: Serializer StringAndInt
-- stringAndInt = Serializer $ \\(StringAndInt s i) ->
--   let sBytes = runSerializer string s
--       iBytes = runSerializer int i
--   in sBytes <> iBytes
-- @
--
-- 'divide' is a generalization by also taking a 'contramap' like function to
-- split any @a@ into a pair. This conveniently allows you to target fields of
-- a record, for instance, by extracting the values under two fields and
-- combining them into a tuple.
--
-- To complete the example, here is how to write @stringAndInt@ using a
-- @Divisible@ instance:
--
-- @
-- instance Divisible Serializer where
--   conquer = Serializer (const mempty)
--
--   divide toBC bSerializer cSerializer = Serializer $ \\a ->
--     case toBC a of
--       (b, c) ->
--         let bBytes = runSerializer bSerializer b
--             cBytes = runSerializer cSerializer c
--         in bBytes <> cBytes
--
-- stringAndInt :: Serializer StringAndInt
-- stringAndInt =
--   divide (\\(StringAndInt s i) -> (s, i)) string int
-- @
--
class Contravariant f => Divisible f where
  --- | If one can handle split `a` into `(b, c)`, as well as handle `b`s and `c`s, then one can handle `a`s
  divide  :: (a -> (b, c)) -> f b -> f c -> f a

  -- | Conquer acts as an identity for combining @Divisible@ functors.
  conquer :: f a

-- |
-- @
-- 'divided' = 'divide' 'id'
-- @
divided :: Divisible f => f a -> f b -> f (a, b)
divided = divide id

-- | Redundant, but provided for symmetry.
--
-- @
-- 'conquered' = 'conquer'
-- @
conquered :: Divisible f => f ()
conquered = conquer

-- |
-- This is the divisible analogue of 'liftA'. It gives a viable default definition for 'contramap' in terms
-- of the members of 'Divisible'.
--
-- @
-- 'liftD' f = 'divide' ((,) () . f) 'conquer'
-- @
liftD :: Divisible f => (a -> b) -> f b -> f a
liftD f = divide ((,) () . f) conquer

instance Monoid r => Divisible (Op r) where
  divide f (Op g) (Op h) = Op $ \a -> case f a of
    (b, c) -> g b `mappend` h c
  conquer = Op $ const mempty

instance Divisible Comparison where
  divide f (Comparison g) (Comparison h) = Comparison $ \a b -> case f a of
    (a',a'') -> case f b of
      (b',b'') -> g a' b' `mappend` h a'' b''
  conquer = Comparison $ \_ _ -> EQ

instance Divisible Equivalence where
  divide f (Equivalence g) (Equivalence h) = Equivalence $ \a b -> case f a of
    (a',a'') -> case f b of
      (b',b'') -> g a' b' && h a'' b''
  conquer = Equivalence $ \_ _ -> True

instance Divisible Predicate where
  divide f (Predicate g) (Predicate h) = Predicate $ \a -> case f a of
    (b, c) -> g b && h c
  conquer = Predicate $ const True

instance Monoid m => Divisible (Const m) where
  divide _ (Const a) (Const b) = Const (mappend a b)
  conquer = Const mempty

#if MIN_VERSION_base(4,8,0)
instance Divisible f => Divisible (Alt f) where
  divide f (Alt l) (Alt r) = Alt $ divide f l r
  conquer = Alt conquer
#endif

#ifdef GHC_GENERICS
instance Divisible U1 where
  divide _ U1 U1 = U1
  conquer = U1

instance Divisible f => Divisible (Rec1 f) where
  divide f (Rec1 l) (Rec1 r) = Rec1 $ divide f l r
  conquer = Rec1 conquer

instance Divisible f => Divisible (M1 i c f) where
  divide f (M1 l) (M1 r) = M1 $ divide f l r
  conquer = M1 conquer

instance (Divisible f, Divisible g) => Divisible (f :*: g) where
  divide f (l1 :*: r1) (l2 :*: r2) = divide f l1 l2 :*: divide f r1 r2
  conquer = conquer :*: conquer

instance (Applicative f, Divisible g) => Divisible (f :.: g) where
  divide f (Comp1 l) (Comp1 r) = Comp1 (divide f <$> l <*> r)
  conquer = Comp1 $ pure conquer
#endif

instance Divisible f => Divisible (Backwards f) where
  divide f (Backwards l) (Backwards r) = Backwards $ divide f l r
  conquer = Backwards conquer

instance Divisible m => Divisible (ExceptT e m) where
  divide f (ExceptT l) (ExceptT r) = ExceptT $ divide (funzip . fmap f) l r
  conquer = ExceptT conquer

instance Divisible f => Divisible (IdentityT f) where
  divide f (IdentityT l) (IdentityT r) = IdentityT $ divide f l r
  conquer = IdentityT conquer

instance Divisible m => Divisible (MaybeT m) where
  divide f (MaybeT l) (MaybeT r) = MaybeT $ divide (funzip . fmap f) l r
  conquer = MaybeT conquer

instance Divisible m => Divisible (ReaderT r m) where
  divide abc (ReaderT rmb) (ReaderT rmc) = ReaderT $ \r -> divide abc (rmb r) (rmc r)
  conquer = ReaderT $ \_ -> conquer

instance Divisible m => Divisible (Lazy.RWST r w s m) where
  divide abc (Lazy.RWST rsmb) (Lazy.RWST rsmc) = Lazy.RWST $ \r s ->
    divide (\ ~(a, s', w) -> case abc a of
                                  ~(b, c) -> ((b, s', w), (c, s', w)))
           (rsmb r s) (rsmc r s)
  conquer = Lazy.RWST $ \_ _ -> conquer

instance Divisible m => Divisible (Strict.RWST r w s m) where
  divide abc (Strict.RWST rsmb) (Strict.RWST rsmc) = Strict.RWST $ \r s ->
    divide (\(a, s', w) -> case abc a of
                                (b, c) -> ((b, s', w), (c, s', w)))
           (rsmb r s) (rsmc r s)
  conquer = Strict.RWST $ \_ _ -> conquer

instance Divisible m => Divisible (Lazy.StateT s m) where
  divide f (Lazy.StateT l) (Lazy.StateT r) = Lazy.StateT $ \s ->
    divide (lazyFanout f) (l s) (r s)
  conquer = Lazy.StateT $ \_ -> conquer

instance Divisible m => Divisible (Strict.StateT s m) where
  divide f (Strict.StateT l) (Strict.StateT r) = Strict.StateT $ \s ->
    divide (strictFanout f) (l s) (r s)
  conquer = Strict.StateT $ \_ -> conquer

instance Divisible m => Divisible (Lazy.WriterT w m) where
  divide f (Lazy.WriterT l) (Lazy.WriterT r) = Lazy.WriterT $
    divide (lazyFanout f) l r
  conquer = Lazy.WriterT conquer

instance Divisible m => Divisible (Strict.WriterT w m) where
  divide f (Strict.WriterT l) (Strict.WriterT r) = Strict.WriterT $
    divide (strictFanout f) l r
  conquer = Strict.WriterT conquer

instance (Applicative f, Divisible g) => Divisible (Compose f g) where
  divide f (Compose l) (Compose r) = Compose (divide f <$> l <*> r)
  conquer = Compose $ pure conquer

instance Monoid m => Divisible (Constant m) where
  divide _ (Constant l) (Constant r) = Constant $ mappend l r
  conquer = Constant mempty

instance (Divisible f, Divisible g) => Divisible (Product f g) where
  divide f (Pair l1 r1) (Pair l2 r2) = Pair (divide f l1 l2) (divide f r1 r2)
  conquer = Pair conquer conquer

instance Divisible f => Divisible (Reverse f) where
  divide f (Reverse l) (Reverse r) = Reverse $ divide f l r
  conquer = Reverse conquer

#if MIN_VERSION_base(4,7,0) || defined(MIN_VERSION_tagged)
instance Divisible Proxy where
  divide _ Proxy Proxy = Proxy
  conquer = Proxy
#endif

#ifdef MIN_VERSION_StateVar
instance Divisible SettableStateVar where
  divide k (SettableStateVar l) (SettableStateVar r) = SettableStateVar $ \ a -> case k a of
    (b, c) -> l b >> r c
  conquer = SettableStateVar $ \_ -> return ()
#endif

lazyFanout :: (a -> (b, c)) -> (a, s) -> ((b, s), (c, s))
lazyFanout f ~(a, s) = case f a of
  ~(b, c) -> ((b, s), (c, s))

strictFanout :: (a -> (b, c)) -> (a, s) -> ((b, s), (c, s))
strictFanout f (a, s) = case f a of
  (b, c) -> ((b, s), (c, s))

funzip :: Functor f => f (a, b) -> (f a, f b)
funzip = fmap fst &&& fmap snd

--------------------------------------------------------------------------------
-- * Contravariant Alternative
--------------------------------------------------------------------------------

-- | A 'Decidable' contravariant functor is the contravariant analogue of 'Alternative'.
--
-- Noting the superclass constraint that @f@ must also be 'Divisible', a @Decidable@
-- functor has the ability to "fan out" input, under the intuition that contravariant
-- functors consume input.
--
-- In the discussion for @Divisible@, an example was demonstrated with @Serializer@s,
-- that turn @a@s into @ByteString@s. @Divisible@ allowed us to serialize the /product/
-- of multiple values by concatenation. By making our @Serializer@ also @Decidable@-
-- we now have the ability to serialize the /sum/ of multiple values - for example
-- different constructors in an ADT.
--
-- Consider serializing arbitrary identifiers that can be either @String@s or @Int@s:
--
-- @
-- data Identifier = StringId String | IntId Int
-- @
--
-- We know we have serializers for @String@s and @Int@s, but how do we combine them
-- into a @Serializer@ for @Identifier@? Essentially, our @Serializer@ needs to
-- scrutinise the incoming value and choose how to serialize it:
--
-- @
-- identifier :: Serializer Identifier
-- identifier = Serializer $ \\identifier ->
--   case identifier of
--     StringId s -> runSerializer string s
--     IntId i -> runSerializer int i
-- @
--
-- It is exactly this notion of choice that @Decidable@ encodes. Hence if we add
-- an instance of @Decidable@ for @Serializer@...
--
-- @
-- instance Decidable Serializer where
--   lose f = Serializer $ \\a -> absurd (f a)
--   choose split l r = Serializer $ \\a ->
--     either (runSerializer l) (runSerializer r) (split a)
-- @
--
-- Then our @identifier@ @Serializer@ is
--
-- @
-- identifier :: Serializer Identifier
-- identifier = choose toEither string int where
--   toEither (StringId s) = Left s
--   toEither (IntId i) = Right i
-- @
class Divisible f => Decidable f where
  -- | Acts as identity to 'choose'.
  lose :: (a -> Void) -> f a

  choose :: (a -> Either b c) -> f b -> f c -> f a

-- |
-- @
-- 'lost' = 'lose' 'id'
-- @
lost :: Decidable f => f Void
lost = lose id

-- |
-- @
-- 'chosen' = 'choose' 'id'
-- @
chosen :: Decidable f => f b -> f c -> f (Either b c)
chosen = choose id

instance Decidable Comparison where
  lose f = Comparison $ \a _ -> absurd (f a)
  choose f (Comparison g) (Comparison h) = Comparison $ \a b -> case f a of
    Left c -> case f b of
      Left d -> g c d
      Right{} -> LT
    Right c -> case f b of
      Left{} -> GT
      Right d -> h c d

instance Decidable Equivalence where
  lose f = Equivalence $ absurd . f
  choose f (Equivalence g) (Equivalence h) = Equivalence $ \a b -> case f a of
    Left c -> case f b of
      Left d -> g c d
      Right{} -> False
    Right c -> case f b of
      Left{} -> False
      Right d -> h c d

instance Decidable Predicate where
  lose f = Predicate $ absurd . f
  choose f (Predicate g) (Predicate h) = Predicate $ either g h . f

instance Monoid r => Decidable (Op r) where
  lose f = Op $ absurd . f
  choose f (Op g) (Op h) = Op $ either g h . f

#if MIN_VERSION_base(4,8,0)
instance Decidable f => Decidable (Alt f) where
  lose = Alt . lose
  choose f (Alt l) (Alt r) = Alt $ choose f l r
#endif

#ifdef GHC_GENERICS
instance Decidable U1 where
  lose _ = U1
  choose _ U1 U1 = U1

instance Decidable f => Decidable (Rec1 f) where
  lose = Rec1 . lose
  choose f (Rec1 l) (Rec1 r) = Rec1 $ choose f l r

instance Decidable f => Decidable (M1 i c f) where
  lose = M1 . lose
  choose f (M1 l) (M1 r) = M1 $ choose f l r

instance (Decidable f, Decidable g) => Decidable (f :*: g) where
  lose f = lose f :*: lose f
  choose f (l1 :*: r1) (l2 :*: r2) = choose f l1 l2 :*: choose f r1 r2

instance (Applicative f, Decidable g) => Decidable (f :.: g) where
  lose = Comp1 . pure . lose
  choose f (Comp1 l) (Comp1 r) = Comp1 (choose f <$> l <*> r)
#endif

instance Decidable f => Decidable (Backwards f) where
  lose = Backwards . lose
  choose f (Backwards l) (Backwards r) = Backwards $ choose f l r

instance Decidable f => Decidable (IdentityT f) where
  lose = IdentityT . lose
  choose f (IdentityT l) (IdentityT r) = IdentityT $ choose f l r

instance Decidable m => Decidable (ReaderT r m) where
  lose f = ReaderT $ \_ -> lose f
  choose abc (ReaderT rmb) (ReaderT rmc) = ReaderT $ \r -> choose abc (rmb r) (rmc r)

instance Decidable m => Decidable (Lazy.RWST r w s m) where
  lose f = Lazy.RWST $ \_ _ -> contramap (\ ~(a, _, _) -> a) (lose f)
  choose abc (Lazy.RWST rsmb) (Lazy.RWST rsmc) = Lazy.RWST $ \r s ->
    choose (\ ~(a, s', w) -> either (Left  . betuple3 s' w)
                                    (Right . betuple3 s' w)
                                    (abc a))
           (rsmb r s) (rsmc r s)

instance Decidable m => Decidable (Strict.RWST r w s m) where
  lose f = Strict.RWST $ \_ _ -> contramap (\(a, _, _) -> a) (lose f)
  choose abc (Strict.RWST rsmb) (Strict.RWST rsmc) = Strict.RWST $ \r s ->
    choose (\(a, s', w) -> either (Left  . betuple3 s' w)
                                  (Right . betuple3 s' w)
                                  (abc a))
           (rsmb r s) (rsmc r s)

#if !(MIN_VERSION_transformers(0,6,0))
instance Divisible m => Divisible (ErrorT e m) where
  divide f (ErrorT l) (ErrorT r) = ErrorT $ divide (funzip . fmap f) l r
  conquer = ErrorT conquer

instance Divisible m => Divisible (ListT m) where
  divide f (ListT l) (ListT r) = ListT $ divide (funzip . map f) l r
  conquer = ListT conquer

instance Divisible m => Decidable (ListT m) where
  lose _ = ListT conquer
  choose f (ListT l) (ListT r) = ListT $ divide ((lefts &&& rights) . map f) l r
#endif

instance Divisible m => Decidable (MaybeT m) where
  lose _ = MaybeT conquer
  choose f (MaybeT l) (MaybeT r) = MaybeT $
    divide ( maybe (Nothing, Nothing)
                   (either (\b -> (Just b, Nothing))
                           (\c -> (Nothing, Just c)) . f)
           ) l r

instance Decidable m => Decidable (Lazy.StateT s m) where
  lose f = Lazy.StateT $ \_ -> contramap lazyFst (lose f)
  choose f (Lazy.StateT l) (Lazy.StateT r) = Lazy.StateT $ \s ->
    choose (\ ~(a, s') -> either (Left . betuple s') (Right . betuple s') (f a))
           (l s) (r s)

instance Decidable m => Decidable (Strict.StateT s m) where
  lose f = Strict.StateT $ \_ -> contramap fst (lose f)
  choose f (Strict.StateT l) (Strict.StateT r) = Strict.StateT $ \s ->
    choose (\(a, s') -> either (Left . betuple s') (Right . betuple s') (f a))
           (l s) (r s)

instance Decidable m => Decidable (Lazy.WriterT w m) where
  lose f = Lazy.WriterT $ contramap lazyFst (lose f)
  choose f (Lazy.WriterT l) (Lazy.WriterT r) = Lazy.WriterT $
    choose (\ ~(a, s') -> either (Left . betuple s') (Right . betuple s') (f a)) l r

instance Decidable m => Decidable (Strict.WriterT w m) where
  lose f = Strict.WriterT $ contramap fst (lose f)
  choose f (Strict.WriterT l) (Strict.WriterT r) = Strict.WriterT $
    choose (\(a, s') -> either (Left . betuple s') (Right . betuple s') (f a)) l r

instance (Applicative f, Decidable g) => Decidable (Compose f g) where
  lose = Compose . pure . lose
  choose f (Compose l) (Compose r) = Compose (choose f <$> l <*> r)

instance (Decidable f, Decidable g) => Decidable (Product f g) where
  lose f = Pair (lose f) (lose f)
  choose f (Pair l1 r1) (Pair l2 r2) = Pair (choose f l1 l2) (choose f r1 r2)

instance Decidable f => Decidable (Reverse f) where
  lose = Reverse . lose
  choose f (Reverse l) (Reverse r) = Reverse $ choose f l r

betuple :: s -> a -> (a, s)
betuple s a = (a, s)

betuple3 :: s -> w -> a -> (a, s, w)
betuple3 s w a = (a, s, w)

lazyFst :: (a, b) -> a
lazyFst ~(a, _) = a

#if MIN_VERSION_base(4,7,0) || defined(MIN_VERSION_tagged)
instance Decidable Proxy where
  lose _ = Proxy
  choose _ Proxy Proxy = Proxy
#endif

#ifdef MIN_VERSION_StateVar
instance Decidable SettableStateVar where
  lose k = SettableStateVar (absurd . k)
  choose k (SettableStateVar l) (SettableStateVar r) = SettableStateVar $ \ a -> case k a of
    Left b -> l b
    Right c -> r c
#endif

-- $divisible
--
-- In denser jargon, a 'Divisible' contravariant functor is a monoid object in the category
-- of presheaves from Hask to Hask, equipped with Day convolution mapping the Cartesian
-- product of the source to the Cartesian product of the target.
--
-- By way of contrast, an 'Applicative' functor can be viewed as a monoid object in the
-- category of copresheaves from Hask to Hask, equipped with Day convolution mapping the
-- Cartesian product of the source to the Cartesian product of the target.
--
-- Given the canonical diagonal morphism:
--
-- @
-- delta a = (a,a)
-- @
--
-- @'divide' 'delta'@ should be associative with 'conquer' as a unit
--
-- @
-- 'divide' 'delta' m 'conquer' = m
-- 'divide' 'delta' 'conquer' m = m
-- 'divide' 'delta' ('divide' 'delta' m n) o = 'divide' 'delta' m ('divide' 'delta' n o)
-- @
--
-- With more general arguments you'll need to reassociate and project using the monoidal
-- structure of the source category. (Here fst and snd are used in lieu of the more restricted
-- lambda and rho, but this construction works with just a monoidal category.)
--
-- @
-- 'divide' f m 'conquer' = 'contramap' ('fst' . f) m
-- 'divide' f 'conquer' m = 'contramap' ('snd' . f) m
-- 'divide' f ('divide' g m n) o = 'divide' f' m ('divide' 'id' n o) where
--   f' a = let (bc, d) = f a; (b, c) = g bc in (b, (c, d))
-- @

-- $conquer
-- The underlying theory would suggest that this should be:
--
-- @
-- conquer :: (a -> ()) -> f a
-- @
--
-- However, as we are working over a Cartesian category (Hask) and the Cartesian product, such an input
-- morphism is uniquely determined to be @'const' 'mempty'@, so we elide it.

-- $decidable
--
-- A 'Divisible' contravariant functor is a monoid object in the category of presheaves
-- from Hask to Hask, equipped with Day convolution mapping the cartesian product of the
-- source to the Cartesian product of the target.
--
-- @
-- 'choose' 'Left' m ('lose' f)  = m
-- 'choose' 'Right' ('lose' f) m = m
-- 'choose' f ('choose' g m n) o = 'choose' f' m ('choose' 'id' n o) where
--   f' = 'either' ('either' 'id' 'Left' . g) ('Right' . 'Right') . f
-- @
--
-- In addition, we expect the same kind of distributive law as is satisfied by the usual
-- covariant 'Alternative', w.r.t 'Applicative', which should be fully formulated and
-- added here at some point!
