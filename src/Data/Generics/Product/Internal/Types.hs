{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Product.Internal.Types
-- Copyright   :  (C) 2017 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Derive traversals of a given type in a product.
--
-----------------------------------------------------------------------------

module Data.Generics.Product.Internal.Types
  ( GHasTypes (..)
  , GHasTypes2 (..)
  , GHasTypesC (..)
--  , GHasTypesR (..)

  , Functions -- TODO: don't export this
  ) where

import Data.Kind    (Type, Constraint)
import GHC.Generics
import Data.Generics.Internal.HList

--import Data.Kind    (Constraint, Type)
import GHC.Generics (Generic (Rep), from, to)
import Boggle

-- |As 'HasTypes' but over generic representations as defined by
--  "GHC.Generics".
class GHasTypes (f :: Type -> Type) a where
  gtypes :: forall g x. Applicative g => (a -> g a) -> f x -> Boggle g (f x)

instance (GHasTypes l a, GHasTypes r a) => GHasTypes (l :*: r) a where
  gtypes f (l :*: r) = (:*:) <$> gtypes f l <*> gtypes f r
  {-# INLINE gtypes #-}

instance (GHasTypes l a, GHasTypes r a) => GHasTypes (l :+: r) a where
  gtypes f (L1 l) = L1 <$> gtypes f l
  gtypes f (R1 l) = R1 <$> gtypes f l

instance GHasTypes (K1 R a) a where
  gtypes f (K1 x) = fmap K1 (liftBoggle (f x))
  {-# INLINE gtypes #-}


instance {-# OVERLAPS #-} GHasTypes (K1 R a) b where
  gtypes _ k = pure k
  {-# INLINE gtypes #-}

instance GHasTypes f a => GHasTypes (M1 m meta f) a where
  gtypes f (M1 x) = M1 <$>  gtypes f x
  {-# INLINE gtypes #-}

instance GHasTypes U1 a where
  gtypes f U1 = liftBoggle (const U1 <$> f undefined)
  {-# INLINE gtypes #-}

--------------------------------------------------------------------------------

class GHasTypes2 (f :: Type -> Type) (as :: [Type]) g where
  gtypes2 :: forall x. Applicative g => HList (Functions as g) -> f x -> Boggle g (f x)

type family Functions (ts :: [Type]) (g :: Type -> Type) = r | r -> ts where
  Functions '[] _ = '[]
  Functions (t ': ts) g = ((t -> g t) ': Functions ts g)

instance (GHasTypes2 l as g, GHasTypes2 r as g) => GHasTypes2 (l :*: r) as g where
  gtypes2 f (l :*: r) = (:*:) <$> gtypes2 @_ @as f l <*> gtypes2 @_ @as f r
  {-# INLINE gtypes2 #-}

-- TODO:
-- instance (GHasTypes2 l a, GHasTypes2 r a) => GHasTypes2 (l :+: r) a where

instance Find a (Functions as g) g => GHasTypes2 (K1 R a) as g where
  gtypes2 fs k = stuff fs k
  {-# INLINE gtypes2 #-}

instance GHasTypes2 t as g => GHasTypes2 (D1 m t) as g where
  gtypes2 fs (M1 x) = M1 <$> gtypes2 @_ @as fs x
  {-# INLINE gtypes2 #-}

instance GHasTypes2 t as g => GHasTypes2 (C1 m t) as g where
  gtypes2 fs (M1 x) = M1 <$> gtypes2 @_ @as fs x
  {-# INLINE gtypes2 #-}

instance GHasTypes2 t as g => GHasTypes2 (S1 m t) as g where
  gtypes2 fs (M1 x) = M1 <$> gtypes2 @_ @as fs x
  {-# INLINE gtypes2 #-}

class Find t (ts :: [Type]) g where
  stuff :: Applicative g => HList ts -> Rec0 t x -> Boggle g (Rec0 t x)

instance {-# OVERLAPPING #-} Find t ((t -> g t) ': ts) g where
  stuff (h :> _) (K1 x) = fmap K1 (liftBoggle (h x))

instance Find t ts g => Find t (x ': ts) g where
  stuff (_ :> hs) = stuff @t @ts hs

instance Find t '[] g where
  stuff _ k = pure k

--------------------------------------------------------------------------------

class GHasTypesC (f :: Type -> Type) (c :: Type -> Constraint) where
  cgtypes :: forall g x. Applicative g => (forall a. c a => a -> g a) -> f x -> Boggle g (f x)

instance (GHasTypesC l c, GHasTypesC r c) => GHasTypesC (l :*: r) c where
  cgtypes f (l :*: r) = (:*:) <$> cgtypes @_ @c f l <*> cgtypes @_ @c f r

instance c a => GHasTypesC (K1 R a) c where
  cgtypes f (K1 x) = fmap K1 (liftBoggle (f x))

instance GHasTypesC f c => GHasTypesC (M1 m meta f) c where
  cgtypes f (M1 x) = M1 <$>  cgtypes @_ @c  f x
