{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Product.Types
-- Copyright   :  (C) 2017 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Derive traversals of a given type in a product.
--
-----------------------------------------------------------------------------

module Data.Generics.Product.Types
  ( -- *Traversals
    --
    --  $example
    HasTypes (..)
  ) where

--import Data.Generics.Internal.Families
import Data.Generics.Internal.Lens
import Data.Generics.Internal.HList
import Data.Generics.Product.Internal.Types

import Data.Kind    (Constraint, Type)
import GHC.Generics
import Boggle
--import GHC.TypeLits (TypeError, ErrorMessage (..))

class HasTypes a s where
  types :: Traversal' s a

instance {-# OVERLAPPING #-} HasTypes a Int where
  types _ i = pure i

instance {-# OVERLAPPING #-} HasTypes a Char where
  types _ i = pure i

instance
  ( Generic s
  , GHasTypes (Rep s) a
  ) => HasTypes a s where

  types f s = lowerBoggle (to <$> gtypes f (from s))


class HasTypes2 f s fs where
  types2 :: Applicative f => fs -> s -> f s

instance
  ( Generic s
  , GHasTypes2 (Rep s) ts f
  , ListTuple fs (Functions ts f)
  , Functions ts f ~ TupleToList fs
  ) => HasTypes2 f s fs where

  types2 fs s = lowerBoggle (to <$> gtypes2 @_ @ts (tupleToList fs) (from s))

-- TODO: delete these eventually
data Test
  = Test Int Int String Char Char
  deriving (Generic, Show)

data Test2
  = Test2 Test Test
  deriving (Generic, Show)

inty :: Int -> Maybe Int
inty = Just . (+1)

stringy :: String -> Maybe String
stringy = Just . (++"!")

charry :: Char -> Maybe Char
charry = Just . const 'z'

booly :: Bool -> Maybe Bool
booly = Just . not

t = Test 10 20 "hello" 'a' 'b'

-- >>> types2 inty (Test 10 20 "hello" 'a' 'b')
-- Just (Test 11 21 "hello" 'a' 'b')
--
-- >>> types2 (inty, stringy) (Test 10 20 "hello" 'a' 'b')
-- Just (Test 11 21 "hello!" 'a' 'b')
--

--- >>> ctypes @_ @(HasTypes Char) (types charry) (Test2 t t)
--- Just (Test2 (Test 10 20 "hello" 'z' 'z') (Test 10 20 "hello" 'z' 'z'))

--------------------------------------------------------------------------------
-- constrained traversals

class HasTypesC s (c :: Type -> Constraint) where
  ctypes :: Applicative g => (forall a. c a => a -> g a) -> s -> g s

instance
  ( Generic s
  , GHasTypesC (Rep s) c
  ) => HasTypesC s c where

  ctypes f s = lowerBoggle (to <$> cgtypes @_ @c f (from s))

--------------------------------------------------------------------------------
class HasTypesR s a where
  typesR :: Traversal' s a

instance
  ( Generic s
  , GHasTypesR (Rep s) c
  ) => HasTypesR s c where

  typesR f s = lowerBoggle (to <$> gtypesR @_ @c f (from s))

data Void

--instance {-# OVERLAPPING #-} HasTypesR a a where
--  typesR f s = f s
--
--instance {-# OVERLAPPING #-} HasTypesR Char Char where
--  typesR f s = f s
--
instance {-# OVERLAPPING #-} HasTypesR Char a where
  typesR _ s = pure s

instance {-# OVERLAPPING #-} HasTypesR Int a where
  typesR _ s = pure s

instance {-# OVERLAPPING #-} HasTypesR Bool a where
  typesR _ s = pure s

--------------------------------------------------------------------------------
class GHasTypesR (f :: Type -> Type) a where
  gtypesR :: forall g x. Applicative g => (a -> g a) -> f x -> Boggle g (f x)

instance (GHasTypesR l a, GHasTypesR r a) => GHasTypesR (l :*: r) a where
  gtypesR f (l :*: r) = (:*:) <$> gtypesR f l <*> gtypesR f r
  {-# INLINE gtypesR #-}

instance (GHasTypesR l a, GHasTypesR r a) => GHasTypesR (l :+: r) a where
  gtypesR f (L1 l) = L1 <$> gtypesR f l
  gtypesR f (R1 l) = R1 <$> gtypesR f l

instance GHasTypesR (K1 R a) a where
  gtypesR f (K1 x) = fmap K1 (liftBoggle (f x))
  {-# INLINE gtypesR #-}

instance {-# OVERLAPS #-} HasTypesR a b => GHasTypesR (K1 R a) b where
  gtypesR f (K1 k) = K1 <$> (liftBoggle $ typesR f k)
  {-# INLINE gtypesR #-}

instance GHasTypesR f a => GHasTypesR (M1 m meta f) a where
  gtypesR f (M1 x) = M1 <$>  gtypesR f x
  {-# INLINE gtypesR #-}

instance GHasTypesR U1 a where
  gtypesR _ U1 = pure U1
  {-# INLINE gtypesR #-}
