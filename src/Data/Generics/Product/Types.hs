{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
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
import GHC.Generics (Generic (Rep), from, to)
import Boggle
--import GHC.TypeLits (TypeError, ErrorMessage (..))

class HasTypes a s where
  types :: Traversal' s a

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
  = Test Int Int String Char Char deriving (Generic, Show)

inty :: Int -> Maybe Int
inty = Just . (+1)

stringy :: String -> Maybe String
stringy = Just . (++"!")

-- >>> types2 inty (Test 10 20 "hello" 'a' 'b')
-- Just (Test 11 21 "hello" 'a' 'b')
--
-- >>> types2 (inty, stringy) (Test 10 20 "hello" 'a' 'b')
-- Just (Test 11 21 "hello!" 'a' 'b')
