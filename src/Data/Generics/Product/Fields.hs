{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE KindSignatures          #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# LANGUAGE DeriveGeneric   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Product.Fields
-- Copyright   :  (C) 2017 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Derive record field getters and setters generically.
--
-----------------------------------------------------------------------------

module Data.Generics.Product.Fields
  ( -- *Lenses

    --  $example
    HasField (..)

  , HasField2 (..)
  ) where

import Data.Generics.Internal.Families
import Data.Generics.Internal.Lens
import Data.Generics.Product.Internal.Fields

import Data.Kind    (Constraint, Type)
import GHC.Generics
import GHC.TypeLits (Symbol, ErrorMessage(..), TypeError)

--  $example
--  @
--    module Example where
--
--    import Data.Generics.Product
--    import GHC.Generics
--
--    data Human = Human
--      { name    :: String
--      , age     :: Int
--      , address :: String
--      }
--      deriving (Generic, Show)
--
--    human :: Human
--    human = Human \"Tunyasz\" 50 \"London\"
--  @

-- |Records that have a field with a given name.
class HasField (field :: Symbol) a s | s field -> a where
  -- |A lens that focuses on a field with a given name. Compatible with the
  --  lens package's 'Control.Lens.Lens' type.
  --
  --  >>> human ^. field @"age"
  --  50
  --  >>> human & field @"name" .~ "Tamas"
  --  Human {name = "Tamas", age = 50, address = "London"}
  field :: Lens' s a
  field f s
    = fmap (flip (setField @field) s) (f (getField @field s))

  -- |Get 'field'
  --
  -- >>> getField @"name" human
  -- "Tunyasz"
  getField :: s -> a
  getField s = s ^. field @field

  -- |Set 'field'
  --
  -- >>> setField @"age" (setField @"name" "Tamas" human) 30
  -- Human {name = "Tamas", age = 30, address = "London"}
  setField :: a -> s -> s
  setField = set (field @field)

  {-# MINIMAL field | setField, getField #-}

instance
  ( Generic s
  , ErrorUnless field s (HasTotalFieldP field (Rep s))
  , GHasField field (Rep s) (Rep s) a a
  ) => HasField field a s where

  field = ravel (repLens . gfield @field)

type family ErrorUnless (field :: Symbol) (s :: Type) (contains :: Bool) :: Constraint where
  ErrorUnless field s 'False
    = TypeError
        (     'Text "The type "
        ':<>: 'ShowType s
        ':<>: 'Text " does not contain a field named "
        ':<>: 'ShowType field
        )

  ErrorUnless _ _ 'True
    = ()

--------------------------------------------------------------------------------

class HasField2 (field :: Symbol) s t a b | s field a b -> t where
  field2 :: Lens s t a b

instance
  ( Generic s
  , Generic t
  , GHasField field (Rep s) (Rep s) a a -- get `a`
  , t ~ Match (Replace field (Rep s) b) (Replace' s a b)
  , GHasField field (Rep s) (Rep t) a b
  ) => HasField2 field s t a b where

  field2 = repLens . gfield @field

data Test a b = Test { fieldInt :: Int, fieldA :: a, fieldB :: b } deriving (Generic, Show)

-- changedA :: Test Int String
-- >>> changedA
-- Test {fieldInt = 10, fieldA = 10, fieldB = "world"}
changedA = set (field2 @"fieldA") (10 :: Int) (Test 10 "hello" "world")

-- changedB :: Test String Int
-- >>> changedB
-- Test {fieldInt = 10, fieldA = "hello", fieldB = 10}
changedB = set (field2 @"fieldB") (10 :: Int) (Test 10 "hello" "world")

type family IfEq a b t e where
  IfEq a a t _ = t
  IfEq a _ _ e = e

type family MapApp (a :: k) (cs :: [k -> j]) :: [Type] where
  MapApp _ '[] = '[]
  MapApp a (c ': cs) = c a ': MapApp a cs

type family Replace' (s :: k) (a :: Type) (b :: Type) :: [k] where
  Replace' (s a) a b = s b ': MapApp a (Replace' s a b)
  Replace' (s a) a b = '[s b, s a]
  Replace' (s x) a b = s x ': MapApp x (Replace' s a b)
  Replace' s _ _     = '[s]

type family Replace (field :: Symbol) (f :: Type -> Type) (b :: Type) :: Type -> Type where
  Replace field (S1 ('MetaSel ('Just field) c f p) (Rec0 _)) b
    = S1 ('MetaSel ('Just field) c f p) (Rec0 b)
  Replace field (l :*: r) b
    = Replace field l b :*: Replace field r b
  Replace field (l :+: r) b
    = Replace field l b :+: Replace field r b
  Replace field (C1 m f) b
    = C1 m (Replace field f b)
  Replace field (D1 m f) b
    = D1 m (Replace field f b)
  Replace _ f _
    = f


type family Match (rep :: Type -> Type) (bs :: [Type]) where
  Match rep (b ': bs) = IfEq rep (Rep b) b (Match rep bs)
  Match rep '[] = TypeError ('Text "Didn't match: " ':<>: 'ShowType rep)


-- > :kind! Match (Replace "fieldA" (Rep (Test Int Int)) String) (Replace' (Test Int Int) Int String)
-- Match (Replace "fieldA" (Rep (Test Int Int)) String) (Replace' (Test Int Int) Int String) :: Maybe
--                                                                                                *
-- = 'Just (Test [Char] Int)
-- > :kind! Match (Replace "fieldB" (Rep (Test Int Int)) String) (Replace' (Test Int Int) Int String)
-- Match (Replace "fieldB" (Rep (Test Int Int)) String) (Replace' (Test Int Int) Int String) :: Maybe
--                                                                                                *
-- = 'Just (Test Int [Char])
