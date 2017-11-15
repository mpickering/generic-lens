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

-- TODO: this is a breaking change
-- |Records that have a field with a given name.
class HasField (field :: Symbol) s t a b | s field b -> t, s field -> a where
  -- |A lens that focuses on a field with a given name. Compatible with the
  --  lens package's 'Control.Lens.Lens' type.
  --
  --  >>> human ^. field @"age"
  --  50
  --  >>> human & field @"name" .~ "Tamas"
  --  Human {name = "Tamas", age = 50, address = "London"}
  field :: Lens s t a b

class GChange field s t a b | field s b -> t
instance
  ( Generic s
  , Generic t
  , t ~ Match field s (Replace field (Rep s) b) (AllParams s b)
  ) => GChange field s t a b

instance
  ( Generic s
  , Generic t
  , GHasField field (Rep s) (Rep s) a a -- get `a`
  , GChange field s t a b
  , GHasField field (Rep s) (Rep t) a b
  , ErrorUnless field s (HasTotalFieldP field (Rep s))
  ) => HasField field s t a b where

  field = ravel (repLens . gfield @field)

type family IfEq a b t e where
  IfEq a a t _ = t
  IfEq a _ _ e = e

-- map . flip ($)
type family MapApp (a :: k) (cs :: [k -> j]) :: [j] where
  MapApp _ '[] = '[]
  MapApp a (c ': cs) = c a ': MapApp a cs

-- | Replace all type parameters one-by-one
--
-- >>> :kind! AllParams  (Test Int String) Bool
--
-- AllParams  (Test Int String) Bool :: [*]
-- = '[Test Int Bool, Test Bool String, Test Int String]
type family AllParams (s :: k) (b :: Type) :: [k] where
  AllParams (s x) b = s b ': MapApp x (AllParams s b)
  AllParams s _ = '[s]

-- | Replace the type of a field in the generic rep
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

type family Match field s (rep :: Type -> Type) (bs :: [Type]) :: Type where
  Match field s rep (b ': bs) = IfEq rep (Rep b) b (Match field s rep bs)
  Match field s rep '[]
    = TypeError
        (     'Text "The type of "
        ':<>: 'Text field
        ':<>: 'Text " is not a parameter of "
        ':$$: 'ShowType s
        ':$$: 'Text "therefore its type can't be changed."
        )

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
