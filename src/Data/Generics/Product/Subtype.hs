{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Product.Subtype
-- Copyright   :  (C) 2017 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Structural subtype relationship between record types.
--
-- The running example in this module is the following two types:
--
-- @
--
--   module Test where
--
--   import GHC.Generics
--   import Data.Generics.Record
--
--   data Human = Human
--     { name    :: String
--     , age     :: Int
--     , address :: String
--     } deriving (Generic, Show)
--
--   data Animal = Animal
--     { name    :: String
--     , age     :: Int
--     } deriving (Generic, Show)
--
--    human :: Human
--    human = Human \"Tunyasz\" 50 \"London\"
--
-- @
--
-----------------------------------------------------------------------------
module Data.Generics.Product.Subtype
  ( Subtype (..)

  , Method (..)
  ) where

import Data.Generics.Internal.Families
import Data.Generics.Internal.Lens
import Data.Generics.Product.Fields
import Data.Generics.Product.Typed

import Data.Kind
import GHC.Generics
import GHC.TypeLits

data Method
  = Label
  | Typed

-- |Structural subtype relationship
--
-- @sub@ is a (structural) `subtype' of @sup@, if its fields are a subset of
-- those of @sup@.
--
class Subtype (method :: Method) sup sub where
  -- | Structural subtype lens. Given a subtype relationship @sub :< sup@,
  --   we can focus on the @sub@ structure of @sup@.
  --
  -- >>> human ^. super @Animal
  -- Animal {name = "Tunyasz", age = 50}
  --
  -- >>> set (super @Animal) (Animal "dog" 10) human
  -- Human {name = "dog", age = 10, address = "London"}
  super  :: Lens' sub sup
  super f sub
    = fmap (flip (smash @method) sub) (f (upcast @method sub))

  -- | Cast the more specific subtype to the more general supertype
  --
  -- >>> upcast human :: Animal
  -- Animal {name = "Tunyasz", age = 50}
  --
  upcast :: sub -> sup
  upcast s = s ^. super @method @sup

  -- | Plug a smaller structure into a larger one
  --
  -- >>> smash (Animal "dog" 10) human
  -- Human {name = "dog", age = 10, address = "London"}
  smash  :: sup -> sub -> sub
  smash = set (super @method @sup)

  {-# MINIMAL super | smash, upcast #-}

-- | Instances are created by the compiler
instance
  ( GSmashN (Rep sub) (Rep sup)
  , GUpcastN (Rep sub) (Rep sup)
  , Generic sup
  , Generic sub
  ) => Subtype 'Label sup sub where
    smash p b = to $ gsmashN (from p) (from b)
    upcast    = to . gupcastN . from

instance
  ( GSmashU (Rep sub) (Rep sup)
  , GUpcastU (Rep sub) (Rep sup)
  , Generic sup
  , Generic sub
  , TypedErrorUnless sub sup (Compatible (Rep sup) (Rep sub))
  ) => Subtype 'Typed sup sub where
    smash p b = to $ gsmashU (from p) (from b)
    upcast    = to . gupcastU . from

type family TypedErrorUnless sub sup (compatible :: Bool) :: Constraint where
  TypedErrorUnless sub sup 'False
    = TypeError
        (     'Text "The type "
        ':<>: 'ShowType sub
        ':<>: 'Text " can not be upcasted to "
        ':<>: 'ShowType sup
        ':<>: 'Text " due to duplicate fields."

        ':$$: 'Text "Try labelled upcasting instead."
        )

  TypedErrorUnless _ _ 'True
    = ()

--------------------------------------------------------------------------------
-- * Generic named upcasting

-- | Upcast 'sub to 'sup' (generic rep)
class GUpcastN (sub :: Type -> Type) (sup :: Type -> Type) where
  gupcastN :: sub p -> sup p

instance (GUpcastN sub a, GUpcastN sub b) => GUpcastN sub (a :*: b) where
  gupcastN rep = gupcastN rep :*: gupcastN rep

instance
  GHasField field sub t
  => GUpcastN sub (S1 ('MetaSel ('Just field) p f b) (Rec0 t)) where

  gupcastN r = M1 (K1 (r ^. gfield @field))

instance GUpcastN sub sup => GUpcastN sub (C1 c sup) where
  gupcastN = M1 . gupcastN

instance GUpcastN sub sup => GUpcastN sub (D1 c sup) where
  gupcastN = M1 . gupcastN

--------------------------------------------------------------------------------
-- * Generic named smashing

class GSmashN sub sup where
  gsmashN :: sup p -> sub p -> sub p

instance (GSmashN a sup, GSmashN b sup) => GSmashN (a :*: b) sup where
  gsmashN rep (a :*: b) = gsmashN rep a :*: gsmashN rep b

instance
  ( leaf ~ (S1 ('MetaSel ('Just field) p f b) t)
  , GSmashNLeafN leaf sup (HasTotalFieldP field sup)
  ) => GSmashN (S1 ('MetaSel ('Just field) p f b) t) sup where

  gsmashN = gsmashLeafN @_ @_ @(HasTotalFieldP field sup)

instance GSmashN sub sup => GSmashN (C1 c sub) sup where
  gsmashN sup (M1 sub) = M1 (gsmashN sup sub)

instance GSmashN sub sup => GSmashN (D1 c sub) sup where
  gsmashN sup (M1 sub) = M1 (gsmashN sup sub)

class GSmashNLeafN sub sup (w :: Bool) where
  gsmashLeafN :: sup p -> sub p -> sub p

instance
  GHasField field sup t
  => GSmashNLeafN (S1 ('MetaSel ('Just field) p f b) (Rec0 t)) sup 'True where
  gsmashLeafN sup _ = M1 (K1 (sup ^. gfield @field))

instance GSmashNLeafN (S1 ('MetaSel ('Just field) p f b) (Rec0 t)) sup 'False where
  gsmashLeafN _ = id


--------------------------------------------------------------------------------
-- * Generic unnamed upcasting

-- | Upcast 'sub to 'sup' (generic rep)
class GUpcastU (sub :: Type -> Type) (sup :: Type -> Type) where
  gupcastU :: sub p -> sup p

instance (GUpcastU sub a, GUpcastU sub b) => GUpcastU sub (a :*: b) where
  gupcastU rep = gupcastU rep :*: gupcastU rep

instance
  GHasType sub t
  => GUpcastU sub (S1 meta (Rec0 t)) where

  gupcastU r = M1 (K1 (r ^. gtyped))

instance GUpcastU sub sup => GUpcastU sub (C1 c sup) where
  gupcastU = M1 . gupcastU

instance GUpcastU sub sup => GUpcastU sub (D1 c sup) where
  gupcastU = M1 . gupcastU

--------------------------------------------------------------------------------
-- * Generic unnamed smashing

class GSmashU sub sup where
  gsmashU :: sup p -> sub p -> sub p

instance (GSmashU a sup, GSmashU b sup) => GSmashU (a :*: b) sup where
  gsmashU rep (a :*: b) = gsmashU rep a :*: gsmashU rep b

instance
  ( leaf ~ (S1 ('MetaSel ('Just field) p f b) t)
  , GSmashNLeafU leaf sup (HasTotalFieldP field sup)
  ) => GSmashU (S1 ('MetaSel ('Just field) p f b) t) sup where

  gsmashU = gsmashLeafU @_ @_ @(HasTotalFieldP field sup)

instance GSmashU sub sup => GSmashU (C1 c sub) sup where
  gsmashU sup (M1 sub) = M1 (gsmashU sup sub)

instance GSmashU sub sup => GSmashU (D1 c sub) sup where
  gsmashU sup (M1 sub) = M1 (gsmashU sup sub)

class GSmashNLeafU sub sup (w :: Bool) where
  gsmashLeafU :: sup p -> sub p -> sub p

instance
  GHasType sup t
  => GSmashNLeafU (S1 ('MetaSel ('Just field) p f b) (Rec0 t)) sup 'True where
  gsmashLeafU sup _ = M1 (K1 (sup ^. gtyped))

instance GSmashNLeafU (S1 ('MetaSel ('Just field) p f b) (Rec0 t)) sup 'False where
  gsmashLeafU _ = id


type family Compatible a other :: Bool where
  Compatible (S1 meta (Rec0 t)) other
    = IsOne (CountTotalType t other)
  Compatible (l :*: r) other
    = Compatible l other && Compatible r other
  Compatible (l :+: r) other
    = Compatible l other && Compatible r other
  Compatible (C1 m f) other
    = Compatible f other
  Compatible (D1 m f) other
    = Compatible f other
  Compatible _ _
    = 'False

type family IsOne (a :: Count) where
  IsOne 'One = 'True
  IsOne _   =  'False
