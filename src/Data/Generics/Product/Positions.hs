{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Product.Positions
-- Copyright   :  (C) 2017 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Derive positional product type getters and setters generically.
--
-----------------------------------------------------------------------------

module Data.Generics.Product.Positions
  ( -- *Lenses

    --  $example
    HasPosition (..)
  ) where

import Data.Generics.Internal.Lens
import Data.Generics.Internal.Void
import Data.Generics.Internal.Families
import Data.Generics.Product.Internal.Positions

import Data.Kind      (Constraint, Type)
import Data.Type.Bool (type (&&), If)
import GHC.Generics
import GHC.TypeLits   (type (<=?),  Nat, TypeError, ErrorMessage(..))

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

-- |Records that have a field at a given position.
class HasPosition (i :: Nat) s t a b | s i -> a, s i b -> t where
  -- |A lens that focuses on a field at a given position. Compatible with the
  --  lens package's 'Control.Lens.Lens' type.
  --
  --  >>> human ^. position @1
  --  "Tunyasz"
  --  >>> human & position @2 .~ "Berlin"
  --  Human {name = "Tunyasz", age = 50, address = "Berlin"}
  position :: Lens s t a b

type GHasPosition' i s a = GHasPosition 1 i s s a a

instance  -- see Note [Changing type parameters]
  ( Generic s
  , ErrorUnless i s (0 <? i && i <=? Size (Rep s))
  , Generic t
  , s' ~ Proxied s
  , GHasPosition' i (Rep s) a
  , GHasPosition' i (Rep s') a'
  , GHasPosition 1 i (Rep s) (Rep t) a b
  , '(t', b') ~ If (IsParam a') '(Change s' (IndexOf a') b, P (IndexOf a') b) '(s', b)
  , t ~ UnProxied t'
  ) => HasPosition i s t a b where

  position f s = ravel (repLens . gposition @1 @i) f s

-- See Note [Uncluttering type signatures]
instance {-# OVERLAPPING #-} HasPosition f Void Void Void Void where
  position = undefined

type family ErrorUnless (i :: Nat) (s :: Type) (hasP :: Bool) :: Constraint where
  ErrorUnless i s 'False
    = TypeError
        (     'Text "The type "
        ':<>: 'ShowType s
        ':<>: 'Text " does not contain a field at position "
        ':<>: 'ShowType i
        )

  ErrorUnless _ _ 'True
    = ()
