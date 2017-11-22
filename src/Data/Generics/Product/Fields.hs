{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeInType              #-}
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
import Data.Generics.Internal.Void
import Data.Generics.Product.Internal.Fields

import Data.Kind    (Constraint, Type)
import GHC.Generics
import GHC.TypeLits (Symbol, ErrorMessage(..), TypeError, Nat, type (+))
import Data.Type.Bool (If)

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

type GHasField' field s a = GHasField field s s a a

instance  -- see Note [Changing type parameters]
  ( Generic s'
  , Generic s
  , Generic t
  , s' ~ Proxied s
  , GHasField' field (Rep s) a
  , GHasField' field (Rep s') a'
  , GHasField field (Rep s) (Rep t) a b
  , '(t', b') ~ If (IsParam a') '(Change s' (IndexOf a') b, P (IndexOf a') b) '(s', b)
  , t ~ UnProxied t'
  , ErrorUnless field s (HasTotalFieldP field (Rep s))
  ) => HasField field s t a b where

  field f s = ravel (repLens . gfield @field) f s

-- See Note [Uncluttering type signatures]
instance {-# OVERLAPPING #-} HasField f Void Void Void Void where
  field = undefined

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

{-
  Note [Changing type parameters]
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  To get good type inference for type-changing lenses, we want to be able
  map the field's type back to the type argument it corresponds to. This way,
  when the field is changed, we know what the result type of the structure is
  going to be.

  However, for a given type @t@, its representation @Rep t@ forgets which types
  in the structure came from type variables, and which didn't. An @Int@ that
  results from the instantiation of the type paremeter and an @Int@ that was
  monomorphically specified in the structure are indistinguishable.

  The solution is to replace the type arguments in the type with unique
  proxies, like: @T a b@ -> @T (P 1 a) (P 0 b)@. This way, if looking up
  a field's type yields something of shape @P _ _@, we know it came from a type
  parameter, and also know which.

  If the field's type is a proxy, then its type is allowed to change, otherwise
  not. This also allows us to satisfy the functional dependency @s field b -> t@.
  If after doing the conversion on @s@, @field@'s type is @(P _ a), then @t@ is
  @s[b/a]@, otherwise @t ~ s@ and @b ~ a@.
-}
data P (i :: Nat) a

type Proxied t = Proxied' t 0

type family Proxied' (t :: k) (next :: Nat) :: k where
  Proxied' (t a :: k) next = (Proxied' t (next + 1)) (P next a)
  Proxied' t _ = t

type family UnProxied (t :: k) :: k where
  UnProxied (t (P _ a) :: k) = UnProxied t a
  UnProxied t = t

type family Change (t :: k) (target :: Nat) (to :: j) :: k where
  Change (t (P target _) :: k) target to = t (P target to)
  Change (t a :: k) target to = Change t target to a
  Change t _ _ = t

type family IsParam a where
  IsParam (P _ _) = 'True
  IsParam _ = 'False

type family IndexOf a where
  IndexOf (P i a) = i

