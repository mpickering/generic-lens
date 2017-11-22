{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}

{-# LANGUAGE AllowAmbiguousTypes             #-}
{-# LANGUAGE DataKinds                       #-}
{-# LANGUAGE DeriveGeneric                   #-}
{-# LANGUAGE DuplicateRecordFields           #-}
{-# LANGUAGE ExistentialQuantification       #-}
{-# LANGUAGE RankNTypes                      #-}
{-# LANGUAGE ScopedTypeVariables             #-}
{-# LANGUAGE TypeApplications                #-}
{-# LANGUAGE TemplateHaskell                 #-}

module Main where

import GHC.Generics
import Data.Generics.Product
import Data.Generics.Product.Boggle
import Data.Generics.Product.Types
import Test.Inspection

main :: IO ()
main = putStrLn "Hello world"

data Record = MkRecord
  { fieldA :: Int
  , fieldB :: Bool
  } deriving Generic

data Record2 = MkRecord2
  { fieldA :: Int
  } deriving Generic

data Record3 = MkRecord3
  { fieldA :: Int
  , fieldB :: Int
  , fieldC :: String
  , fieldD :: Int
  , fieldE :: Char
  , fieldF :: Int
  } deriving Generic

data Record4 a = MkRecord4
  { fieldA :: a
  , fieldB :: a
  } deriving (Generic1)

type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s

type Traversal' s a = forall f. Applicative f => (a -> f a) -> s -> f s

newtype L s a = L (Lens' s a)

intTraversalManual :: Traversal' Record3 Int
intTraversalManual = types

intTraversalDerived3 :: Traversal' (Record4 Int) Int
intTraversalDerived3 = genericTraverse

fieldALensManual :: Lens' Record Int
fieldALensManual f (MkRecord a b) = (\a' -> MkRecord a' b) <$> f a

subtypeLensManual :: Lens' Record Record2
subtypeLensManual f record
  = fmap (\ds -> case record of
                  MkRecord _ b -> MkRecord (case ds of {MkRecord2 g1 -> g1}) b
         ) (f (MkRecord2 (case record of {MkRecord a _ -> a})))

--------------------------------------------------------------------------------
-- * Tests
-- The inspection-testing plugin checks that the following equalities hold, by
-- checking that the LHSs and the RHSs are CSEd. This also means that the
-- runtime characteristics of the derived lenses is the same as the manually
-- written ones above.

fieldALensName :: Lens' Record Int
fieldALensName = field @"fieldA"

fieldALensType :: Lens' Record Int
fieldALensType = typed @Int

fieldALensPos :: Lens' Record Int
fieldALensPos = position @1

subtypeLensGeneric :: Lens' Record Record2
subtypeLensGeneric = super

inspect $ 'fieldALensManual === 'fieldALensName
inspect $ 'fieldALensManual === 'fieldALensType
inspect $ 'fieldALensManual === 'fieldALensPos
inspect $ 'subtypeLensManual === 'subtypeLensGeneric
