#!/usr/bin/env stack
-- stack --resolver lts-9.9 --install-ghc ghci

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes, PolyKinds, GADTs #-}

-- これを圏論をどのくらい追うかの基準とする。
data Category :: (k -> k -> *) -> * where
 Category :: forall cat. (forall a. cat a a) -> (forall a b c. cat b c -> cat a b -> cat a c) -> Category cat

data Functor :: (k -> k) -> (k -> k -> *) -> (k -> k -> *) -> * where
 Functor :: forall f cat dat. Category cat -> Category dat -> (forall a b. cat a b -> dat (f a) (f b)) -> Functor f cat dat

data NatTrns :: (k -> k) -> (k -> k) -> (k -> k -> *) -> (k -> k -> *) -> * where
 NatTrns :: forall f g cat dat. Category cat -> Category dat -> Functor f cat dat -> Functor g cat dat -> (forall a. dat (f a) (g a)) -> NatTrns f g cat dat
