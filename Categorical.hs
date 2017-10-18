#!/usr/bin/env stack
-- stack --resolver lts-9.9 --install-ghc ghci

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes, PolyKinds, GADTs #-}

-- これを圏論をどのくらい追うかの基準とする。
data Category :: (k -> k -> *) -> * where
 Category :: forall cat. (forall a. cat a a) -> (forall a b c. cat b c -> cat a b -> cat a c) -> Category cat

data Functor :: (k0 -> k1) -> (k0 -> k0 -> *) -> (k1 -> k1 -> *) -> * where
 Functor :: forall f cat dat. Category cat -> Category dat -> (forall a b. cat a b -> dat (f a) (f b)) -> Functor f cat dat

data NatTrns :: (k -> k) -> (k -> k) -> (k -> k -> *) -> (k -> k -> *) -> * where
 NatTrns :: forall f g cat dat. Category cat -> Category dat -> Functor f cat dat -> Functor g cat dat -> (forall a. dat (f a) (g a)) -> NatTrns f g cat dat

data Bifunctor :: (k0 -> k1 -> k2) -> (k0 -> k0 -> *) -> (k1 -> k1 -> *) -> (k2 -> k2 -> *) -> * where
 Bifunctor :: forall f cat dat eat. Category cat -> Category dat -> Category eat -> (forall a b c d. cat a b -> dat c d -> eat (f a c) (f b c)) -> Bifunctor f cat dat eat

data NatIso :: k -> k -> (k -> k -> *) -> * where
 NatIso :: forall a b cat. cat a b -> cat b a -> NatIso a b cat

data MndCat :: k -> (k -> k -> k) -> (k -> k -> *) -> * where
 MndCat :: forall i f cat. Category cat -> Bifunctor f cat cat cat -> (forall a b c. NatIso (f a (f b c)) (f (f a b) c) cat) -> (forall a. NatIso (f i a) a cat) -> (forall a. NatIso (f a i) a cat) -> MndCat i f cat
