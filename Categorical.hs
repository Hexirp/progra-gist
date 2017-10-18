#!/usr/bin/env stack
-- stack --resolver lts-9.9 --install-ghc ghci

{-# LANGUAGE RankNTypes, PolyKinds, GADTs #-}

data Category :: (k -> k -> *) -> * where
 Category :: forall cat. (forall a. cat a a) -> (forall a b c. cat b c -> cat a b -> cat a c) -> Category cat
