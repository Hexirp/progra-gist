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
 NatIso :: forall a b cat. Category cat -> cat a b -> cat b a -> NatIso a b cat

data MndCat :: k -> (k -> k -> k) -> (k -> k -> *) -> * where
 MndCat :: forall i f cat. Category cat -> Bifunctor f cat cat cat -> (forall a b c. NatIso (f a (f b c)) (f (f a b) c) cat) -> (forall a. NatIso (f i a) a cat) -> (forall a. NatIso (f a i) a cat) -> MndCat i f cat

data Op :: (k -> k -> *) -> k -> k -> * where
 Op :: forall cat a b. cat b a -> Op cat a b

data DiNatTrns :: (k -> k -> l) -> (k -> k -> l) -> (k -> k -> *) -> (l -> l -> *) -> * where
 DiNatTrns :: forall f g cat dat. Category cat -> Category dat -> Bifunctor f (Op cat) cat dat -> Bifunctor f (Op cat) cat dat -> (forall a. dat (f a a) (g a a)) -> DiNatTrns f g cat dat
