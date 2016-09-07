module Naturals where

import Category

import Data.Type.Equality
import Data.Typeable

import Data.Proxy

import Data.Kind
import GHC.Exts

data N = Z | S N

type family x :+: y  where
    Z :+: y = y
    (S x) :+: y = S (x :+: y)

type family a :=: b where
    Z :=: Z = True
    (S a) :=: (S b) = a :=: b
    a :=: b = False


induct' :: forall z a p . (Typeable a, Typeable z) => p z -> (forall n . p n -> p (S n)) -> p a
induct' baseCase inductionCase = case eqT :: Maybe (a :~: z) of
                                   Just Refl -> baseCase
                                   _ -> induct' (inductionCase baseCase) inductionCase

induct :: forall a p . (Typeable a) => p Z -> (forall n . p n -> p (S n)) -> p a
induct = induct' @Z

cong :: (a :~: b) -> (S a :~: S b)
cong Refl = Refl

data Associative c b a = Associative {
      getAssociate :: Proxy a -> Proxy b -> Proxy c ->  (a :+: (b :+: c)) :~: ((a :+: b) :+: c)
    }

associativeZ :: Associative c b Z
associativeZ = Associative $ \_ _ _ -> Refl

associativeS :: forall c b a . Associative c b a -> Associative c b (S a)
associativeS recurse = Associative $ \_ b c -> cong (getAssociate recurse (Proxy @a) b c)

associative :: Typeable c => Associative a b c
associative = induct associativeZ associativeS

data CommuteZRight a = CommuteZRight {
      getCommuteZRight :: Proxy a -> (a :+: Z) :~: a
    }

commuteZRightZ :: CommuteZRight Z
commuteZRightZ = CommuteZRight $ \_ -> Refl

commuteZRightS :: forall a. CommuteZRight a -> CommuteZRight (S a)
commuteZRightS recurse = CommuteZRight $ \_ -> cong (getCommuteZRight recurse (Proxy @a))

commuteZRight :: Typeable a => CommuteZRight a
commuteZRight = induct commuteZRightZ commuteZRightS

data CommuteSRight b a = CommuteSRight {
      getCommuteSRight :: Proxy a -> Proxy b -> (a :+: S b) :~: S (a :+: b)
    }

commuteSRightZ :: CommuteSRight a Z
commuteSRightZ = CommuteSRight $ \_ _ -> Refl

commuteSRightS :: forall a b . CommuteSRight a b -> CommuteSRight a (S b)
commuteSRightS recurse = CommuteSRight $ \_ a -> cong $ getCommuteSRight recurse (Proxy @b) a

commuteSRight :: Typeable b => CommuteSRight a b
commuteSRight = induct commuteSRightZ commuteSRightS

data Commutative a b = Commutative {
      getCommute :: Proxy a -> Proxy b -> (a :+: b) :~: (b :+: a)
    }


commutativeZ :: Typeable a => Commutative a Z
commutativeZ = Commutative $ \a _ -> case getCommuteZRight commuteZRight a of
                                       Refl -> Refl

commutativeS :: forall a b . Typeable a => Commutative a (S b)
commutativeS = Commutative $ \a _ -> case getCommuteSRight commuteSRight a (Proxy @b) of

commutative :: (Typeable a, Typeable b) => Commutative a b
commutative = induct commutativeZ (const commutativeS)


data a :<=: b where
    LTE :: Proxy p -> (a :+: p :~: b) -> a :<=: b

symmetricLT :: forall a . (Typeable a) => a :<=: a
symmetricLT = LTE (Proxy @Z) $ getCommuteZRight commuteZRight Proxy

transitiveLT :: forall a b c . (Typeable a) => a :<=: b -> b :<=: c -> a :<=: c
transitiveLT (LTE (Proxy :: Proxy a') Refl) (LTE (Proxy :: Proxy b') Refl) = LTE (Proxy @(a' :+: b')) $
  getAssociate associative (Proxy @a) (Proxy @a') (Proxy @b')


data Typeable' :: TyFun k Constraint -> * where
  Typeable' :: Typeable' a

type instance Apply Typeable' a = Typeable a

type OrderedN = CategoryP Typeable' (:<=:)

nCat :: OrderedN
nCat = Category symmetricLT (flip transitiveLT)
