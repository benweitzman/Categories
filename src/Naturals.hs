module Naturals where

import Classy hiding ((:+:))

import Data.Constraint

import Data.Type.Equality
import Data.Typeable

import Data.Proxy

import Data.Kind
import GHC.Exts

data N = Z | S N

data SNat (n :: N) where
    SZ :: SNat 'Z
    SS :: SNat n -> SNat ( 'S n )

type family x :+: y  where
    Z :+: y = y
    (S x) :+: y = S (x :+: y)

(+:) :: SNat a -> SNat b -> SNat (a :+: b)
SZ +: y = y
SS x +: y = SS (x +: y)

data SBool (a :: Bool) where
    STrue :: SBool 'True
    SFalse :: SBool 'False

type family a :=: b where
    Z :=: Z = True
    (S a) :=: (S b) = a :=: b
    a :=: b = False

(=:) :: SNat a -> SNat b -> SBool (a :=: b)
SZ =: SZ = STrue
(SS a) =: (SS b) = a =: b
SZ =: (SS _) = SFalse
(SS _) =: SZ = SFalse


induct' :: forall (z :: N) a p . (Typeable a, Typeable z) => p z -> (forall n . p n -> p (S n)) -> p a
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
    LTE :: (Typeable a, Typeable b) => Proxy p -> (a :+: p :~: b) -> a :<=: b

type instance Hom = (:<=:)

symmetricLT :: forall a . (Typeable a) => a :<=: a
symmetricLT = LTE (Proxy @Z) $ getCommuteZRight commuteZRight Proxy

transitiveLT :: forall a b c . (Typeable a) => a :<=: b -> b :<=: c -> a :<=: c
transitiveLT (LTE (Proxy :: Proxy a') Refl) (LTE (Proxy :: Proxy b') Refl) = LTE (Proxy @(a' :+: b')) $
  getAssociate associative (Proxy @a) (Proxy @a') (Proxy @b')


instance Category (:<=:) where
    type Prop a = Typeable a

    a . b = case (observe a, observe b) of
              (Dict, Dict) -> transitiveLT b a

    id =  symmetricLT

    observe (LTE _ _) = Dict
