module Naturals where

import Prelude hiding ((.), id)

import Classy hiding ((:+:))

import Data.Constraint

import Data.Type.Equality

data N = Z | S N

data SNat (n :: N) where
    SZ :: SNat 'Z
    SS :: SNat n -> SNat ( 'S n )

class KnownNat n where
    singNat :: SNat n

instance KnownNat 'Z where
    singNat = SZ

instance KnownNat n => KnownNat ('S n) where
    singNat = SS singNat

type family x :+: y  where
    'Z :+: y = y
    ('S x) :+: y = 'S (x :+: y)

(+:) :: SNat a -> SNat b -> SNat (a :+: b)
SZ +: y = y
SS x +: y = SS (x +: y)

data SBool (a :: Bool) where
    STrue :: SBool 'True
    SFalse :: SBool 'False

type family a :=: b where
    'Z :=: 'Z = 'True
    ('S a) :=: ('S b) = a :=: b
    a :=: b = 'False

(=:) :: SNat a -> SNat b -> SBool (a :=: b)
SZ =: SZ = STrue
(SS a) =: (SS b) = a =: b
SZ =: (SS _) = SFalse
(SS _) =: SZ = SFalse

(==:) :: SNat a -> SNat b -> Maybe (a :~: b)
SZ ==: SZ = Just Refl
(SS a) ==: (SS b) = case a ==: b of
                      Just Refl -> Just Refl
                      Nothing -> Nothing
_ ==: _ = Nothing


induct' :: forall z a p . (KnownNat a, KnownNat z) => p z -> (forall n . p n -> p ('S n)) -> p a
induct' baseCase inductionCase = case singNat @z ==: singNat @a of
  Just Refl -> baseCase
  Nothing -> induct' (inductionCase baseCase) inductionCase


induct :: forall a p . (KnownNat a) => p 'Z -> (forall n . p n -> p ('S n)) -> p a
induct = induct' @'Z

cong :: (a :~: b) -> ('S a :~: 'S b)
cong Refl = Refl


data Associative c b a = Associative {
      getAssociate :: (a :+: (b :+: c)) :~: ((a :+: b) :+: c)
    }

associativeZ :: Associative c b 'Z
associativeZ = Associative $ Refl

associativeS :: forall c b a . Associative c b a -> Associative c b ('S a)
associativeS recurse = Associative . cong $ getAssociate recurse

associative :: KnownNat c => Associative a b c
associative = induct associativeZ associativeS


data CommuteZRight a = CommuteZRight {
      getCommuteZRight :: (a :+: 'Z) :~: a
    }

commuteZRightZ :: CommuteZRight 'Z
commuteZRightZ = CommuteZRight Refl

commuteZRightS :: forall a. CommuteZRight a -> CommuteZRight ('S a)
commuteZRightS recurse = CommuteZRight $ cong (getCommuteZRight recurse)

commuteZRight :: KnownNat a => CommuteZRight a
commuteZRight = induct commuteZRightZ commuteZRightS


data CommuteSRight b a = CommuteSRight {
      getCommuteSRight :: (a :+: 'S b) :~: 'S (a :+: b)
    }

commuteSRightZ :: CommuteSRight a 'Z
commuteSRightZ = CommuteSRight Refl

commuteSRightS :: forall a b . CommuteSRight a b -> CommuteSRight a ('S b)
commuteSRightS recurse = CommuteSRight . cong $ getCommuteSRight recurse

commuteSRight :: KnownNat b => CommuteSRight a b
commuteSRight = induct commuteSRightZ commuteSRightS


data Commutative a b = Commutative {
      getCommute :: (a :+: b) :~: (b :+: a)
    }


commutativeZ :: forall a . KnownNat a => Commutative a 'Z
commutativeZ = Commutative $ case getCommuteZRight (commuteZRight @a) of
                               Refl -> Refl

commutativeS :: forall a b . KnownNat a => Commutative a ('S b)
commutativeS = Commutative $ case getCommuteSRight (commuteSRight @a) of

commutative :: (KnownNat a, KnownNat b) => Commutative a b
commutative = induct commutativeZ (const commutativeS)


data a :<=: b where
    LTE :: (KnownNat a, KnownNat b) => SNat p -> (a :+: p :~: b) -> a :<=: b

type instance Hom = (:<=:)

symmetricLT :: forall a . (KnownNat a) => a :<=: a
symmetricLT = LTE SZ $ getCommuteZRight commuteZRight


transitiveLT :: forall a b c . (KnownNat a) => a :<=: b -> b :<=: c -> a :<=: c
transitiveLT (LTE (a' :: SNat a') Refl) (LTE (b' :: SNat b') Refl) = LTE (a' +: b') $
  getAssociate (associative @a @b' @a')


instance Category (:<=:) where
    type Prop a = KnownNat a

    a . b = case (observe a, observe b) of
              (Dict, Dict) -> transitiveLT b a

    id =  symmetricLT

    observe (LTE _ _) = Dict
