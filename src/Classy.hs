{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Classy where

import Prelude hiding (Functor, fmap, id, Monoid, Monad(..), (.), id)
import qualified Prelude as P
import qualified Control.Monad as P

import Data.Constraint

import Data.Kind



type family Hom :: i -> i -> Type
type instance Hom = (->)
type instance Hom = (:~>)

type Cat k = k -> k -> Type

type HasCat k = Category (Hom :: Cat k)

type (~>) = (Hom :: i -> i -> Type)

class (c ~ Hom) => Category (c :: k -> k -> Type) where
  type Prop (a :: k) :: Constraint
  type Prop a = ()

  id :: Prop a => c a a

  (.) :: c y z -> c x y -> c x z

  observe :: c a b -> Dict (Prop a, Prop b)
  default observe :: (Prop a ~ (() :: Constraint), Prop b ~ (() :: Constraint))
                  => c a b -> Dict (Prop a, Prop b)
  observe _ = Dict

instance Category (->) where
  id = P.id
  (.) = (P..)

data Isomorphism c a b where
  Iso :: (Category c, Prop a, Prop b) =>
         { isoTo :: c a b
         , isoFrom :: c b a
         } -> Isomorphism c a b


{-
instance Category c => Category (Isomorphism c) where
  type Prop (Isomorphism c) a = Prop c a
  id = Iso id id
  (Iso a y) . (Iso b x) = case (observe a, observe b, observe y, observe x) of
    (Dict, Dict, Dict, Dict) -> Iso (a . b) (x . y)

  observe (Iso to _) = observe to
-}

class (HasCat k) => Terminal (t :: k) where
  terminate :: a ~> t


instance Terminal () where
  terminate _ = ()


class (HasCat k) => Initial (i :: k) where
  initiate :: i ~> a


data Void

instance Initial Void where
  initiate v = case v of

class (HasCat j, HasCat k) => Functor (f :: j -> k) where
  fmap :: a ~> b -> f a ~> f b


ob :: forall f a . Functor f => Prop a :- Prop (f a)
ob = Sub $ case observe (fmap (id :: a ~> a) :: (f a) ~> (f a)) of
  Dict -> Dict


newtype Prelude f a = Prelude { unPrelude :: f a } deriving Show

instance P.Functor f => Functor (Prelude f) where
  fmap f (Prelude fa) =  Prelude $ P.fmap f fa


class (HasCat j, HasCat k, HasCat l) => Bifunctor (p :: j -> k -> l) where
  bimap :: (a ~> b) -> (x ~> y) -> (p a x ~> p b y)

left :: (Bifunctor p, Prop c) => a ~> b -> (p a c) ~> (p b c)
left f = bimap f id


right :: (Bifunctor p, Prop a) => b ~> c -> (p a b) ~> (p a c)
right f = bimap id f

instance Bifunctor Either where
  bimap lf _ (Left l) = Left (lf l)
  bimap _ rf (Right r) = Right (rf r)

instance Bifunctor (,) where
  bimap lf rf (l, r) = (lf l, rf r)


type Biendofunctor (f :: k -> k -> k) = (Bifunctor f)

class (Category c, Biendofunctor ((**) :: k -> k -> k)) => Monoidal (c :: k -> k -> *) where
  type (**) :: k -> k -> k
  type Unit :: k

  leftUnitor :: (Prop a) => Isomorphism c (Unit ** a) a

  rightUnitor :: (Prop a) => Isomorphism c (a ** Unit) a

  associator :: (Prop z, Prop x, Prop y)
             => Isomorphism c (x ** (y ** z)) ((x ** y) ** z)

instance Monoidal (->) where
  type (**) = (,)
  type Unit = ()

  leftUnitor = Iso snd (\a -> ((), a))

  rightUnitor = Iso fst (\a -> (a, ()))

  associator = Iso (\(x, (y, z)) -> ((x, y), z))
                   (\((x, y), z) -> (x, (y, z)))


class (Monoidal (Hom :: Cat k), Prop m, Prop (Unit :: k)) => Monoid (m :: k) where
  mult :: (m ** m) ~> m
  unit :: Unit ~> m

instance (P.Monoid m) => Monoid m where
  mult (x, y) = x `P.mappend` y
  unit _ = P.mempty


data (:+:) f g a = Compose { unCompose :: (f (g a)) } deriving Show

instance (Functor g, Functor f) => Functor (f :+: g) where
  fmap f = Compose . fmap (fmap f) . unCompose


data (:~>) (f :: i -> j) (g :: i -> j) where
  Nat :: (Functor f, Functor g) =>
         (forall a . Prop a => f a ~> g a) -> f :~> g

instance Category (:~>) where
  type Prop f = Functor f

  id = Nat id1 where
    id1 :: forall f x . (Functor f, Prop x) => (f x) ~> (f x)
    id1 = id \\ (ob @f @x :: Prop x :- Prop (f x))

  (Nat a) . (Nat b) = Nat (a . b)

  observe (Nat _) = Dict


instance Bifunctor (:+:) where

   bimap :: forall a b x y . (a ~> b) -> (x ~> y) -> (a :+: x) ~> (b :+: y)
   bimap (Nat lf) (Nat rf) = Nat f

    where
      f :: forall q . (Prop q) => (a :+: x) q ~> (b :+: y) q
      f = case observe (rf :: x q ~> y q) of
            Dict -> Compose . lf . fmap rf . unCompose



data Identity a = Identity { unIdentity :: a }

instance Functor Identity where
  fmap f (Identity a) = Identity (f a)


instance Monoidal ((:~>) :: Cat (Type -> Type)) where
  type (**) = (:+:)
  type Unit = Identity

  leftUnitor = Iso (Nat $ unIdentity . unCompose)
                   (Nat $ Compose . Identity)

  rightUnitor = Iso (Nat $ fmap unIdentity . unCompose)
                    (Nat $ Compose . fmap Identity)

  associator = Iso (Nat $ Compose . Compose . fmap unCompose . unCompose)
                   (Nat $ Compose . fmap Compose . unCompose . unCompose)


class Monoid m => Monad (m :: i -> i) where
    return :: Unit a ~> m a
    join  :: m (m a) ~> m a

instance Monoid m => Monad (m :: * -> *) where
    return :: Identity a -> m a
    return = let Nat u = unit in u

    join :: m (m a) -> m a
    join = let Nat x = mult in x . Compose

instance (Functor m, P.Monad m) => Monoid m where
  mult = Nat $ P.join . unCompose

  unit = Nat $ P.return . unIdentity


instance (Monoid m) => P.Functor (Prelude m) where
  fmap f (Prelude fa) = Prelude (fmap f fa)


instance (Monoid m) => P.Applicative (Prelude m) where
  pure a = case (unit :: Identity :~> m) of
    Nat f -> Prelude $ f (Identity a)

  (Prelude mf) <*> (Prelude ma) =
   let bind :: m a -> (a -> m b) -> m b
       bind m f = join $ fmap f m
   in Prelude $ bind mf (\f -> bind ma (\a -> return . Identity $ f a))

instance (Monoid m) => P.Monad (Prelude m) where
  (Prelude m) >>= f = Prelude $ join $ fmap (unPrelude . f) m
