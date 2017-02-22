{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeInType #-}

module Classy where

import Prelude hiding (Functor, fmap, id, Monoid, Monad(..), (.), id)
import qualified Prelude as P
import qualified Control.Monad as P

import Data.Constraint
import Data.Constraint.Forall

import Data.Kind

class Category k where
  type Prop (a :: k) :: Constraint
  type Prop a = ()

  type (~>) :: k -> k -> Type

  id :: forall (a :: k) . Prop a => a ~> a

  (.) :: forall (x :: k) (y :: k) (z :: k) . y ~> z -> x ~> y -> x ~> z

  observe :: forall (a :: k) (b :: k) . a ~> b -> Dict (Prop a, Prop b)
  default observe :: forall (a :: k) (b :: k) .
                     (Prop a ~ (() :: Constraint), Prop b ~ (() :: Constraint))
                  => a ~> b -> Dict (Prop a, Prop b)
  observe _ = Dict

instance Category Type where
  type (~>) = (->)

  id = P.id
  (.) = (P..)

data Isomorphism a b where
  Iso :: forall (a :: k) (b :: k) . (Category k, Prop a, Prop b) =>
         { isoTo :: a ~> b
         , isoFrom :: b ~> a
         } -> Isomorphism a b



{-
instance (Category k, Forall (Same :: Proxy k -> Constraint)) => Category (Proxy k) where
  type Prop ('Proxy a) = Prop a

  type (~>) = Isomorphism

  id :: forall (a :: Proxy k) . (Prop a) => Isomorphism a a
  id = case (inst :: Forall Same :- Same a) of
         Sub Dict -> Iso (id :: Unproxy a ~> Unproxy a) _

  (Iso a y) . (Iso b x) = case (observe a, observe b, observe y, observe x) of
    (Dict, Dict, Dict, Dict) -> Iso (a . b) (x . y)

  observe (Iso to _) = observe to
-}


class (Category k) => Terminal (t :: k) where
  terminate :: a ~> t


instance Terminal () where
  terminate _ = ()


class (Category k) => Initial (i :: k) where
  initiate :: i ~> a


data Void

instance Initial Void where
  initiate v = case v of

class (Category j, Category k) => Functor (f :: j -> k) where
  fmap :: a ~> b -> f a ~> f b


ob :: forall f a . Functor f => Prop a :- Prop (f a)
ob = Sub $ case observe (fmap (id :: a ~> a) :: (f a) ~> (f a)) of
  Dict -> Dict


newtype Prelude f a = Prelude { unPrelude :: f a } deriving Show

instance P.Functor f => Functor (Prelude f) where
  fmap f (Prelude fa) =  Prelude $ P.fmap f fa


class (Category j, Category k, Category l) => Bifunctor (p :: j -> k -> l) where
  bimap :: (a ~> b) -> (x ~> y) -> (p a x ~> p b y)

left :: (Bifunctor p, Prop c) => (a ~> b) -> (p a c ~> p b c)
left f = bimap f id


right :: (Bifunctor p, Prop a) => (b ~> c) -> (p a b ~> p a c)
right f = bimap id f

instance Bifunctor Either where
  bimap lf _ (Left l) = Left (lf l)
  bimap _ rf (Right r) = Right (rf r)

instance Bifunctor (,) where
  bimap lf rf (l, r) = (lf l, rf r)


type Biendofunctor (f :: k -> k -> k) = (Bifunctor f)


class (Category k, Biendofunctor ((**) :: k -> k -> k)) => Monoidal k where
  type (**) :: k -> k -> k
  type Unit :: k

  leftUnitor :: forall (a :: k) . (Prop a) => Isomorphism (Unit ** a) a

  rightUnitor :: forall (a :: k) . (Prop a) => Isomorphism (a ** Unit) a

  associator :: forall (x :: k) (y :: k) (z :: k) .
                (Prop z, Prop x, Prop y)
             => Isomorphism (x ** (y ** z)) ((x ** y) ** z)

instance Monoidal Type where
  type (**) = (,)
  type Unit = ()

  leftUnitor = Iso snd (\a -> ((), a))

  rightUnitor = Iso fst (\a -> (a, ()))

  associator = Iso (\(x, (y, z)) -> ((x, y), z))
                   (\((x, y), z) -> (x, (y, z)))



class (Monoidal k, Prop m, Prop (Unit :: k)) => Monoid (m :: k) where
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

instance Category (i -> j) where
  type Prop f = Functor f

  type (~>) = (:~>)

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


instance Monoidal (Type -> Type) where
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
