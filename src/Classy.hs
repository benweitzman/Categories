{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Classy where

import Prelude hiding (Functor, fmap, id, Monoid, Monad, (.), id)
import qualified Prelude as P
import qualified Data.Monoid as P
import qualified Control.Monad as P

import Data.Constraint

import Data.Kind

import GHC.Exts

class Category (c :: k -> k -> Type) where
  type Prop c (a :: k) :: Constraint
  type Prop c a = ()

  id :: Prop c a => c a a

  (.) :: c y z -> c x y -> c x z

  observe :: c a b -> Dict (Prop c a, Prop c b)
  default observe :: (Prop c a ~ (() :: Constraint), Prop c b ~ (() :: Constraint))
                  => c a b -> Dict (Prop c a, Prop c b)
  observe _ = Dict


instance Category (->) where
  id = P.id
  (.) = (P..)

data Isomorphism c a b where
  Iso :: (Category c, Prop c a, Prop c b) =>
         { isoTo :: c a b
         , isoFrom :: c b a
         } -> Isomorphism c a b




instance Category c => Category (Isomorphism c) where
  type Prop (Isomorphism c) a = Prop c a
  id = Iso id id
  (Iso a y) . (Iso b x) = case (observe a, observe b, observe y, observe x) of
    (Dict, Dict, Dict, Dict) -> Iso (a . b) (x . y)

  observe (Iso to _) = observe to


class (Category c) => HasTerminal (c :: k -> k -> *) where
  type Terminal c :: k

  terminate :: c a (Terminal c)


instance HasTerminal (->) where
  type Terminal (->) = ()

  terminate _ = ()


class (Category c) => HasInitial (c :: k -> k -> *) where
  type Initial c :: k

  initiate :: c (Initial c) a


data Void

instance HasInitial (->) where
  type Initial (->) = Void

  initiate v = case v of


class (Category (Dom f), Category (Cod f)) => Functor (f :: j -> k) where
  type Cod f :: k -> k -> *
  type Dom f :: j -> j -> *

  fmap :: Dom f a b -> Cod f (f a) (f b)


ob :: forall f a . Functor f => Prop (Dom f) a :- Prop (Cod f) (f a)
ob = Sub $ case observe (fmap (id :: Dom f a a) :: Cod f (f a) (f a)) of
  Dict -> Dict


newtype Prelude f a = Prelude { unPrelude :: f a } deriving Show

instance P.Functor f => Functor (Prelude f) where
  type Cod (Prelude f) = (->)
  type Dom (Prelude f) = (->)

  fmap f (Prelude fa) =  Prelude $ P.fmap f fa



class (Category (Left p), Category (Right p), Category (Target p)) => Bifunctor (p :: j -> k -> l) where
  type Left p :: j -> j -> *
  type Right p :: k -> k -> *
  type Target p :: l -> l -> *

  bimap :: Left p a b -> Right p x y -> Target p (p a x) (p b y)

left :: (Bifunctor p, Prop (Right p) c) => Left p a b -> Target p (p a c) (p b c)
left f = bimap f id


right :: (Bifunctor p, Prop (Left p) a) => Right p b c -> Target p (p a b) (p a c)
right f = bimap id f

instance Bifunctor Either where
  type Left Either = (->)
  type Right Either = (->)
  type Target Either = (->)

  bimap lf _ (Left l) = Left (lf l)
  bimap _ rf (Right r) = Right (rf r)

instance Bifunctor (,) where
  type Left (,) = (->)
  type Right (,) = (->)
  type Target (,) = (->)

  bimap lf rf (l, r) = (lf l, rf r)


type Biendofunctor f = (Bifunctor f, Left f ~ Right f, Right f ~ Target f)


class (Category c, Biendofunctor (Tensor c)) => Monoidal (c :: k -> k -> *) where
  type Tensor c :: k -> k -> k
  type Unit c :: k

  leftUnitor :: (Prop c a) => Isomorphism c ((Tensor c) (Unit c) a) a

  rightUnitor :: (Prop c a) => Isomorphism c ((Tensor c) a (Unit c)) a

  associator :: (Prop c z, Prop c x, Prop c y)
             => Isomorphism c ((Tensor c) x ((Tensor c) y z)) ((Tensor c) (Tensor c x y) z)


instance Monoidal (->) where
  type Tensor (->) = (,)
  type Unit (->) = ()

  leftUnitor = Iso snd (\a -> ((), a))

  rightUnitor = Iso fst (\a -> (a, ()))

  associator = Iso (\(x, (y, z)) -> ((x, y), z))
                   (\((x, y), z) -> (x, (y, z)))


class (Monoidal c, Prop c m, Prop c (Unit c)) => Monoid c m where
  mult :: c (Tensor c m m) m
  unit :: c (Unit c) m

instance (P.Monoid m) => Monoid (->) m where
  mult (x, y) = x `P.mappend` y
  unit _ = P.mempty


data (:+:) f g a = Compose { unCompose :: (f (g a)) } deriving Show

instance (Functor g, Functor f, Cod f ~ (->), Cod g ~ Dom f) => Functor (f :+: g) where
  type Dom (f :+: g) = Dom g
  type Cod (f :+: g) = Cod f

  fmap f = Compose . fmap (fmap f) . unCompose

type FunctorOf c d f = (Functor f, Dom f ~ c, Cod f ~ d)

data (:~>) c d f g where
  Nat :: (FunctorOf c d f, FunctorOf c d g) =>
         (forall a . Prop c a => d (f a) (g a)) -> (c :~> d) f g

instance (Category c, Category d) => Category (c :~> d) where
  type Prop (c :~> d) f = FunctorOf c d f

  id = Nat id1 where
    id1 :: forall f x . (FunctorOf c d f, Prop c x) => d (f x) (f x)
    id1 = id \\ (ob @f @x :: Prop c x :- Prop d (f x))

  (Nat a) . (Nat b) = Nat (a . b)

  observe (Nat _) = Dict


-- todo, generalize
instance Bifunctor ((:+:) :: (Type -> Type) -> (Type -> Type) -> Type -> Type) where
  type Left (:+:) = (->) :~> (->)
  type Right (:+:) = (->) :~> (->)
  type Target (:+:) = (->) :~> (->)

  bimap (Nat lf) (Nat rf) = Nat $
    \(Compose ax) -> Compose $
    lf (fmap rf ax)

data Identity a = Identity { unIdentity :: a }

instance Functor Identity where
  type Dom Identity = (->)
  type Cod Identity = (->)

  fmap f (Identity a) = Identity (f a)



instance Monoidal ((->) :~> (->)) where
  type Tensor ((->) :~> (->)) = (:+:)
  type Unit ((->) :~> (->)) = Identity

  leftUnitor = Iso (Nat $ unIdentity . unCompose)
                   (Nat $ Compose . Identity)

  rightUnitor = Iso (Nat $ fmap unIdentity . unCompose)
                    (Nat $ Compose . fmap Identity)

  associator = Iso (Nat $ Compose . Compose . fmap unCompose . unCompose)
                   (Nat $ Compose . fmap Compose . unCompose . unCompose)


type Monad m = Monoid ((->) :~> (->)) m



instance (FunctorOf (->) (->) m, P.Monad m) => Monoid ((->) :~> (->)) m where
  mult = Nat $ P.join . unCompose

  unit = Nat $ P.return . unIdentity

instance (Monoid ((->) :~> (->)) m) => P.Functor m where
  fmap f fa = fmap f fa

instance (Monoid ((->) :~> (->)) m) => P.Applicative m where
  pure a = case (unit :: ((->) :~> (->)) Identity m)of
    Nat f -> f (Identity a)

  mf <*> ma = let bind :: m a -> (a -> m b) -> m b
                  bind m f = case (mult :: ((->) :~> (->)) (m :+: m) m) of
                    Nat join -> join . Compose $ fmap f m
              in bind mf (\f -> bind ma (\a -> pure $ f a))

instance (Monoid ((->) :~> (->)) m) => P.Monad m where
  m >>= f = case (mult :: ((->) :~> (->)) (m :+: m) m) of
    Nat join -> join . Compose $ fmap f m
