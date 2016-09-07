module Category where

import Prelude hiding (Functor, fmap, id, Monoid, Monad)
import qualified Prelude as Prelude

import qualified Data.Monoid as M

import Data.Kind

import Data.Functor.Identity
import Data.Function (fix)

import GHC.Exts

type Hask = (->)

-- Basically ignore from here:
data TyFun :: * -> * -> *
type a ~> b = TyFun a b -> *
infixr 0 ~>

type family Apply (f :: k1 ~> k2) (x :: k1) :: k2

type family Const x y where
    Const x _ = x

data Const' :: k1 -> TyFun k2 k1 -> * where
    Const' :: Const' k1 k2

type instance Apply (Const' x) y = Const x y

type EmptyConstraint = (() :: Constraint)

data CategoryP p c = Category { getId :: forall a . Apply p a => c a a
                              , getDot :: forall r s t . (Apply p r, Apply p s, Apply p t) => c s t -> c r s -> c r t
                              }

-- To here.

type Category = CategoryP (Const' EmptyConstraint)

hask :: Category Hask
hask = Category (\x -> x) (.)

data Isomorphism c a b = Isomorphism { isoGetCategory :: Category c
                                     , getFrom :: c a b
                                     , getTo :: c b a
                                     }


data Terminal c t = Terminal { terminalGetCategory :: Category c
                             , terminate :: forall a . c a t
                             }


haskTerminal :: Terminal Hask ()
haskTerminal = Terminal hask (\_ -> ())

data Initial c i = Initial { initialGetCategory :: Category c
                           , initiate :: forall a . c i a
                           }

data Void


haskInital :: Initial Hask Void
haskInital = Initial hask (\v -> case v of)

data Bifunctor l r t f = Bifunctor { bifunctorGetLeftCategory :: Category l
                                   , bifunctorGetRightCategory :: Category r
                                   , bifunctorGetTargetCategory :: Category t
                                   , bimap :: forall a b x y . l a b -> r x y -> t (f a x) (f b y)
                                   }

type Biendofunctor c = Bifunctor c c c

eitherBifunctor :: Biendofunctor Hask Either
eitherBifunctor = Bifunctor hask hask hask $ \f g e -> case e of
                                                         Left x -> Left (f x)
                                                         Right y -> Right (g y)
pairBifunctor :: Biendofunctor Hask (,)
pairBifunctor = Bifunctor hask hask hask $ \f g (a, b) -> (f a, g b)

data Monoidal c p u = Monoidal { getMonoidalCategory :: Category c
                               , getMonoidalBiendofunctor :: Biendofunctor c p
                               , getLeftUnitor :: forall a . Isomorphism c (p u a) a
                               , getRightUnitor :: forall a . Isomorphism c (p a u) a
                               , getAssociativity :: forall x y z . Isomorphism c (p x (p y z)) (p (p x y) z)
                               }


monoidalHask :: Monoidal Hask (,) ()
monoidalHask = Monoidal hask pairBifunctor
               (Isomorphism hask
                            snd
                            (\a -> ((), a)))
               (Isomorphism hask
                            fst
                            (\a -> (a, ())))
               (Isomorphism hask
                            (\(x, (y, z)) -> ((x, y), z))
                            (\((x, y), z) -> (x, (y, z))))

data Monoid c p u m = Monoid { getMonoidal :: Monoidal c p u
                             , getMultiplication :: c (p m m) m
                             , getUnit :: c u m
                             }

haskMonoid :: M.Monoid m => Monoid Hask (,) () m
haskMonoid = Monoid monoidalHask (uncurry M.mappend) (const M.mempty)


data Products c p  = Products { getProductsCategory :: Category c
                              , inL :: forall a b. c (p a b) a
                              , inR :: forall a b. c (p a b) b
                              , ump :: forall a b z. c z a -> c z b -> c z (p a b)
                              }

haskProducts :: Products Hask (,)
haskProducts = Products hask fst snd $ \f g z -> (f z, g z)

data Functor s t f = Functor { functorGetSourceCategory :: Category s
                             , functorGetTargetCategory :: Category t
                             , fmap :: forall a b . s a b -> t (f a) (f b)
                             }

type Endofunctor c = Functor c c

type HaskFunctor = Endofunctor Hask

haskFunctor :: Prelude.Functor f => Functor Hask Hask f
haskFunctor = Functor hask hask Prelude.fmap

maybeFunctor :: Endofunctor Hask Maybe
maybeFunctor = Functor hask hask $ \f m -> case m of
                                             Nothing -> Nothing
                                             Just a -> Just (f a)

data Compose s t u f g a = Compose { getOuterFunctor :: Functor t u f
                                   , getInnerFunctor :: Functor s t g
                                   , getCompose :: f (g a) -- TODO: write in terms of identity arrow so that `u`
                                                           -- doesn't need to have kind `* -> * -> *`
                                   }

type HaskCompose = Compose Hask Hask Hask

composeFunctor :: Category s -> Functor s Hask (Compose s t Hask f g)
composeFunctor sCat = Functor sCat hask $ \f -> \(Compose o@(Functor _ _ outer) i@(Functor _ _ inner) fg) -> Compose o i (outer (inner f) fg)

composeFunctorHask :: Endofunctor Hask (Compose Hask t Hask f g)
composeFunctorHask = composeFunctor hask

splitOuterFunctor :: Endofunctor Hask (HaskCompose f g) -> Endofunctor Hask f
splitOuterFunctor (Functor _ _ fgMap) = Functor hask hask $
                                        \f ->
                                        let Compose (Functor _ _ fmap) _ _ = fgMap f (error "not implemented")
                                        in fmap f

splitInnerFunctor :: Endofunctor Hask (HaskCompose f g) -> Endofunctor Hask g
splitInnerFunctor (Functor _ _ fgMap) = Functor hask hask $
                                        \f ->
                                        let Compose _ (Functor _ _ gmap) _ = fgMap f (error "not implemented")
                                        in gmap f

splitComposeFunctor :: Endofunctor Hask (HaskCompose f g) -> (Endofunctor Hask f, Endofunctor Hask g)
splitComposeFunctor func = (splitOuterFunctor func, splitInnerFunctor func)

type Trans f g = forall a . f a -> g a

data Nat c d f g = Nat { getTargetCategory :: Category d
                       , getTrans :: forall a . d (f a) (g a)
                       , getFunctorProof :: Functor c d f -> Functor c d g
                       }

type (:~>) = Nat Hask Hask

type (:<~>) = Isomorphism (:~>)

haskNat :: (Prelude.Functor g) => Trans f g -> f :~> g
haskNat nat = Nat hask (\(fa) -> (nat fa)) (\_ -> haskFunctor)


natCategory :: Category d -> Category (Nat c d)
natCategory catD = Category (Nat catD (getId catD) (getId hask))
              (\(Nat _ x p1) (Nat _ y p2) -> Nat catD (getDot catD x y) (p1 . p2))



natHaskCategory :: Category (:~>)
natHaskCategory = natCategory hask


bifunctorCompose :: Biendofunctor (:~>) HaskCompose
bifunctorCompose = Bifunctor natHaskCategory natHaskCategory natHaskCategory $
                   \(Nat _ betaNat betaProof) (Nat _ alphaNat alphaProof) -> Nat hask
                   (\(Compose o@(Functor _ _ outerFmap) i fg) ->
                     Compose (betaProof o) (alphaProof i) (betaNat (outerFmap alphaNat fg))
                   )
                   (const composeFunctorHask)


listToMaybe :: [] :~> Maybe
listToMaybe = haskNat safeHead
    where safeHead :: [a] -> Maybe a
          safeHead [] = Nothing
          safeHead (x : _) = Just x


natLeftUnitor :: HaskFunctor f -> (HaskCompose Identity f) :<~> f
natLeftUnitor f = Isomorphism natHaskCategory
                (Nat hask (\(Compose _ _ (Identity fa)) -> fa) (const f))
                (Nat hask (\fa -> Compose haskFunctor f (Identity fa)) (const composeFunctorHask))


natRightUnitor :: HaskFunctor f -> (HaskCompose f Identity) :<~> f
natRightUnitor f@(Functor _ _ fmap) = Isomorphism natHaskCategory
                 (Nat hask (\(Compose fFunc@(Functor _ _ fmap) _ fia) -> (fmap runIdentity fia)) (const f))
                 (Nat hask (\fa -> Compose f haskFunctor (fmap Identity fa)) (const composeFunctorHask))


natAssociativity :: (HaskCompose f (HaskCompose g h)) :<~> (HaskCompose (HaskCompose f g) h)
natAssociativity = Isomorphism natHaskCategory
                   (Nat hask
                    (\(Compose fFunc@(Functor _ _ fmap) ghFunc fgh) ->
                      let unwrapped = fmap getCompose fgh
                          (gFunc, hFunc) = splitComposeFunctor ghFunc
                      in Compose composeFunctorHask hFunc (Compose fFunc gFunc  unwrapped))
                    (const composeFunctorHask))
                   (Nat hask
                     (\(Compose fgFunc hFunc@(Functor _ _ hmap) (Compose fFunc@(Functor _ _ fmap) gFunc fgh)) ->
                      let wrapped = fmap (Compose gFunc hFunc) fgh
                      in Compose fFunc composeFunctorHask wrapped)
                     (const composeFunctorHask))


natMonoidal :: Monoidal (:~>) HaskCompose Identity
natMonoidal = Monoidal natHaskCategory bifunctorCompose (natLeftUnitor _what_do) (natRightUnitor _blegh) natAssociativity

data Monad m = Monad { getMonadFunctor :: HaskFunctor m
                     , getReturn :: forall a . a -> m a
                     , getBind :: forall a b . m a -> (a -> m b) -> m b
                     }


haskMonad :: Prelude.Monad m => Monad m
haskMonad = Monad haskFunctor return (>>=)


monadToMonoid :: forall m . Monad m -> Monoid (:~>) HaskCompose Identity m
monadToMonoid (Monad func return bind) = Monoid natMonoidal
            (Nat hask (join . getCompose) (const func))
            (Nat hask (return . runIdentity) (const func))
    where join :: m (m a) -> m a
          join mma = bind mma $ getId hask

monoidToMonad :: Monoid (:~>) HaskCompose Identity m -> Monad m
monoidToMonad (Monoid monoidal (Nat _ mult _) (Nat _ unit functorProof)) = Monad mFunc (unit . Identity) (\ma f -> mult (Compose mFunc mFunc (mmap f ma)))
    where mFunc@(Functor _ _ mmap) = functorProof haskFunctor
