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
{-
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

data TyCon :: (a -> b) -> a ~> b where

type instance Apply (TyCon f) x = f x

-}

data Const a b = Const a

data Category p c = Category { getId :: forall a . p a -> c a a
                             , getDot :: forall r s t . c s t -> c r s -> c r t
                             , getObserve :: forall a b . c a b -> (p a, p b)
                             }

-- To here.

swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

type Vacuous = Const ()

type Category' = Category Vacuous

vacuous :: Vacuous a
vacuous = Const ()

hask :: Category' Hask
hask = Category (\_ x -> x) (.) (\_ -> (vacuous, vacuous))


data Dual c a b = Dual { getDual :: c b a }

dualCategory :: Category p c -> Category p (Dual c)
dualCategory (Category idIf dot observe) = Category
  (Dual . idIf)
  (\(Dual a) (Dual b) -> Dual (b `dot` a))
  (swap  . observe . getDual)


data Isomorphism p c a b = Isomorphism { getIsoCategory :: Category p c
                                       , getIsoPropFrom :: p a
                                       , getIsoPropTo :: p b
                                       , getIsoForward :: c a b
                                       , getIsoBackward :: c b a
                                       }


isomorphismCat :: Category p c -> Category p (Isomorphism p c)
isomorphismCat cat@(Category idIf dot observe) = Category
  (\pa -> Isomorphism cat pa pa (idIf pa) (idIf pa))
  (\(Isomorphism _ ps pt a y) (Isomorphism _ pr _ b x) -> Isomorphism cat pr pt (a `dot` b) (x `dot` y))
  (\(Isomorphism _ pa pb _ _) -> (pa, pb))


data Terminal p c t = Terminal { getTerminalCategory :: Category p c
                               , getTerminalProp :: p t
                               , getTerminate :: forall a . c a t
                               }


haskTerminal :: Terminal Vacuous Hask ()
haskTerminal = Terminal hask vacuous (\_ -> ())


data Initial p c i = Initial { getInitialCategory :: Category p c
                             , getInitialProp :: p i
                             , getInitiate :: forall a . c i a
                             }

data Void


haskInital :: Initial Vacuous Hask Void
haskInital = Initial hask vacuous (\v -> case v of)


data Bifunctor pl l pr r pt t f = Bifunctor { bifunctorGetLeftCategory :: Category pl l
                                            , bifunctorGetRightCategory :: Category pr r
                                            , bifunctorGetTargetCategory :: Category pt t
                                            , bimap :: forall a b x y . l a b -> r x y -> t (f a x) (f b y)
                                            }

type Biendofunctor p c = Bifunctor p c p c p c


eitherBifunctor :: Biendofunctor Vacuous (->) Either
eitherBifunctor = Bifunctor hask hask hask $ \f g e -> case e of
                                                         Left x -> Left (f x)
                                                         Right y -> Right (g y)
pairBifunctor :: Biendofunctor Vacuous (->) (,)
pairBifunctor = Bifunctor hask hask hask $ \f g (a, b) -> (f a, g b)



constBifunctor :: Biendofunctor Vacuous (->) Const
constBifunctor = Bifunctor hask hask hask $ \f g (Const a) -> Const (f a)



data Monoidal p c x u = Monoidal { getMonoidalCategory :: Category p c
                                 , getMonoidalBiendofunctor :: Biendofunctor p c x
                                 , getLeftUnitor :: forall a . Isomorphism p c (u `x` a) a
                                 , getRightUnitor :: forall a . Isomorphism p c (a `x` u) a
                                 , getAssociativity :: forall r s t . Isomorphism p c (r `x` (s `x` t)) ((r `x` s) `x` t)
                                 }


monoidalHask :: Monoidal Vacuous (->) (,) ()
monoidalHask = Monoidal hask pairBifunctor
               (Isomorphism hask
                            vacuous
                            vacuous
                            snd
                            (\a -> ((), a)))
               (Isomorphism hask
                            vacuous
                            vacuous
                            fst
                            (\a -> (a, ())))
               (Isomorphism hask
                            vacuous
                            vacuous
                            (\(x, (y, z)) -> ((x, y), z))
                            (\((x, y), z) -> (x, (y, z))))


data Monoid p c x u m = Monoid { getMonoidal :: Monoidal p c x u
                               , getMultiplication :: c (m `x` m) m
                               , getUnit :: c u m
                               }

haskMonoid :: M.Monoid m => Monoid Vacuous (->) (,) () m
haskMonoid = Monoid monoidalHask (uncurry M.mappend) (const M.mempty)



data Products p c x  = Products { getProductsCategory :: Category p c
                                , inL :: forall a b. c (a `x` b) a
                                , inR :: forall a b. c (a `x` b) b
                                , ump :: forall a b z. c z a -> c z b -> c z (a `x` b)
                                }

haskProducts :: Products Vacuous (->) (,)
haskProducts = Products hask fst snd $ \f g z -> (f z, g z)


{-
monoidalProduct :: forall p c x u . Monoidal p c x u -> Terminal p c u -> Products p c x
monoidalProduct
  (Monoidal cat@(Category idIf dot observe)
                (Bifunctor _ _ _ bimap)
                (Isomorphism _ _ _ takeR putR)
                (Isomorphism _ _ _ takeL putL)
                _
  )
  (Terminal _ _ terminate) =
    Products
    cat
    (takeL `dot` bimap (idIf _) terminate)
    undefined
    undefined
-}

{-
    (takeL `dot` bimap id terminate)
    (takeR `dot` bimap terminate id)
    (\za zb ->
       let x = putR `dot` zb
           y = putL `dot` za
           q = bimap za zb
       in _)
-}

{-
type CoProducts c p = Products (Dual c) p

haskCoproducts :: CoProducts Hask Either
haskCoproducts = Products (dualCategory hask) (Dual Left) (Dual Right) $ \(Dual az) (Dual bz) -> Dual (either az bz)

data Functor s t f = Functor { functorGetSourceCategory :: Category s
                             , functorGetTargetCategory :: Category t
                             , map :: forall a b . s a b -> t (f a) (f b)
                             }

class IsFunctor s t f | f -> s, f -> t where
  getFunctor :: Functor s t f


type Endofunctor c = Functor c c

type HaskFunctor = Endofunctor Hask

haskFunctor :: Prelude.Functor f => Functor Hask Hask f
haskFunctor = Functor hask hask Prelude.fmap

maybeFunctor :: Endofunctor Hask Maybe
maybeFunctor = Functor hask hask $ \f m -> case m of
                                             Nothing -> Nothing
                                             Just a -> Just (f a)

data Compose s t u f g a where
  Compose :: (IsFunctor t u f, IsFunctor s t g) =>
             { getCompose :: f (g a) -- TODO: write in terms of identity arrow so that `u`
                                     -- doesn't need to have kind `* -> * -> *`
             } -> Compose s t u f g a

type HaskCompose = Compose Hask Hask Hask

type f :.: g = HaskCompose f g


composeFunctor :: Category s -> Functor s Hask (Compose s t Hask f g)
composeFunctor sCat = Functor sCat hask $ \f -> \(Compose fg) ->
  let Functor _ _ outer = getFunctor
      Functor _ _ inner = getFunctor
  in Compose (outer (inner f) fg)


composeFunctorHask :: HaskFunctor (Compose Hask t Hask f g)
composeFunctorHask = composeFunctor hask

{-
splitOuterFunctor :: HaskFunctor (f :.: g) -> HaskFunctor f
splitOuterFunctor (Functor _ _ fgMap) = Functor hask hask $
                                        \f ->
                                        let Compose (Functor _ _ fmap) _ _ = fgMap f (error "not implemented")
                                        in fmap f

splitInnerFunctor :: HaskFunctor (f :.: g) -> HaskFunctor g
splitInnerFunctor (Functor _ _ fgMap) = Functor hask hask $
                                        \f ->
                                        let Compose _ (Functor _ _ gmap) _ = fgMap f (error "not implemented")
                                        in gmap f

splitComposeFunctor :: HaskFunctor (f :.: g) -> (HaskFunctor f, HaskFunctor g)
splitComposeFunctor func = (splitOuterFunctor func, splitInnerFunctor func)
-}

type Trans f g = forall a . f a -> g a

data Nat c d f g where
  Nat :: (IsFunctor c d f, IsFunctor c d g) =>
         { getTargetCategory :: Category d
         , getTrans :: forall a . d (f a) (g a)
         } -> Nat c d f g

type (:~>) = Nat Hask Hask

type (:<~>) = Isomorphism (:~>)


instance Prelude.Functor g => IsFunctor Hask Hask g where
  getFunctor = haskFunctor



haskNat :: (Prelude.Functor f, Prelude.Functor g) => Trans f g -> f :~> g
haskNat nat = Nat hask (\(fa) -> (nat fa))


natCategory :: Category d -> CategoryP (TyCon (IsFunctor c d)) (Nat c d)
natCategory catD = Category (Nat catD (getId catD))
                   (\(Nat _ x) (Nat _ y) -> Nat catD (getDot catD x y))

type NatHaskCategory = CategoryP (TyCon (IsFunctor Hask Hask)) (:~>)

natHaskCategory :: NatHaskCategory
natHaskCategory = natCategory hask

{-
bifunctorCompose :: Biendofunctor (:~>) HaskCompose
bifunctorCompose = Bifunctor natHaskCategory natHaskCategory natHaskCategory $
                   \(Nat _ betaNat) (Nat _ alphaNat) -> Nat hask
                   (\(Compose fg) ->
                     Compose (betaNat (outerFmap alphaNat fg))
                   )


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

natAssociate :: (f :.: (g :.: h)) :~> ((f :.: g) :.: h)
natAssociate = Nat hask
               (\(Compose fFunc@(Functor _ _ fmap) ghFunc fgh) ->
                  let unwrapped = fmap getCompose fgh
                      (gFunc, hFunc) = splitComposeFunctor ghFunc
                  in Compose composeFunctorHask hFunc (Compose fFunc gFunc  unwrapped))
                    (const composeFunctorHask)

natAssociativity :: (HaskCompose f (HaskCompose g h)) :<~> (HaskCompose (HaskCompose f g) h)
natAssociativity = Isomorphism natHaskCategory
                   natAssociate
                   (Nat hask
                     (\(Compose fgFunc hFunc@(Functor _ _ hmap) (Compose fFunc@(Functor _ _ fmap) gFunc fgh)) ->
                      let wrapped = fmap (Compose gFunc hFunc) fgh
                      in Compose fFunc composeFunctorHask wrapped)
                     (const composeFunctorHask))


natMonoidal :: Monoidal (:~>) HaskCompose Identity
natMonoidal = Monoidal natHaskCategory bifunctorCompose (natLeftUnitor (error "what goes here")) (natRightUnitor (error "what goes here")) natAssociativity

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
-}
-}
