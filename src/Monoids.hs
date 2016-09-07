{-# LANGUAGE RankNTypes #-}

module Monoids where

import Data.Monoid

reduce :: (Monoid a, Monoid b, Eq a, Eq b) => [Either a b] -> [Either a b]
reduce [] = []
reduce (x : xs) | x == Left mempty || x == Right mempty = reduce xs
reduce ((Left x) : (Left y) : zs) = reduce $ Left (x <> y) : zs
reduce ((Right x) : (Right y) : zs) = reduce $ Right (x <> y) : zs
reduce (x : xs) = x : reduce xs
