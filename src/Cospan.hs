{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Cospan where

import Algebra.Graph.AdjacencyMap (AdjacencyMap, compose, gmap)
import Data.Biapplicative (Bifunctor)
import Data.Bifunctor (Bifunctor (bimap, first))
import Data.List (nub)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.These (These (..))
import GHC.Generics (Generic)
import Petri.Stochastic (PetriNode, Stochastic (Stochastic))

-- | An Cospan `x` is just the x and
-- functions to pick out the inputs and outputs at the boundary of `x`
data Cospan x y z = Cospan
  { -- | The apex object x
    apex :: x,
    -- | The input leg
    input :: x -> y,
    -- | The output leg
    output :: x -> z
  }
  deriving stock (Generic, Functor)

-- | An OpenStochastic net is a petri net with two "legs" that form it's inputs and outputs
type OpenStochastic p t r = Cospan (Stochastic p t r) [p] [p]

mergeThem :: (Ord p', Ord p) => Map p p' -> Map p' p -> Either p p' -> These p p'
mergeThem mp _ (Left p) =
  case Map.lookup p mp of
    Nothing -> This p
    Just p' -> These p p'
mergeThem _ mp' (Right p') = case Map.lookup p' mp' of
  Nothing -> That p'
  Just p -> These p p'

gmapBimap ::
  (Ord (p a c), Ord (p b d), Bifunctor p) =>
  (a -> b) ->
  (c -> d) ->
  AdjacencyMap (p a c) ->
  AdjacencyMap (p b d)
gmapBimap f g = gmap (bimap f g)

legPushforward ::
  (Eq p, Eq p') =>
  (Either p p' -> These p p') ->
  Stochastic p t r ->
  Stochastic p' t' r ->
  (Stochastic p t r -> [p]) ->
  (Stochastic p' t' r -> [p']) ->
  (Stochastic (These p p') (Either t t') r -> [These p p'])
legPushforward merge' xL xR legL legR = const pushforward
  where
    legL' = Left <$> legL xL
    legR' = Right <$> legR xR
    pushforward = nub $ (merge' <$> legL') <> (merge' <$> legR')

-- | Horizontal composition of OpenStochastic petri nets. The resuting net is glued together using `Either` for transitions
-- and `These` for places since some places will be merged in the legs.
composeH ::
  forall p t p' t' r.
  (Ord p, Ord p', Ord t, Ord t') =>
  -- | The list of places that should be merged:  Since places are different types here, we need to know which pairs should "plugged" together in a composition.  Most likely these will be pairs of input / output places.
  [(p, p')] ->
  -- | The left
  OpenStochastic p t r ->
  -- | The right
  OpenStochastic p' t' r ->
  OpenStochastic (These p p') (Either t t') r
composeH toMerge (Cospan apeL iL oL) (Cospan apeR iR oR) = pushforward
  where
    (Stochastic netL rateL) = apeL
    (Stochastic netR rateR) = apeR
    mp = Map.fromList toMerge
    mp' = Map.fromList $ fmap (\(a, b) -> (b, a)) toMerge
    mergeThem' = mergeThem mp mp'
    netL' = gmapBimap Left Left netL
    netR' = gmapBimap Right Right netR
    netPushForward = gmap @_ @(PetriNode (These p p') (Either t t')) (first mergeThem') (compose netL' netR')
    ratePushforward s (Left ts) t = rateL s ts t
    ratePushforward s (Right ts) t = rateR s ts t
    iPushForward = legPushforward mergeThem' apeL apeR iL iR
    oPushForward = legPushforward mergeThem' apeL apeR oL oR
    pushforward = Cospan (Stochastic netPushForward ratePushforward) iPushForward oPushForward