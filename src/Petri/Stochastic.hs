{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

-- | A stochastic petri net is a petri net with rate constants for every transition.  See: https://math.ucr.edu/home/baez/structured_vs_decorated/structured_vs_decorated_companions_web.pdf
-- TODO: This will be more efficient if we lean on linear algebra and use morphisms in VectK by building a "vector field representation"
-- of the transition matrix.  This amounts to building the representation of the graph in a matrix of edges and computing rates and updates using BLAS primatives.
-- See: https://github.com/AlgebraicJulia/AlgebraicPetri.jl/blob/91535bd5aea8b8bbc3de25d1c7b55071017c1801/src/AlgebraicPetri.jl#L256-L264
-- We can do this using HMatix if we don't care about cross compilation to JS or we can maybe use massiv if we do, tbd.
module Petri.Stochastic
  ( toStocastic,
    runPetriMorphism,
    foldMapNeighbors,
    foldNeighborsEndo,
    sirNet,
    PetriNode,
    Stochastic (..),
    SIR (..),
    debug,
  )
where

import Algebra.Graph.AdjacencyMap
  ( AdjacencyMap (..),
    edges,
  )
import Data.Bifunctor (Bifunctor (bimap))
import qualified Data.Map as Map
import qualified Data.Map.Monoidal.Strict as MMap
import Data.Maybe (fromMaybe)
import Data.Monoid (Endo (..), Sum (..))
import qualified Data.Set as Set
import Debug.Trace (trace)
import GHC.Generics (Generic)

-- | Nodes in the graph will either be Places or Transitions
data PetriNode p t = Place p | Transition t
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

instance Bifunctor PetriNode where
  bimap f _ (Place p) = Place $ f p
  bimap _ f (Transition p) = Transition $ f p

-- | A stochastic petri net is defined by graph of nodes an a rate function.
-- TODO:  It may in some cases also be defined by multiple edges between two nodes. Dunno what semanticcs are required here.
data Stochastic p t r = Stochastic
  { net :: AdjacencyMap (PetriNode p t),
    rate :: r -> t -> r -> r
  }

-- | Our basic algorithm needs to move over the graph and propagate values from source nodes to target nodes.
-- it also needs to remove values from the source nodes but only at the end of the walk over the graph.
-- Now, we could update values as we walk over graph but this would mean we would need to walk the whole
-- structure each time we want to simulate initial values.  Instead, we walk the struccture once and return
-- a function that can be called with initial values.  This is the @Endo@ type, which is a mondoid that
-- composes functions for it's `mappend` and does `id` for mempty.
-- >>> let k = (MMap.fromList $ [(S, 1), (I, 1), (R, 0)])
-- >>> let j = (MMap.fromList $ [(S, 0), (I, -1), (R, -1)])
-- >>> let a = (PetriMorphism . Endo $ \(a, b) -> (a <> k, b))
-- >>> let b = (PetriMorphism . Endo $ \(a, b) -> (a , b <> j))
-- >>> runPetriMorphism (mconcat [mempty, a, mempty, b, mempty]) (MMap.fromList $ [(S, -2), (I, 0), (R, 2)])
-- MonoidalMap {getMonoidalMap = fromList [(S,Sum {getSum = -1}),(I,Sum {getSum = 0}),(R,Sum {getSum = 1})]}
newtype PetriMorphism p b = PetriMorphism
  { unPetriMorphism ::
      Endo
        ( MMap.MonoidalMap p (Sum b),
          MMap.MonoidalMap p (Sum b),
          MMap.MonoidalMap p (Sum b)
        )
  }
  deriving stock (Generic)
  deriving newtype (Monoid, Semigroup)

-- | Run a PetriMorphism with some initial values.  Note that we only combine the updates after the whole graph is composed.
runPetriMorphism :: (Ord p, Num b) => PetriMorphism p b -> MMap.MonoidalMap p (Sum b) -> MMap.MonoidalMap p (Sum b)
runPetriMorphism (PetriMorphism endo) initialValues = source <> target
  where
    (source, target, _) = appEndo endo (mempty, mempty, initialValues)

for :: [a] -> (a -> b) -> [b]
for = flip fmap

-- | Debug prints
debug :: c -> String -> c
debug = flip trace

-- | This is like @foldMap@ except will walk our graph and bail once everything has been seen.
foldMapNeighbors ::
  (Ord p, Ord t, Show p, Show t) =>
  AdjacencyMap (PetriNode p t) ->
  Set.Set (PetriNode p t, PetriNode p t) ->
  PetriNode p t ->
  (PetriMorphism p b -> (PetriNode p t, PetriNode p t, PetriNode p t) -> PetriMorphism p b) ->
  PetriMorphism p b
foldMapNeighbors net' seen start f =
  case Map.lookup start (adjacencyMap net') of
    Nothing -> mempty
    Just transitions -> foldMap (<> mempty) $
      for (Set.toList transitions) $
        \transition -> case Map.lookup transition (adjacencyMap net') of
          Nothing -> mempty
          Just targets -> foldMap (<> mempty) $
            for (Set.toList targets) $ \target ->
              if Set.member (start, target) seen
                then mempty
                else
                  let recurse =
                        foldMapNeighbors
                          net'
                          (Set.singleton (start, target) <> seen)
                          target
                          f
                   in f recurse (start, transition, target)

-- | compute the updates given a source, target, and rate function.
computeUpdates ::
  (Ord p, Num b) =>
  (b -> t -> b -> b) ->
  PetriNode p t ->
  PetriNode p t ->
  PetriNode p t ->
  PetriMorphism p b
computeUpdates rateFn (Place source) (Transition t') (Place target) = PetriMorphism . Endo $ \(sourceUpdate, targetUpdate, initialValues) ->
  let source' = fromMaybe mempty . MMap.lookup source $ initialValues
      target' = fromMaybe mempty . MMap.lookup target $ initialValues
      rateConst = rateFn (getSum source') t' (getSum target')
      targetUpdate' = MMap.singleton target (fmap (rateConst *) source')
      sourceUpdate' = MMap.singleton source (fmap (negate . (rateConst *)) source')
   in (sourceUpdate' <> sourceUpdate, targetUpdate <> targetUpdate', initialValues)
computeUpdates _ _ _ _ = mempty

-- | The fold that applies the above Endos
foldNeighborsEndo ::
  (Ord p, Ord t, Num r, Show p, Show t) =>
  Stochastic p t r ->
  p ->
  PetriMorphism p r
foldNeighborsEndo stochasticNet start = foldMapNeighbors net' seen (Place start) f
  where
    seen = mempty
    net' = net stochasticNet
    f acc (source, transition, target) =
      let !acc' = computeUpdates (rate stochasticNet) source transition target
       in acc <> acc' -- N.B the order of mappending matters!

toStocastic ::
  (Ord p, Ord t) =>
  (r -> t -> r -> r) ->
  [(PetriNode p t, PetriNode p t)] ->
  Stochastic p t r
toStocastic rateFn netEdges = Stochastic (edges netEdges) rateFn

-- | The SIR model
data SIR = S | I | R
  deriving stock (Eq, Ord, Show, Enum, Bounded)

s :: PetriNode SIR t
s = Place S

i :: PetriNode SIR t
i = Place I

r :: PetriNode SIR t
r = Place R

data R = R_1 | R_2
  deriving stock (Eq, Ord, Show, Enum, Bounded)

r_1 :: PetriNode p R
r_1 = Transition R_1

r_2 :: PetriNode p R
r_2 = Transition R_2

sirEdges :: [(PetriNode SIR R, PetriNode SIR R)]
sirEdges =
  [ (s, r_1),
    (r_1, i),
    (i, r_1),
    (i, r_2),
    (r_2, r)
  ]

-- | Define a SIR model given two rates
-- >>> let r_1 = 0.02
-- >>> let r_2 = 0.05
-- >>> let net = sirNet r_1 r_2
-- >>> let kont = foldNeighborsEndo net S
-- >>> let inits = (MMap.fromList $ [(S, Sum 0.99), (I, Sum 0.01), (R, 0)])
-- >>> let t1 = runPetriMorphism kont inits
-- >>> let t2 = runPetriMorphism kont (t1 <> inits)
-- >>> let t3 = runPetriMorphism kont (t2 <> t1 <> inits)
-- >>> show t1
-- >>> show t2
-- >>> show t3
-- "MonoidalMap {getMonoidalMap = fromList [(S,Sum {getSum = -1.9602e-4}),(I,Sum {getSum = 1.8602e-4}),(R,Sum {getSum = 1.0e-5})]}"
-- "MonoidalMap {getMonoidalMap = fromList [(S,Sum {getSum = -1.9958730398756031e-4}),(I,Sum {getSum = 1.8921180364352033e-4}),(R,Sum {getSum = 1.0375500344040002e-5})]}"
-- "MonoidalMap {getMonoidalMap = fromList [(S,Sum {getSum = -2.032127873982716e-4}),(I,Sum {getSum = 1.9244824390033798e-4}),(R,Sum {getSum = 1.0764543497933596e-5})]}"
sirNet :: (Num r, Eq r) => r -> r -> Stochastic SIR R r
sirNet r1 r2 = toStocastic rateFn sirEdges
  where
    rateFn source R_1 target
      | target == 0 = 0
      | source == 0 = 0
      | otherwise = 2 * r1 * target * source
    rateFn source R_2 _ = source * r2

-- >>> test
-- MonoidalMap {getMonoidalMap = fromList [(S,Sum {getSum = -1.9602e-4}),(I,Sum {getSum = 1.8602e-4}),(R,Sum {getSum = 1.0e-5})]}
test :: MMap.MonoidalMap SIR (Sum Double)
test =
  let r_1 = 0.02
      r_2 = 0.05
      net = sirNet r_1 r_2
      kont = foldNeighborsEndo net S
   in runPetriMorphism kont (MMap.fromList [(S, Sum 0.99), (I, Sum 0.01), (R, Sum 0)])
