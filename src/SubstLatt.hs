{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
module SubstLatt where

import           Control.Applicative
import           Control.Monad                     (unless)
import           Data.Graph.Inductive
import           Data.Graph.Inductive.Graph
import qualified Data.Graph.Inductive.Graph        as Graph
import           Data.Graph.Inductive.NodeMap
import           Data.Graph.Inductive.PatriciaTree
import qualified Data.GraphViz                     as GV
import           Data.List                         (nub, nubBy)
import           Data.Partition
import qualified Data.Partition                    as Partition
import           Data.Set                          (singleton, toList)

{-# ANN module "HLint: ignore Use mappend" #-}
{-# ANN module "HLint: ignore Use fmap" #-}

-------------------------------------------------------------

type G = Gr (Partition Int) (Int,Int)

-- all join pairs (assuming input list is sorted and uniq)
joinPairs []     = []
joinPairs [_]    = []
joinPairs (x:xs) = [(x,y) | y<-xs] ++ joinPairs xs

type M t = NodeMapM (Partition Int) (Int,Int) Gr t

-- join the partition containging i and the partition continaing j
addJoinFrom :: Partition Int -> (Int,Int) -> M (LNode (Partition Int))
addJoinFrom p (i,j) = do
  ln <- insMapNodeM p'
  insMapEdgeM (p,p',(i,j))
  return ln
  where p' = joinElems i j p


instance GV.Labellable (Int,Int) where
  toLabelValue (i,j) = GV.toLabelValue (show i ++ "=" ++ show j)

instance GV.Labellable (Partition Int) where
  toLabelValue p = GV.toLabelValue (show $  toList <$> Partition.nontrivialSets p)


mkPartitionLattice :: Int -> (NodeMap (Partition Int), G)
mkPartitionLattice n = snd . run g0 $ addFromFix p0
  where

  maxVal = n - 1

  p0 = fromDisjointSets (fmap singleton [0..maxVal])

  (g0,_,_) = insMapNode new p0 Graph.empty

  -- generate all possible partitions from p by a single join pair
  -- and add them to the graph and nodemap
  -- join pairs are generated from representative elem of each partition
  addFrom :: Partition Int -> M [LNode (Partition Int)]
  addFrom p = do
    lnodes <- mapM (addJoinFrom p) $ joinPairs (nub $ map (rep p) [0..maxVal])
    return $ nubBy (\x y -> fst x == fst y) lnodes

  -- repeatedly apply addFrom to newly geneated partitions
  -- until there are no more partitions to generate
  addFromFix :: Partition Int -> M ()
  addFromFix p = do
    lnodes <- addFrom p
    unless (null lnodes) $
      sequence_ [addFromFix p' | (_,p')<- lnodes]


-- kind of works up to 5
-- from 6 preview isn't meaningful becuase state space is too large
-- from 7 it seg faults before even going to preview
someFunc :: Int -> IO ()
-- main = someFunc
someFunc n = do
  -- generate all substititions that equates variables in size n set
  -- where the elements are numberd as 0,1,2,3,..,n-1
  let (nmap,g) = mkPartitionLattice n
  print nmap
  print g
  GV.preview g
