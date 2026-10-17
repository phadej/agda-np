module README where

------------------------------------------------------------------------
-- agda-np library

-- A specialised version of Data.List.Relation.Unary.Any: bare proof that an element is an the list.
import Data.Idx

-- A reimplemetation of Data.List.Relation.Unary.All; like NP from Haskell's sop-core.
import Data.NP

-- Weakenings / thinnings / order preserving embeddings.
import Data.NP.Wk

-- Cover xys xs ys is an evidence that xys is (order preserving) inteleaving of xs and ys.
import Data.List.Cover

------------------------------------------------------------------------
-- examples

-- normalisation-by-evaluation of simply typed lambda calculus
import Examples.STLC

-- linear logic using Cover
import Example.ILL
