module PropositionalEquality

import Interfaces

Reflexive (=) where
  refl = Refl

Coreflexive (=) where
  corefl = id

Symmetric (=) where
  symm Refl = Refl

Antisymmetric (=) where
  antisymm Refl _ = Refl

Transitive (=) where
  trans Refl prf = prf

Euclidean (=) where
  eucl Refl prf = prf

Preorder (=) where

Equivalence (=) where

PartialOrder (=) where
