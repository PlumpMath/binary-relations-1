module Interfaces

%default total
%access public export

interface Reflexive (R : m -> m -> Type) where
  refl : x `R` x

interface Irreflexive (R : m -> m -> Type) where
  irrefl : x `R` x -> Void

interface Coreflexive (R : m -> m -> Type) where
  corefl : x `R` y -> x = y

interface Symmetric (R : m -> m -> Type) where
  symm : x `R` y -> y `R` x

interface Antisymmetric (R : m -> m -> Type) where
  antisymm : x `R` y -> y `R` x -> x = y

interface Asymmetric (R : m -> m -> Type) where
  asymm : x `R` y -> y `R` x -> Void

interface Transitive (R : m -> m -> Type) where
  trans : x `R` y -> y `R` z -> x `R` z

interface Euclidean (R : m -> m -> Type) where
  eucl : x `R` y -> x `R` z -> y `R` z

data Cohe : (R : m -> m -> Type) -> (x, y : m) -> Type where
  Dir : {R : m -> m -> Type} -> (prf : x `R` y) -> Cohe R x y
  Inv : {R : m -> m -> Type} -> (prf : y `R` x) -> Cohe R x y

interface Coherent (R : m -> m -> Type) where
  cohe : Cohe R x y

interface WeakCoherent (R : m -> m -> Type) where
  wcohe : {x, y : m} -> (x = y -> Void) -> Cohe R x y

interface Connexive (R : m -> m -> Type) where
  conx : Either (x = y) (Cohe R x y)

interface (Reflexive R, Transitive R)
  => Preorder (R : m -> m -> Type)

interface (Reflexive R, Symmetric R, Transitive R)
  => Equivalence (R : m -> m -> Type)

interface (Reflexive R, Antisymmetric R, Transitive R)
  => PartialOrder (R : m -> m -> Type)

interface (Irreflexive R, Antisymmetric R, Transitive R)
  => Order (R : m -> m -> Type)
