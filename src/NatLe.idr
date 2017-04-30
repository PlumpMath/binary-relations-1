module NatLe

import Interfaces

%default total
%access public export

data NatLe : Nat -> Nat -> Type where
  ZA : NatLe Z _
  SS : NatLe x y -> NatLe (S x) (S y)

Uninhabited (NatLe (S _) Z) where
  uninhabited ZA impossible
  uninhabited (SS _) impossible

Reflexive NatLe where
  refl {x = Z} = ZA
  refl {x = S x} = SS (refl {x})

Antisymmetric NatLe where
  antisymm ZA ZA = Refl
  antisymm (SS prf) (SS frp) = cong (antisymm prf frp)

Transitive NatLe where
  trans ZA _ = ZA
  trans (SS pf1) (SS pf2) = SS (trans pf1 pf2)

-- FIXME
private
cohe' : (x, y : Nat) -> Cohe NatLe x y
cohe' Z _ = Dir ZA
cohe' _ Z = Inv ZA
cohe' (S k) (S j) = case cohe' k j of
  Dir prf => Dir (SS prf)
  Inv prf => Inv (SS prf)

Coherent NatLe where
  cohe {x} {y} = cohe' x y

-- FIXME
private
wcohe' : (x, y : Nat) -> (x = y -> Void) -> Cohe NatLe x y
wcohe' Z Z contra = void (contra Refl)
wcohe' Z (S _) _ = Dir ZA
wcohe' (S _) Z _ = Inv ZA
wcohe' (S k) (S j) contra = case wcohe' k j (contra . cong) of
  Dir prf => Dir (SS prf)
  Inv prf => Inv (SS prf)

WeakCoherent NatLe where
  wcohe {x} {y} = wcohe' x y

-- FIXME
private
conx' : (x, y : Nat) -> Either (x = y) (Cohe NatLe x y)
conx' Z Z = Left Refl
conx' Z (S _) = Right (Dir ZA)
conx' (S _) Z = Right (Inv ZA)
conx' (S k) (S j) = case conx' k j of
  Left Refl => Left Refl
  Right (Dir prf) => Right (Dir (SS prf))
  Right (Inv prf) => Right (Inv (SS prf))

Connexive NatLe where
  conx {x} {y} = conx' x y

PartialOrder NatLe where
