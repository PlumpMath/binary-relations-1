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

Coherent NatLe where
  cohe {x = Z} = Dir ZA
  cohe {y = Z} = Inv ZA
  cohe {x = S k} {y = S j} = case the (Cohe NatLe k j) cohe of
    Dir prf => Dir (SS prf)
    Inv prf => Inv (SS prf)

WeakCoherent NatLe where
  wcohe {x = Z} {y = Z} contra = void (contra Refl)
  wcohe {x = Z} _ = Dir ZA
  wcohe {y = Z} _ = Inv ZA
  wcohe {x = S k} {y = S j} contra = let contra = contra . cong in
    case the (Cohe NatLe k j) (wcohe contra) of
      Dir prf => Dir (SS prf)
      Inv prf => Inv (SS prf)

Connexive NatLe where
  conx {x = Z} {y = Z} = Left Refl
  conx {x = Z} = Right (Dir ZA)
  conx {y = Z} = Right (Inv ZA)
  conx {x = S k} {y = S j} = case the (Either (k = j) (Cohe NatLe k j)) conx of
    Left Refl => Left Refl
    Right (Dir prf) => Right (Dir (SS prf))
    Right (Inv prf) => Right (Inv (SS prf))

PartialOrder NatLe where
