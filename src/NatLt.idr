module NatLt

import Interfaces

%default total
%access public export

data NatLt : Nat -> Nat -> Type where
  ZS : NatLt Z (S _)
  SS : NatLt x y -> NatLt (S x) (S y)

Uninhabited (NatLt _ Z) where
  uninhabited ZS impossible
  uninhabited (SS _) impossible

Irreflexive NatLt where
  irrefl (SS prf) = irrefl prf

Asymmetric NatLt where
  asymm (SS pf1) (SS pf2) = asymm pf1 pf2

Transitive NatLt where
  trans ZS (SS _) = ZS
  trans (SS pf1) (SS pf2) = SS (trans pf1 pf2)

-- FIXME
private
wcohe' : (x, y : Nat) -> (x = y -> Void) -> Cohe NatLt x y
wcohe' Z Z contra = void (contra Refl)
wcohe' Z (S _) _ = ?wcohe'_rhs_4
wcohe' (S _) Z _ = ?wcohe'_rhs_1
wcohe' (S k) (S j) contra = case wcohe' k j (contra . cong) of
  Dir prf => Dir (SS prf)
  Inv prf => Inv (SS prf)

WeakCoherent NatLt where
  wcohe {x} {y} = wcohe' x y

-- FIXME
private
conx' : (x, y : Nat) -> Either (x = y) (Cohe NatLt x y)
conx' x y with (decEq x y)
  conx' _ _ | (Yes prf) = Left prf
  conx' x y | (No contra) = Right (wcohe contra)

Connexive NatLt where
  conx {x} {y} = conx' x y
