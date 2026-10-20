module
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
import VerifiedGarbage.Impl.MlKem.AArch64.Noise
import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon


/-! # One fused ciphertext row using retained noise -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay} {L : Layout}

def uTerms (P : KemLay) (i : Nat) : List (Nat × Nat) :=
  (List.range P.k).map fun j => (aOff P j i,yOff P j)

end VG.Proof.MlKem.AArch64.Kem
