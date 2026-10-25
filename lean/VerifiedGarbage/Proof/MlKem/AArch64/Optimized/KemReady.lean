module

import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Ready
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DotSpec
import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
public import Init.Data.List.Basic
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Field

/-! # The terms of the fused dot product of `ŝ` and `û'` and their sum -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

def decodedTerms (P : KemLay) : List (Nat × Nat) :=
  (List.range P.k).map fun j => (aOff P 0 j,yOff P j)

def decodedF (T : Nat → Poly) (fg : Nat × Nat) : Poly := T ((fg.1-AH)/1024)
def decodedG (P : KemLay) (Y : Nat → Poly) (fg : Nat × Nat) : Poly := Y ((fg.2-YH P)/1024)

theorem decoded_sum (T Y : Nat → Poly) :
    Dot.polySum (decodedTerms P) (decodedF T) (decodedG P Y)=KPke.dotK T Y P.k := by
  apply Optimized.polySum_dotK
  · intro j hj; simp [decodedF,aOff]
  · intro j hj; simp [decodedG,yOff]

end VG.Proof.MlKem.AArch64.Kem
