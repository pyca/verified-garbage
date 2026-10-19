module
public import VerifiedGarbage.Proof.MlKem.AArch64.KgCommon
import VerifiedGarbage.Impl.MlKem.AArch64.Noise


/-! # One fused key-generation row with a precomputed error polynomial -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay}

def rowTerms (P : KemLay) (i : Nat) : List (Nat × Nat) :=
 (List.range P.k).map fun j => (aOff P i j,sOff P j)

def rowWrites (P : KemLay) (s₀ : State) (i : Nat) : List Region :=
 [R (kA s₀) 3 (TP P) 1024,R (kA s₀) 1 (384*i) 384,R (kA s₀) 2 (384*P.k+384*i) 384]

end VG.Proof.MlKem.AArch64.KeyGen
