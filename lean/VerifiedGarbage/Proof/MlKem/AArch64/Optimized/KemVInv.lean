module
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc

/-! # Encryption after the consumed matrix may be reused for decoded keys -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}

/-- A region apart from what `VInv` describes. -/
def VFar (P : KemLay) (L : Layout) (s₀ : State) (kC co nY nU : Nat) (r : Region) : Prop :=
  (R (kA s₀) L.sc RB 32).Disjoint r ∧ (R (kA s₀) L.sc MB 32).Disjoint r ∧
    (R (kA s₀) L.sc (YH P) (1024 * nY)).Disjoint r ∧
    (R (kA s₀) (L.slot kC) co (32 * P.du * nU)).Disjoint r ∧ ∃ r' ∈ encW P L s₀ kC co, Region.Sub r r'

theorem Far.vfar {s₀ : State} {kC co nY nU : Nat} {r : Region}
    (h : Far P L s₀ kC co nY nU r) : VFar P L s₀ kC co nY nU r :=
  ⟨h.1,h.2.1,h.2.2.2⟩

end VG.Proof.MlKem.AArch64.Kem
