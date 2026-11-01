module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.TCB.Arm.Isa

/-! # The shared RSA scratch requirement fits the ARMv7 workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem pc_dimensions {k len : Nat} (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (space : Spec.Rsa.publicScratchWords k ≤ len) :
    2 ≤ Spec.Rsa.modulusWords k ∧ Spec.Rsa.modulusWords k < 2 ^ 31 ∧
      arrAt (Spec.Rsa.modulusWords k) 8 ≤ 8 * len ∧
      k ≤ 8 * Spec.Rsa.modulusWords k ∧ 128 * Spec.Rsa.modulusWords k < 2 ^ 32 := by
  simp only [Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords, arrAt, Proof.Rsa.Mont.hdrBytes] at *
  omega

theorem rsa_bytes_frame {regions : List Region} {m m' : Mem} {src : Addr} {k : Nat}
    (frame : Frame regions m m') (fit : k < 2 ^ 64)
    (sep : ∀ r ∈ regions, (⟨src, k⟩ : Region).Disjoint r) :
    Spec.Rsa.bytesAt m' src k = Spec.Rsa.bytesAt m src k :=
  VG.Proof.Rsa.rsa_bytes_frame frame fit sep

end VG.Proof.Bignum.Arm
