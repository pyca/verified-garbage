module

public import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
public import VerifiedGarbage.Spec.Rsa.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The shared RSA scratch requirement fits the ARMv7 workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm
open VG.Spec.Rsa.Mont (arrAt)

theorem pc_dimensions {k len : Nat} (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (space : Spec.Rsa.publicScratchWords k ≤ len) :
    2 ≤ Spec.Rsa.modulusWords k ∧ Spec.Rsa.modulusWords k < 2 ^ 31 ∧
      arrAt (Spec.Rsa.modulusWords k) 8 ≤ 8 * len ∧
      k ≤ 8 * Spec.Rsa.modulusWords k ∧ 128 * Spec.Rsa.modulusWords k < 2 ^ 32 := by
  simp only [Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords, arrAt, Spec.Rsa.Mont.hdrBytes] at *
  omega

theorem rsa_bytes_frame {regions : List Region} {m m' : Mem} {src : Addr} {k : Nat}
    (frame : Frame regions m m') (fit : k < 2 ^ 64)
    (sep : ∀ r ∈ regions, (⟨src, k⟩ : Region).Disjoint r) :
    Spec.Rsa.bytesAt m' src k = Spec.Rsa.bytesAt m src k := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro j hj
  exact frame.bytes (R := ⟨src, k⟩) sep (by change k ≤ 2 ^ 64; omega) (List.mem_range.mp hj)

end VG.Proof.Bignum.Arm
