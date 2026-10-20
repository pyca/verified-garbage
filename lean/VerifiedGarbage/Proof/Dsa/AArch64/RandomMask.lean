module

public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Correctness of the sampler's fixed public-byte mask selection. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.Bignum.AArch64

def randomMaskValue (n : Nat) : BitVec 64 :=
  if n < 2 then 1 else if n < 4 then 3 else if n < 8 then 7 else
  if n < 16 then 15 else if n < 32 then 31 else if n < 64 then 63 else
  if n < 128 then 127 else 255

theorem random_sub_carry (a b : BitVec 64) :
    decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + 1) = decide (b.toNat ≤ a.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, BitVec.toNat_not]
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem random_mask_ok (s : State) :
    WP isa Impl.Dsa.AArch64.Random.mask s fun t =>
      t.gpr .x8 = randomMaskValue (s.gpr .x0).toNat ∧ t.mem = s.mem ∧
      Keep [.x3, .x4, .x8] s t := by
  refine WP.mono (WP.keep [.x3, .x4, .x8] (Q := fun t =>
    t.gpr .x8 = randomMaskValue (s.gpr .x0).toNat ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  unfold Impl.Dsa.AArch64.Random.mask Impl.Dsa.AArch64.Random.maskCode
    Impl.Dsa.AArch64.Random.maskStep
  brun [random_sub_carry, Bool.toNat_true, decide_eq_true_eq]
  change (if 2 ≤ (s.gpr .x0).toNat then
    if 4 ≤ (s.gpr .x0).toNat then
    if 8 ≤ (s.gpr .x0).toNat then
    if 16 ≤ (s.gpr .x0).toNat then
    if 32 ≤ (s.gpr .x0).toNat then
    if 64 ≤ (s.gpr .x0).toNat then
    if 128 ≤ (s.gpr .x0).toNat then 255 else 127
    else 63 else 31 else 15 else 7 else 3 else 1) = _
  simp only [← Nat.not_lt, ite_not, randomMaskValue]

/-- The selected mask keeps exactly the significant bits of a nonzero byte. -/
theorem randomMaskValue_eq (n : Nat) (hpos : 0 < n) (hbound : n < 256) :
    randomMaskValue n = BitVec.ofNat 64 (2 ^ (n.log2 + 1) - 1) := by
  unfold randomMaskValue
  split
  · have hlog : n.log2 = 0 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
    rw [hlog]
    rfl
  ·
    split
    · have hlog : n.log2 = 1 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
      rw [hlog]
      rfl
    ·
      split
      · have hlog : n.log2 = 2 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
        rw [hlog]
        rfl
      ·
        split
        · have hlog : n.log2 = 3 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
          rw [hlog]
          rfl
        ·
          split
          · have hlog : n.log2 = 4 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
            rw [hlog]
            rfl
          ·
            split
            · have hlog : n.log2 = 5 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
              rw [hlog]
              rfl
            ·
              split
              · have hlog : n.log2 = 6 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
                rw [hlog]
                rfl
              ·
                have hlog : n.log2 = 7 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
                rw [hlog]
                rfl

end VG.Proof.Dsa.AArch64
