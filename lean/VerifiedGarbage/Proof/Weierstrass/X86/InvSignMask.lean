import VerifiedGarbage.Proof.Weierstrass.X86.InvMaskCopy

/-! # The mask of a signed word coefficient -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem signMask_eq (x : BitVec 32) :
    0 - (x >>> 31) = if 2 ^ 31 ≤ x.toNat then BitVec.allOnes 32 else 0 := by
  have E : x >>> 31 = if 2 ^ 31 ≤ x.toNat then (1 : BitVec 32) else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := x.isLt
    have : (1 : BitVec 32).toNat = 1 := by decide
    have : (0 : BitVec 32).toNat = 0 := by decide
    split <;> omega
  rw [E]
  split <;> decide

theorem maskOf_ok {s : State} {base : Addr} {size coefficient : Nat}
    (hs : Scr s base size) (hc : coefficient + 4 ≤ size) :
    WP isa (.block (maskOf coefficient)) s fun u =>
      u.gpr .ecx = (if 2 ^ 31 ≤ w32 s.mem base coefficient then BitVec.allOnes 32 else 0) ∧
      Keeps [.eax, .ecx] s u ∧ u.mem = s.mem := by
  unfold maskOf
  refine wp_movS (readSrc_sc hs hc) fun s₁ U₁ _ => ?_
  refine wp_shr (by decide) fun s₂ U₂ _ => ?_
  refine wp_movS rfl fun s₃ U₃ _ => ?_
  refine wp_subS rfl fun u U₄ _ => WP.block_nil ?_
  refine ⟨?_, (((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
    (U₃.keeps.mono (by decide))).trans (U₄.keeps.mono (by decide)), ?_⟩
  · rw [U₄.gpr, U₃.gpr, U₃.other _ (by decide), U₂.gpr, U₁.gpr]
    exact signMask_eq _
  · rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]

end VG.Proof.Weierstrass.X86.Inv
