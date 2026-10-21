module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The constant-time comb scan compares its public index with the secret magnitude. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.X25519.Arm

theorem eqMask_ok {s : State} {index : Op2} {v : BitVec 32}
    (hi : index.eval s = some v) :
    WP isa (.block (TCombCfg.eqMask index)) s fun t =>
      t.gpr .r10 = 0#32 - (((s.gpr .r9 ^^^ v) - 1) >>> 31) ∧
      Rest [.r5,.r10] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.eqMask
  refine wp_dp hi fun s₁ u₁ => wp_dp (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
    wp_dp (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  refine ⟨?_, (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans (u₅.rest (by simp))))), ?_⟩
  · rw [u₅.gpr,dpVal,u₄.gpr,u₄.other .r10 (by decide),u₃.gpr,u₂.gpr,dpVal,u₁.gpr,dpVal]
    rfl
  · rw [u₅.mem,u₄.mem,u₃.mem,u₂.mem,u₁.mem]

theorem zero_test_bit (x : BitVec 32) (hx : x.toNat < 2^31) :
    (x-1) >>> 31 = if x=0#32 then 1 else 0 := by
  by_cases h : x = 0#32
  · subst h; decide
  · have h0 : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    simp only [h, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
      show (1 : BitVec 32).toNat = 1 from rfl]
    show _ = 0
    omega

theorem equality_mask {a b : BitVec 32} (ha : a.toNat < 2^31) (hb : b.toNat < 2^31) :
    0#32 - (((a ^^^ b)-1) >>> 31) = if a=b then BitVec.allOnes 32 else 0 := by
  have hx : (a ^^^ b).toNat < 2^31 := by
    rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow ha hb
  rw [zero_test_bit _ hx]
  by_cases h : a=b
  · subst h; simp only [BitVec.xor_self, ↓reduceIte]; decide
  · have hn : a ^^^ b ≠ 0#32 := fun e => h (BitVec.xor_eq_zero_iff.mp e)
    simp only [hn,h,↓reduceIte]; decide

end VG.Proof.Weierstrass.Arm.TComb
