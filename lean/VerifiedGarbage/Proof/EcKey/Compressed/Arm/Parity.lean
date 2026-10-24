module

public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.Code

/-! # Choose the canonical root matching the SEC 1 parity bit -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov op2_imm op2_reg dpVal)

theorem xor_low_mask32 (x y : BitVec 32) :
    0 - ((x ^^^ y) &&& 1) = mask32 (x.toNat % 2 ≠ y.toNat % 2) := by
  have hlow : (x ^^^ y) &&& 1 = if x.toNat % 2 = y.toNat % 2 then 0 else 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_xor, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, show 2 = 2 ^ 1 from rfl, Nat.xor_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> simp [hx, hy]
  rw [hlow]
  by_cases h : x.toNat % 2 = y.toNat % 2 <;> simp [h, mask32]

theorem parityMask_ok {c : Cfg} {s : State} {base : Addr}
    (hs : Scr s base size) (hn : 0 < c.n)
    (hy : c.sl Impl.Ecdh.Arm.QY + 4 ≤ size) (ht : c.sl D + 4 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.parityMask c)) s fun t =>
      t.gpr .r10 = mask32 (sv c base s Impl.Ecdh.Arm.QY % 2 ≠
        (s.mem.readW (off base (c.sl D)) 32).toNat % 2) ∧
      Rest [.r4, .r5, .r10] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.Arm.parityMask
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read hy) fun s₁ u₁ => ?_
  have hs₁ := hs.of_rest (u₁.rest (ws := [.r4]) (by simp)) (by decide)
  refine wp_ldr (hs₁.off_lt (by omega)) (hs₁.ea (by omega)) (hs₁.read ht) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun t u₆ => WP.block_nil ?_
  refine ⟨?_, (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans
      ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))))), ?_⟩
  · rw [u₆.gpr, dpVal, u₅.gpr, u₅.other .r5 (by decide), u₄.gpr, dpVal, u₃.gpr, dpVal,
      u₂.gpr, u₂.other .r4 (by decide), u₁.gpr, u₁.mem, BitVec.xor_comm, xor_low_mask32]
    rw [slot32_parity _ _ _ _ hn]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem invertMask_ok (s : State) (P : Prop) [Decidable P] (h : s.gpr .r10 = mask32 P) :
    WP isa (.block Impl.EcKey.Compressed.Arm.invertMask) s fun t =>
      t.gpr .r5 = mask32 (¬ P) ∧ Rest [.r4, .r5] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.Arm.invertMask
  refine wp_dp (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun t u₃ => WP.block_nil ?_
  refine ⟨?_, (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans (u₃.rest (by simp))), ?_⟩
  · rw [u₃.gpr, dpVal, u₂.gpr, u₂.other .r5 (by decide), u₁.gpr, dpVal, h]
    by_cases hp : P <;> simp [mask32, hp]
  · rw [u₃.mem, u₂.mem, u₁.mem]

end VG.Proof.EcKey.Compressed.Arm
