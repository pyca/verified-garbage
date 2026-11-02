module

public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Frame
public import VerifiedGarbage.Impl.Argon2.RISCV64.HPrime
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Argon2.RISCV64.Ops
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp

/-! # H′: selecting the first digest length -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Wp (wp_mv wp_subi wp_li Upd eval_nonzero)

/-- A bounded public output length can be compared using the high bit of
its subtraction, without adding flag-based branches to the ISA. -/
theorem below65 (x : BitVec 64) (hx : x.toNat < 2 ^ 32) :
    (x - 65) >>> (63 : Nat) = if x.toNat < 65 then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  by_cases h : x.toNat < 65
  · rw [ite_eq_left h, BitVec.toNat_sub_of_lt (by rw [BitVec.lt_def]; exact h)]
    simp only [show (65 : BitVec 64).toNat = 65 from rfl,
      show (1 : BitVec 64).toNat = 1 from rfl, Nat.reducePow]
    omega
  · rw [ite_eq_right h, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact Nat.le_of_not_gt h)]
    simp only [show (65 : BitVec 64).toNat = 65 from rfl,
      show (0 : BitVec 64).toNat = 0 from rfl]
    omega

theorem Keeps.of_upd {s t : State} {d : Reg} {v : BitVec 64}
    (h : Upd s t d v) (hd : d ∉ preserved) : Keeps s t := by
  refine ⟨fun r hr => h.other r ?_, h.rd, h.wr, h.sp, ?_⟩
  · intro he; subst r; exact hd hr
  · rw [h.mem]; exact Frame.refl _ _

theorem chooseLength_ok (s : State) (hb : (s.gpr .s3).toNat < 2 ^ 32) :
    WP isa chooseLength s fun t =>
      t.gpr .a1 = BitVec.ofNat 64 (min (s.gpr .s3).toNat 64) ∧ Keeps s t := by
  unfold chooseLength
  refine WP.seq (wp_mv fun a ha => wp_subi (by decide) fun b hb' =>
    wp_srl (by decide) fun u hu => WP.block_nil ?_)
  have ku : Keeps s u :=
    (Keeps.of_upd ha (by decide)).trans
      ((Keeps.of_upd hb' (by decide)).trans (Keeps.of_upd hu (by decide)))
  have n : u.gpr .a1 = s.gpr .s3 := by
    rw [hu.other _ (by decide), hb'.other _ (by decide), ha.gpr]
  have comparison : u.gpr .a7 = if (s.gpr .s3).toNat < 65 then 1 else 0 := by
    rw [hu.gpr, hb'.gpr, ha.gpr]
    exact below65 _ hb
  have flag : isa.eval (.nonzero .a7) u = some (decide ((s.gpr .s3).toNat < 65)) := by
    show VG.RISCV64.eval (.nonzero .a7) u = _
    by_cases hn : (s.gpr .s3).toNat < 65 <;>
      simp [eval_nonzero, comparison, hn]
  refine WP.ite (decide ((s.gpr .s3).toNat < 65)) flag ?_ ?_
  · intro h
    have hn : (s.gpr .s3).toNat ≤ 64 := by have := of_decide_eq_true h; omega
    apply WP.block_nil
    refine ⟨?_, ku⟩
    rw [n, Nat.min_eq_left hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro h
    have hn : 64 ≤ (s.gpr .s3).toNat := by have := of_decide_eq_false h; omega
    refine wp_li (by decide) fun t ht => WP.block_nil ?_
    refine ⟨?_, ku.trans (Keeps.of_upd ht (by decide))⟩
    rw [Nat.min_eq_right hn]; exact ht.gpr

end VG.Proof.Argon2.RISCV64.HPrime
