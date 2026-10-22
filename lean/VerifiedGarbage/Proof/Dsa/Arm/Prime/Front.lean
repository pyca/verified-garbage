module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Loads
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Instr
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint1
import VerifiedGarbage.Proof.Bignum.Arm.MontMath

/-! # A candidate on ARMv7: whether `rand` holds a candidate

`lenCheck_vp`: Z iff `rand_len < out_len`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {P : CP}

theorem lenCheck_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ Bk P σ s) (.block lenCheck)
      (fun σ s => (E σ ∧ Bk P σ s) ∧ s.z = decide (P.rl < P.L)) := by
  rw [lenCheck_eq]
  refine VP.block_append (G := fun σ s => (E σ ∧ Bk P σ s) ∧ s.gpr .r1 = BitVec.ofNat 32 P.rl ∧
    s.gpr .r2 = BitVec.ofNat 32 P.L) ?_ ?_
  · show VP _ (.block ([(Reg.r1, aoRl), (Reg.r2, foL)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h⟩ => ?_
    · rw [h₁.2.sp, h₁.2.pre.sp, h₂.2.sp, h₂.2.pre.sp]
    · refine h.ldrSp (o := aoRl) (by decide) fun s1 u1 => ?_
      refine (h.of_upd u1).ldrSp (o := foL) (by decide) fun t u2 => WP.block_nil ?_
      exact ⟨⟨e, (h.of_upd u1).of_upd u2⟩, by rw [u2.other _ (by decide), u1.gpr, h.pre.aRl],
        by rw [u2.gpr, h.pre.wL]⟩
  · refine VP.taint [.r1, .r2] carryTail_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h⟩, r1, r2⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]
    have pre := h.pre
    have hr : P.rl < 2 ^ 32 := pre.rlt
    have hl : P.L < 2 ^ 32 := by have := pre.k2; omega
    refine carry_ok fun s1 r1' m1 v1 => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil
      ⟨⟨e, (h.of_rest r1' m1).of_rest (f.rest []) f.mem⟩, ?_⟩
    rw [z, v1, r1, r2, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hl]
    by_cases hc : P.L ≤ P.rl
    · simp [hc]
    · simp [hc]; omega

end

end VG.Proof.Dsa.Arm.Prime
