module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Out2
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint5
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Rsa.Arm.RvFail
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint4
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # An RSA key on ARMv7: the seven outputs and the mask returned (`stores_vp`), or zeros and 2 (`zeros_vp`) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

/-- Zeros at the first `k` outputs. -/
def ZS (P : KP) (E : State → Prop) (k : Nat) (σ s : State) : Prop :=
  E σ ∧ Bo P σ s ∧ ∀ i < k, Spec.Rsa.bytesAt s.mem (State.addr (oPtr P i)) (oLen P i) = List.replicate (oLen P i) 0

section
variable {P : KP}

theorem oFw_ok (i : Nat) (hi : i < 7) : oFw i + 4 ≤ 112 ∧ oFw i % 4 = 0 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem oFl_ok (i : Nat) : oFl i + 4 ≤ 112 ∧ oFl i % 4 = 0 := by unfold oFl; split <;> decide

/-- The seven outputs, and the mask returned. -/
theorem stores_vp {E : State → Prop} :
    VP (SS P E 0) stores (fun σ s => SS P E 7 σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (b2n (maskv P σ))) := by
  simp only [stores, List.cons_append, List.nil_append, storeTo, seqs]
  refine VP.assoc ((store_vp 0 (by decide) storeN_taint).seq ?_)
  refine VP.assoc ((store_vp 1 (by decide) storeD_taint).seq ?_)
  refine VP.assoc ((store_vp 2 (by decide) storeP_taint).seq ?_)
  refine VP.assoc ((store_vp 3 (by decide) storeQ_taint).seq ?_)
  refine VP.assoc ((store_vp 4 (by decide) storeDp_taint).seq ?_)
  refine VP.assoc ((store_vp 5 (by decide) storeDq_taint).seq ?_)
  refine VP.assoc ((store_vp 6 (by decide) storeQi_taint).seq ?_)
  refine VP.taint [.r7, .r8, .r9] retMask_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · rw [h₁.ws.r7, h₂.ws.r7]
    · rw [h₁.ws.r8, h₂.ws.r8]
    · rw [h₁.ws.r9, h₂.ws.r9]
  · refine wp_ldrSlot h.ws (d := sMask) (by decide) fun t u => WP.block_nil ⟨⟨h.e, h.bo.of_upd u,
      h.ws.of_upd u (by decide) (by decide) (by decide), by rw [u.mem]; exact h.arrs, by rw [u.mem]; exact h.mask,
      by rw [u.mem]; exact h.outs⟩, ?_⟩
    rw [u.gpr, ← h.mask]
    simp only [slot, w32, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Zeros to output `i`. -/
theorem zeroOut_vp {E : State → Prop} (i : Nat) (hi : i < 7) :
    VP (ZS P E i) (zeroOut (oFw i) (oFl i)) (ZS P E (i + 1)) := by
  unfold zeroOut
  have fw4 := oFw_ok i hi
  have fl4 := oFl_ok i
  refine VP.seq (G := fun σ s => ZS P E i σ s ∧ s.gpr .r0 = oPtr P i ∧
    s.gpr .lr = BitVec.ofNat 32 (oLen P i) ∧ s.gpr .r2 = 0) ?_ ?_
  · show VP _ (.block (([(Reg.r0, oFw i), (Reg.lr, oFl i)].map fun p => Instr.ldrSp p.1 p.2) ++
      [.mov .r2 (.imm 0)])) _
    refine VP.block_append (G := fun σ s => ZS P E i σ s ∧ s.gpr .r0 = oPtr P i ∧
      s.gpr .lr = BitVec.ofNat 32 (oLen P i)) ?_ ?_
    · refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, x⟩ => ?_
      · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
      · show WP isa (.block [.ldrSp .r0 (oFw i), .ldrSp .lr (oFl i)]) s _
        refine h.ldrSp fw4.1 fw4.2 fun s1 u1 => ?_
        refine (h.of_upd u1).ldrSp fl4.1 fl4.2 fun t u2 => WP.block_nil ?_
        exact ⟨⟨e, (h.of_upd u1).of_upd u2, by rw [u2.mem, u1.mem]; exact x⟩,
          by rw [u2.other _ (by decide), u1.gpr, h.pre.fwO i hi], by rw [u2.gpr, h.pre.flO i]⟩
    · refine VP.taint [.r0, .lr] VG.Proof.Rsa.Arm.Recover.movR2_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
        fun σ s ⟨⟨e, h, x⟩, p0, plr⟩ => ?_
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]
      · refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ⟨⟨e, h.of_upd u, by rw [u.mem]; exact x⟩,
          by rw [u.other _ (by decide), p0], by rw [u.other _ (by decide), plr], by rw [u.gpr]⟩
  · refine VP.taint [.r0, .lr] VG.Proof.Rsa.Arm.Recover.mask_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
      fun σ s ⟨⟨e, h, x⟩, p0, plr, p2⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
    have pre := h.pre
    have hl := oLen_le pre i
    have hW : 4 * P.W < 2 ^ 32 := by have := pre.k2; simp only [KP.W]; omega
    have hwr : InRegions s.wr (State.addr (oPtr P i)) (oLen P i) :=
      ⟨_, by rw [h.wr]; exact pre.oW i hi, Region.contains_self _ _⟩
    refine WP.mono (maskBuffer_ok s (oLen_pos pre i) (by omega) (pre.oFit i hi) hwr p0 plr)
      fun t ⟨b, f, r⟩ => ⟨e, ⟨pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, h.frame.trans (f.mono ?_)⟩,
        fun k hk => ?_⟩
    · intro r' hr; simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_cons_of_mem _ (oR_mem i hi)
    · rcases (by omega : k < i ∨ k = i) with hk' | rfl
      · rw [VG.Proof.Rsa.Arm.CrtValues.bytes_frame f (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact pre.oO k i (by omega) hi (by omega))
          (by have := pre.oFit k (by omega); omega)]
        exact x k hk'
      · rw [b, p2, VG.Proof.Rsa.Arm.CrtValues.zero_mask_bytes, VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]

/-- Zeros to the seven outputs, and 2 returned. -/
theorem zeros_vp {E : State → Prop} :
    VP (ZS P E 0) zeros (fun σ s => ZS P E 7 σ s ∧ s.gpr .r0 = 2) := by
  simp only [zeros, seqs]
  refine (zeroOut_vp 0 (by decide)).seq ?_
  refine (zeroOut_vp 1 (by decide)).seq ?_
  refine (zeroOut_vp 2 (by decide)).seq ?_
  refine (zeroOut_vp 3 (by decide)).seq ?_
  refine (zeroOut_vp 4 (by decide)).seq ?_
  refine (zeroOut_vp 5 (by decide)).seq ?_
  refine (zeroOut_vp 6 (by decide)).seq ?_
  refine VP.taint [] ret2_taint (fun _ _ _ _ _ _ r hr => absurd hr List.not_mem_nil)
    fun σ s ⟨e, h, z⟩ => wp_mov (op2_imm (by decide)) fun t u => WP.block_nil
      ⟨⟨e, h.of_upd u, by rw [u.mem]; exact z⟩, u.gpr⟩

end

end VG.Proof.RsaKeyGen.Arm.Key
