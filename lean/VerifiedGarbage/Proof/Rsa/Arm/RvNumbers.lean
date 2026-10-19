module

public import VerifiedGarbage.Proof.Rsa.Arm.RvLoads
import VerifiedGarbage.Proof.Rsa.Arm.RvMM

/-! # `vg_rsa_recover_primes` on ARMv7: the loads (`loads_vp`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

section
variable {P : RP}

theorem setupK_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ Bs P σ s) (.block setupK) (fun σ s => E σ ∧ Bs P σ s ∧ Ws s P.B P.Z P.w nArr ∧
      s.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.w ∧
      s.gpr .r0 = P.B + BitVec.ofNat 32 hdr ∧ s.gpr .lr = BitVec.ofNat 32 (nArr * (P.w + 2)) ∧
      s.gpr .r3 = 0) := by
  rw [setupK_eq]
  refine VP.block_append (G := fun σ s => (E σ ∧ Bs P σ s) ∧ s.gpr .r8 = P.B) ?_
    (VP.block_append (G := fun σ s => ((E σ ∧ Bs P σ s) ∧ s.gpr .r8 = P.B) ∧ s.gpr .r9 = BitVec.ofNat 32 P.K)
      ?_ ?_)
  · show VP _ (.block ([(Reg.r8, aoS)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h⟩ => ?_
    · rw [h₁.2.sp, h₁.2.pre.sp, h₂.2.sp, h₂.2.pre.sp]
    · exact h.ldrSp (o := aoS) (by decide) (by decide) (by decide) fun t u => WP.block_nil
        ⟨⟨e, h.of_rest (u.rest (ws := [.r8]) (by simp)) u.mem⟩, u.gpr.trans h.pre.aS⟩
  · show VP _ (.block ([(Reg.r9, aoK)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h⟩, r8⟩ => ?_
    · rw [h₁.1.2.sp, h₁.1.2.pre.sp, h₂.1.2.sp, h₂.1.2.pre.sp]
    · exact h.ldrSp (o := aoK) (by decide) (by decide) (by decide) fun t u => WP.block_nil
        ⟨⟨⟨e, h.of_rest (u.rest (ws := [.r9]) (by simp)) u.mem⟩, by rw [u.other _ (by decide), r8]⟩,
          u.gpr.trans h.pre.aK⟩
  · refine VP.taint [.r8, .r9] setupKTail_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨⟨e, h⟩, r8⟩, r9⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.1.2, h₂.1.2]
      · rw [h₁.2, h₂.2]
    · exact WP.mono (setupKTail_ok h r8 r9) fun t ⟨bt, wt, ct, p0, plr, r3, _⟩ => ⟨e, bt, wt, ct, p0, plr, r3⟩

theorem zero_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ Bs P σ s ∧ Ws s P.B P.Z P.w nArr ∧
      s.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.w ∧
      s.gpr .r0 = P.B + BitVec.ofNat 32 hdr ∧ s.gpr .lr = BitVec.ofNat 32 (nArr * (P.w + 2)) ∧
      s.gpr .r3 = 0) VG.Impl.Bignum.Arm.zero (fun σ s => E σ ∧ LS P σ (fun _ => 0) s) := by
  refine VP.taint [.r0, .lr] zero_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨e, h, hw, cnt, p0, plr, r3⟩ => WP.mono (zero_ls h hw cnt p0 plr r3) fun t ht => ⟨e, ht⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.1]

theorem loads_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ Bs P σ s) loads (fun σ s => E σ ∧ LS P σ (Aload P σ) s) := by
  have eL : loads = .seq (.block setupK) (.seq VG.Impl.Bignum.Arm.zero
      (.seq (.block [.ldrSp .r4 aoN, .ldrSp .r6 (aoN + 4)]) (.seq (VG.Impl.Rsa.Arm.CrtValues.load aN)
      (.seq (.block [.ldrSp .r4 aoE, .ldrSp .r6 (aoE + 4)]) (.seq (VG.Impl.Rsa.Arm.CrtValues.load (2 * wE))
        (seqs (loadArg aoD (2 * wD)))))))) := rfl
  rw [eL]
  refine setupK_vp.seq (zero_vp.seq (VP.assoc ?_))
  refine (loadArg_vp (A := fun _ _ => 0) (src := P.nP) (k := P.K) loadN_taint (by decide) (by decide) (by decide)
    (by decide) fun σ h => ⟨h.aN, h.aK, h.rdN, h.sN.symm, h.nF, h.fN, by have := h.k1; omega, Nat.le_refl _⟩).seq
    (VP.assoc ((loadArg_vp (src := P.eP) (k := P.el) loadE_taint (by decide) (by decide) (by decide) (by decide)
      fun σ h => ⟨h.aE, h.aEl, h.rdE, h.sE.symm, h.eF, h.fE, h.el1, h.el2⟩).seq
    ((loadArg_vp (src := P.dP) (k := P.dl) loadD_taint (by decide) (by decide) (by decide) (by decide)
      fun σ h => ⟨h.aD, h.aDl, h.rdD, h.sD.symm, h.dF, h.fD, h.dl1, h.dl2⟩).mono (fun _ _ h => h) ?_)))
  intro σ s ⟨e, h⟩
  refine ⟨e, ⟨h.bs, h.ws, h.cnt, fun j hj => ?_⟩⟩
  rw [h.full j hj]
  simp only [Aload, h.bs.pre.nB, h.bs.pre.eB, dv, dB]

end

end VG.Proof.Rsa.Arm.Recover
