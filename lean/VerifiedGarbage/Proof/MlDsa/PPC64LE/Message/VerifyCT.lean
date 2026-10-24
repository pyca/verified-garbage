module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Verify
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.SignCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Sha3.PPC64LE.PiecesCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.Message.Common
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Verify
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.SignCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.PiecesCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.Message.Common

/-!
# ML-DSA on PPC64LE, `verify_message`: constant time

As signing's (`SignCT.lean`): two runs from states that satisfy `MVPre` and
agree on the arguments in registers, the stack pointer and the inputs, the
leakage of `verifyMessageContract` (`MVPub`), leak the same trace
(`verifyMessage_ct`). The two hashes are related by `hash_ct`, and the call
of the verification function on `μ` by its own constant time, whose leakage
is its inputs: the key and the signature, and `μ`, which both runs compute
from the same inputs.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Message

open VG VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Message
open VG.Impl.Sha3.PPC64LE.Pieces (Piece hash)
open VG.Proof.Sha3.PPC64LE.Pieces (HashOk hashRegs hash_ct)
open VG.Proof.MlKem.PPC64LE.Sample (relct_wp)
open VG.Proof.X25519.PPC64LE (Upd WP.cons)
open VG.Proof.MlDsa.PPC64LE.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The argument registers of `verify_message`. -/
abbrev vArgs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9]

theorem venter_taint (p : Params) : (VG.PPC64LE.taint.check (Taint.ofRegs vArgs)
    (.block (enter .r9 p verifyRegs verifyMs))
    (VG.Taint.hintOf VG.PPC64LE.taint (Taint.ofRegs vArgs) (.block (enter .r9 mlDsa44 verifyRegs verifyMs)))).isSome =
    true := rfl

/-- What two runs agree on: `verifyMessageContract`'s public part. -/
def MVPub (p : Params) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧
    leakBytes (pkB p s₁ ++ msgB s₁ ++ ctxB s₁ ++ vsigB p s₁) = leakBytes (pkB p s₂ ++ msgB s₂ ++ ctxB s₂ ++ vsigB p s₂) ∧
    ∀ r ∈ vArgs, s₁.gpr r = s₂.gpr r

theorem verifyV_eq {p : Params} {s₁ s₂ : State} (h : ∀ r ∈ vArgs, s₁.gpr r = s₂.gpr r) :
    ∀ r ∈ verifyRegs, verifyV p s₁ r = verifyV p s₂ r := by
  intro r hr
  simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 7 exact h _ (by decide)
  show eAt p (s₁.gpr .r9) = eAt p (s₂.gpr .r9)
  rw [h .r9 (by decide)]

theorem vinv_regs {p : Params} {STK : Nat} {s₁ s₂ a b : State} (h : ∀ r ∈ vArgs, s₁.gpr r = s₂.gpr r)
    (ha : VInv p STK s₁ a) (hb : VInv p STK s₂ b) : ∀ r ∈ verifyRegs, a.gpr r = b.gpr r := fun r hr =>
  (ha.regs r hr).trans ((verifyV_eq h r hr).trans (hb.regs r hr).symm)

section
variable {p : Params} {STK : Nat} {s t : State} (hF : MFacts p) (hp : MVPre p STK s) (h48 : 48 ≤ STK)
include hF hp h48

theorem mv1_hashOk (h : MV1 p STK s t) : HashOk 840 64 .r30 .r30 oMU [(⟨.r22, 0, .imm p.pkLen⟩ : Piece)] t := by
  have hi := h.inv
  have g30 := v_e hi
  exact ⟨by decide, by decide, by decide, by decide, by simp, by rw [g30]; exact vke hp h48 hi,
    by rw [g30]; exact trHash_ins hF hp h48 hi, by rw [g30]; exact ve_cov hp hi.wr (by decide),
    by rw [g30]; exact (e_e0 (by decide) (by decide)).symm,
    by rw [g30, hi.sp]; exact (hp.bx.sub_left (vbelow48 hp h48)).sub_right (e_sub (by decide))⟩

omit hF in
theorem mv2_hashOk (h : MV2 p STK s t) :
    HashOk 840 64 .r30 .r30 oMU ((⟨.r30, oMU, .imm 64⟩ : Piece) :: fmtPieces) t := by
  have hi := h.inv
  have g30 := v_e hi
  exact ⟨by decide, by decide, by decide, by decide, by simp, by rw [g30]; exact vke hp h48 hi,
    by rw [g30]; exact muHash_ins hp h48 hi, by rw [g30]; exact ve_cov hp hi.wr (by decide),
    by rw [g30]; exact (e_e0 (by decide) (by decide)).symm,
    by rw [g30, hi.sp]; exact (hp.bx.sub_left (vbelow48 hp h48)).sub_right (e_sub (by decide))⟩

end

theorem verifyMessage_ct {p : Params} {STK S : Nat} (hF : MFacts p) (h48 : 48 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => verifyContract p PPC64LE.abi stk) S) (hS : S ≤ STK) {n : String} :
    ConstantTime isa (MVPre p STK) (MVPub p) (verifyMessage n f p) := by
  obtain ⟨stk, hstk, hver⟩ := hf.verified
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ MVPre p STK x.1 ∧ MVPre p STK x.2 ∧
    MVPub p x.1 x.2) (RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩) (fun _ _ h => h)
  by_cases hH : MVPre p STK s₁ ∧ MVPre p STK s₂ ∧ MVPub p s₁ s₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨hp₁, hp₂, psp, pl, pr⟩ := hH
  refine RelCT.mono (P := fun a b => a = s₁ ∧ b = s₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have p7 : s₁.gpr .r7 = s₂.gpr .r7 := pr _ (by decide)
  obtain ⟨ek, em, ec, eg⟩ := Proof.MlDsa.Message.leak4 (by simp [Proof.MlKem.bytesAt_length])
    (by simp [Proof.MlKem.bytesAt_length, pr .r5 (by decide)]) (by simp [Proof.MlKem.bytesAt_length, p7]) pl
  unfold verifyMessage top
  -- The length check.
  refine RelCT.seq (R := fun a b => a = s₁.write .r11 (s₁.gpr .r7 >>> 8) ∧ b = s₂.write .r11 (s₂.gpr .r7 >>> 8))
    (RelCT.mono (relct_wp (ct_prog [.r7] (fun a b hab => by rw [hab.1, hab.2, psp])
      (fun a b hab r hr => by rw [List.mem_singleton.mp hr, hab.1, hab.2, p7]) (by taint_decide)) fun a b hab =>
      ⟨by rw [hab.1]; exact WP.cons (exec_lsr_d (by decide)) (WP.block_nil rfl),
       by rw [hab.2]; exact WP.cons (exec_lsr_d (by decide)) (WP.block_nil rfl)⟩) (fun _ _ h => h)
      fun _ _ h => h) ?_
  refine RelCT.ite (fun a b hab => by
    rw [hab.1, hab.2, eval_zero, eval_zero, (Upd.write _ _ _).gpr, (Upd.write _ _ _).gpr, p7]) ?_ ?_
  · have hu₁ := Upd.write s₁ .r11 (s₁.gpr .r7 >>> 8)
    have hu₂ := Upd.write s₂ .r11 (s₂.gpr .r7 >>> 8)
    -- The setup.
    refine RelCT.seq (R := fun a b => MV1 p STK s₁ a ∧ MV1 p STK s₂ b)
      (RelCT.mono (relct_wp (ct_prog vArgs (fun a b hab => by
          rw [hab.1.1, hab.1.2, hu₁.sp, hu₂.sp, psp]) (fun a b hab r hr => by
          rw [hab.1.1, hab.1.2, hu₁.other _ (by revert r; decide), hu₂.other _ (by revert r; decide)]
          exact pr r hr) (venter_taint p)) fun a b hab => by
          rw [hab.1.1, hab.1.2]
          exact ⟨verifySetup_ok hF hp₁ hu₁.other hu₁.rd hu₁.wr hu₁.sp rfl hu₁.mem,
            verifySetup_ok hF hp₂ hu₂.other hu₂.rd hu₂.wr hu₂.sp rfl hu₂.mem⟩) (fun _ _ h => h) fun _ _ h => h) ?_
    -- `tr`.
    refine RelCT.seq (R := fun a b => MV2 p STK s₁ a ∧ MV2 p STK s₂ b)
      (relct_wp (hash_ct (by taint_decide) fun a b h => ⟨mv1_hashOk hF hp₁ h48 h.1, mv1_hashOk hF hp₂ h48 h.2,
          h.1.inv.sp.trans (psp.trans h.2.inv.sp.symm), fun r hr => vinv_regs pr h.1.inv h.2.inv r
            (by simp only [hashRegs, List.flatMap_cons, List.flatMap_nil, Piece.regs, List.append_nil] at hr
                revert r hr; decide)⟩)
        fun a b hab => ⟨trHash_ok hF hp₁ h48 hab.1, trHash_ok hF hp₂ h48 hab.2⟩) ?_
    -- `μ`.
    refine RelCT.seq (R := fun a b => MV3 p STK s₁ a ∧ MV3 p STK s₂ b)
      (relct_wp (hash_ct (by taint_decide) fun a b h => ⟨mv2_hashOk hp₁ h48 h.1, mv2_hashOk hp₂ h48 h.2,
          h.1.inv.sp.trans (psp.trans h.2.inv.sp.symm), fun r hr => vinv_regs pr h.1.inv h.2.inv r
            (by revert r hr; decide)⟩)
        fun a b hab => ⟨verifyHash_ok hp₁ h48 hab.1, verifyHash_ok hp₂ h48 hab.2⟩) ?_
    -- The call.
    refine RelCT.seq (R := fun a b => VInv p STK s₁ a ∧ VInv p STK s₂ b)
      (relct_wp ?_ fun a b hab => ⟨WP.mono (verifyCall_ok hF hp₁ hf hS hab.1) fun _ h => h.1,
        WP.mono (verifyCall_ok hF hp₂ hf hS hab.2) fun _ h => h.1⟩)
      (ct_prog [.r30] (fun a b hab => hab.1.sp.trans (psp.trans hab.2.sp.symm))
        (fun a b hab r hr => by rw [List.mem_singleton.mp hr]; exact vinv_regs pr hab.1 hab.2 _ (by decide))
        (by taint_decide))
    refine RelCT.seq (R := fun a b => VA p STK s₁ a ∧ VA p STK s₂ b)
      (relct_wp (ct_prog [.r22, .r27, .r29, .r30] (fun a b hab => hab.1.inv.sp.trans (psp.trans hab.2.inv.sp.symm))
        (fun a b hab r hr => vinv_regs pr hab.1.inv hab.2.inv r (by revert r hr; decide)) (by taint_decide))
        fun a b hab => ⟨verifyArgs_ok hab.1, verifyArgs_ok hab.2⟩) ?_
    refine RelCT.call hver.1 hver.2.1 (vRd p s₁) (vWr p s₁) fun a b hab => ?_
    have hpre₁ := verifyCall_pre hF hp₁ (Nat.le_trans hstk hS) hab.1
    have hpre₂ := verifyCall_pre hF hp₂ (Nat.le_trans hstk hS) hab.2
    have eRd : vRd p s₂ = vRd p s₁ := by simp only [vRd, pkR, vsigR, pr _ (by decide : Reg.r3 ∈ vArgs),
      pr _ (by decide : Reg.r8 ∈ vArgs), pr _ (by decide : Reg.r9 ∈ vArgs)]
    have eWr : vWr p s₂ = vWr p s₁ := by simp only [vWr, pr _ (by decide : Reg.r9 ∈ vArgs)]
    rw [eRd, eWr] at hpre₂
    refine ⟨hpre₁.1, hpre₂.1, ?_, hpre₁.2.1, hpre₁.2.2, hpre₂.2.1, hpre₂.2.2⟩
    have k₁ := hab.1.ms.inv
    have k₂ := hab.2.ms.inv
    refine verify_pub (by simp only [State.withRegions_sp, State.callEntry_sp, k₁.sp, k₂.sp, psp]) ?_ ?_ ?_ ?_ ?_
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.r3, hab.2.r3, pr _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.r4, hab.2.r4, pr _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.r5, hab.2.r5, pr _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.r6, hab.2.r6, pr _ (by decide)]
    · simp only [State.withRegions_mem, State.callEntry_mem, ce_gpr _ _ _ (show Reg.r3 ∉ linkRegs by decide),
        ce_gpr _ _ _ (show Reg.r4 ∉ linkRegs by decide), ce_gpr _ _ _ (show Reg.r5 ∉ linkRegs by decide),
        hab.1.r3, hab.1.r4, hab.1.r5, hab.2.r3, hab.2.r4, hab.2.r5]
      rw [v_keep k₁ (R := pkR p s₁) (by have := hF.pk; show p.pkLen < 2 ^ 64; omega) hp₁.kc hp₁.bk,
        hab.1.ms.mu, v_keep k₁ (R := vsigR p s₁) (by have := hF.sgl; show p.sigLen < 2 ^ 64; omega) hp₁.gc hp₁.bg,
        v_keep k₂ (R := pkR p s₂) (by have := hF.pk; show p.pkLen < 2 ^ 64; omega) hp₂.kc hp₂.bk,
        hab.2.ms.mu, v_keep k₂ (R := vsigR p s₂) (by have := hF.sgl; show p.sigLen < 2 ^ 64; omega) hp₂.gc hp₂.bg]
      simp only [pkB, vsigB, fmtB, ctxB, msgB] at ek em ec eg ⊢
      rw [ek, em, ec, eg, p7]
  · -- `ctx_len ≥ 256`.
    exact ct_prog [] (fun a b hab => by rw [hab.1.1, hab.1.2, (Upd.write _ _ _).sp, (Upd.write _ _ _).sp, psp])
      (fun _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide)

end VG.Proof.MlDsa.PPC64LE.Message
