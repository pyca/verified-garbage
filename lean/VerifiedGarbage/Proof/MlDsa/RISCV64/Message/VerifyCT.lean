module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Verify
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.SignCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Sha3.RISCV64.PiecesCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.Message.Common
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Verify
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.SignCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Sha3.RISCV64.PiecesCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.Message.Common
meta import VerifiedGarbage.Impl.MlDsa.RISCV64.Message
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Message

/-!
# ML-DSA on RISC-V, `verify_message_cached`: constant time

As signing's (`SignCT.lean`): two runs from states that satisfy `MVCPre` and
agree on the arguments in registers, the stack pointer and the inputs, the
leakage of `verifyMessageCachedContract` (`MVCPub`), leak the same trace
(`verifyMessageCached_ct`). The hash of `μ` is related by `hash_ct`, and the
call of the verification function on `μ` by its own constant time, whose
leakage is its inputs: the key and the signature, and `μ`, which both runs
compute from the same inputs (`verifyCall_ct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Message
open VG.Impl.Sha3.RISCV64.Pieces (Piece hash)
open VG.Proof.Sha3.RISCV64.Pieces (HashOk PieceOk hash_ct)
open VG.RISCV64.Steps (Upd)
open VG.Proof.MlDsa.RISCV64.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The argument registers of `verify_message_cached` but `tr` (`a7`). -/
abbrev vArgs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6]

/-- The registers `rs` agree in two runs whose invariants say they hold the same. -/
theorem vinvG_regs {p : Params} {STK : Nat} {s₁ s₂ a b : State} {rs : List Reg} {V₁ V₂ : Reg → BitVec 64}
    (h : ∀ r ∈ rs, V₁ r = V₂ r) (ha : VInvG p STK s₁ rs V₁ a) (hb : VInvG p STK s₂ rs V₂ b) :
    ∀ r ∈ rs, a.gpr r = b.gpr r := fun r hr =>
  (ha.regs r hr).trans ((h r hr).trans (hb.regs r hr).symm)

section
variable {p : Params} {q : Bool} {STK : Nat} {X : List Region} {s t : State} (hF : MFacts p) (hp : MVPre p q STK X s)
  (h48 : 1168 ≤ STK)
include hF hp h48

omit hF in
/-- The hash of `μ` may run, from the first piece `q₀`. -/
theorem mu_hashOk {rs : List Reg} {V : Reg → BitVec 64} (hL : VL p s rs V) (hi : VInvG p STK s rs V t)
    {q₀ : Piece} (h₀ : PieceOk 840 (eAt p (s.gpr .a6)) t q₀) :
    HashOk 840 64 .s8 .s8 oMU (q₀ :: fmtPieces) t := by
  have g30 := v_e hL hi
  exact ⟨by decide, by decide, by decide, by decide, by simp, by rw [g30]; exact vke hp h48 hi,
    by rw [g30]; exact mu_ins hp h48 hL hi h₀, by rw [g30]; exact ve_cov hp hi.wr (by decide),
    by rw [g30]; exact (e_e0 (by decide) (by decide)).symm,
    by rw [g30, hi.sp]; exact (hp.bx.sub_left (vbelow48 hp h48)).sub_right (e_sub (by decide))⟩

omit hF in
end

/-- The call of the verification function on `μ`, in two runs that agree on `MVCPub`'s inputs, and whose
invariants say the registers `rs` hold the same. -/
theorem verifyCall_ct {p : Params} {q : Bool} {STK S : Nat} {X₁ X₂ : List Region} {s₁ s₂ : State} {rs : List Reg}
    {V₁ V₂ : Reg → BitVec 64} (hF : MFacts p) {f : Prog isa}
    (hf : Callee f (fun stk => PreparedKey.verifyEK p q stk) S) (hS : S ≤ STK) {n : String}
    (hL₁ : VL p s₁ rs V₁) (hL₂ : VL p s₂ rs V₂) (hp₁ : MVPre p q STK X₁ s₁) (hp₂ : MVPre p q STK X₂ s₂)
    (hk₁ : q = true → PreparedPublicKey p s₁.mem (s₁.gpr .a0)) (hk₂ : q = true → PreparedPublicKey p s₂.mem (s₂.gpr .a0))
    (psp : s₁.sp = s₂.sp)
    (pr : ∀ r ∈ vArgs, s₁.gpr r = s₂.gpr r) (hV : ∀ r ∈ rs, V₁ r = V₂ r)
    (ek : pkB p s₁ = pkB p s₂) (em : msgB s₁ = msgB s₂) (ec : ctxB s₁ = ctxB s₂) (eg : vsigB p s₁ = vsigB p s₂) :
    RelCT isa (fun a b => MV3 p STK s₁ rs V₁ a ∧ MV3 p STK s₂ rs V₂ b) (.seq (.block verifyArgs) (.call n f))
      fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hf.verified
  have p7 : s₁.gpr .a4 = s₂.gpr .a4 := pr _ (by decide)
  refine RelCT.seq (R := fun a b => VA p STK s₁ rs V₁ a ∧ VA p STK s₂ rs V₂ b)
    (relct_wp (ct_prog [.s0, .s5, .s7, .s8] (fun a b hab => hab.1.inv.sp.trans (psp.trans hab.2.inv.sp.symm))
      (fun a b hab r hr => vinvG_regs hV hab.1.inv hab.2.inv r (hL₁.regs r (by revert r hr; decide)).1)
      (by taint_decide))
      fun a b hab => ⟨verifyArgs_ok hL₁ hab.1, verifyArgs_ok hL₂ hab.2⟩) ?_
  refine RelCT.call hver.1 hver.2.1 (vRd p q s₁) (vWr p s₁) fun a b hab => ?_
  have hpre₁ := verifyCall_pre hF hp₁ hk₁ (Nat.le_trans hstk hS) hab.1
  have hpre₂ := verifyCall_pre hF hp₂ hk₂ (Nat.le_trans hstk hS) hab.2
  have eRd : vRd p q s₂ = vRd p q s₁ := by simp only [vRd, pkR, vsigR, pr _ (by decide : Reg.a0 ∈ vArgs),
    pr _ (by decide : Reg.a5 ∈ vArgs), pr _ (by decide : Reg.a6 ∈ vArgs)]
  have eWr : vWr p s₂ = vWr p s₁ := by simp only [vWr, pr _ (by decide : Reg.a6 ∈ vArgs)]
  rw [eRd, eWr] at hpre₂
  refine ⟨hpre₁.1, hpre₂.1, ?_, hpre₁.2.1, hpre₁.2.2, hpre₂.2.1, hpre₂.2.2⟩
  have k₁ := hab.1.ms.inv
  have k₂ := hab.2.ms.inv
  refine verify_pub (by simp only [State.withRegions_sp, State.callEntry_sp, k₁.sp, k₂.sp, psp]) ?_ ?_ ?_ ?_ ?_
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a0, hab.2.a0, pr _ (by decide)]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a1, hab.2.a1, pr _ (by decide)]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a2, hab.2.a2, pr _ (by decide)]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a3, hab.2.a3, pr _ (by decide)]
  · simp only [State.withRegions_mem, State.callEntry_mem, ce_gpr _ _ _ (show Reg.a0 ∉ linkRegs by decide),
      ce_gpr _ _ _ (show Reg.a1 ∉ linkRegs by decide), ce_gpr _ _ _ (show Reg.a2 ∉ linkRegs by decide),
      hab.1.a0, hab.1.a1, hab.1.a2, hab.2.a0, hab.2.a1, hab.2.a2]
    have ks := pkE_sub hF q
    have hl : p.pkLen < 2 ^ 64 := by have := hF.pk; omega
    rw [v_keep k₁ (R := ⟨s₁.gpr .a0, p.pkLen⟩) hl (hp₁.kc.sub_left (ks s₁)) (hp₁.bk.sub_right (ks s₁)),
      hab.1.ms.mu, v_keep k₁ (R := vsigR p s₁) (by have := hF.sgl; show p.sigLen < 2 ^ 64; omega) hp₁.gc hp₁.bg,
      v_keep k₂ (R := ⟨s₂.gpr .a0, p.pkLen⟩) hl (hp₂.kc.sub_left (ks s₂)) (hp₂.bk.sub_right (ks s₂)),
      hab.2.ms.mu, v_keep k₂ (R := vsigR p s₂) (by have := hF.sgl; show p.sigLen < 2 ^ 64; omega) hp₂.gc hp₂.bg]
    simp only [pkB, vsigB, fmtB, ctxB, msgB] at ek em ec eg ⊢
    rw [ek, em, ec, eg, p7]

/-- The argument registers of `verify_message_cached`. -/
abbrev vcArgs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

theorem cachedEnter_taint (p : Params) : (VG.RISCV64.taint.check (Taint.ofRegs vcArgs)
    (.block (enter .a6 p signRegs cachedMs))
    (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs vcArgs) (.block (enter .a6 mlDsa44 signRegs cachedMs)))).isSome =
    true := rfl

/-- What two runs agree on: `verifyMessageCachedContract`'s public part. -/
def MVCPub (p : Params) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧
    leakBytes (pkB p s₁ ++ msgB s₁ ++ ctxB s₁ ++ vsigB p s₁) = leakBytes (pkB p s₂ ++ msgB s₂ ++ ctxB s₂ ++ vsigB p s₂) ∧
    ∀ r ∈ vcArgs, s₁.gpr r = s₂.gpr r

theorem cachedV_eq {p : Params} {s₁ s₂ : State} (h : ∀ r ∈ vcArgs, s₁.gpr r = s₂.gpr r) :
    ∀ r ∈ signRegs, cachedV p s₁ r = cachedV p s₂ r := by
  intro r hr
  simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 8 exact h _ (by decide)
  show eAt p (s₁.gpr .a6) = eAt p (s₂.gpr .a6)
  rw [h .a6 (by decide)]

theorem verifyMessageCached_ct {p : Params} {q : Bool} {STK S : Nat} (hF : MFacts p) (h48 : 1168 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => PreparedKey.verifyEK p q stk) S) (hS : S ≤ STK) {n : String} :
    ConstantTime isa (MVCPre p q STK) (MVCPub p) (verifyMessageCached n f p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ MVCPre p q STK x.1 ∧
    MVCPre p q STK x.2 ∧ MVCPub p x.1 x.2) (RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩)
    (fun _ _ h => h)
  by_cases hH : MVCPre p q STK s₁ ∧ MVCPre p q STK s₂ ∧ MVCPub p s₁ s₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨hc₁, hc₂, psp, pl, pr⟩ := hH
  have hp₁ := hc₁.mv
  have hp₂ := hc₂.mv
  have pv : ∀ r ∈ vArgs, s₁.gpr r = s₂.gpr r := fun r hr => pr r (by revert r hr; decide)
  have hV := cachedV_eq (p := p) pr
  refine RelCT.mono (P := fun a b => a = s₁ ∧ b = s₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have p7 : s₁.gpr .a4 = s₂.gpr .a4 := pr _ (by decide)
  obtain ⟨ek, em, ec, eg⟩ := Proof.MlDsa.Message.leak4 (by simp [Proof.MlKem.bytesAt_length])
    (by simp [Proof.MlKem.bytesAt_length, pr .a2 (by decide)]) (by simp [Proof.MlKem.bytesAt_length, p7]) pl
  unfold verifyMessageCached top
  -- The length check.
  refine RelCT.seq (R := fun a b => a = s₁.write .t1 (s₁.gpr .a4 >>> 8) ∧ b = s₂.write .t1 (s₂.gpr .a4 >>> 8))
    (RelCT.mono (relct_wp (ct_prog [.a4] (fun a b hab => by rw [hab.1, hab.2, psp])
      (fun a b hab r hr => by rw [List.mem_singleton.mp hr, hab.1, hab.2, p7]) (by taint_decide)) fun a b hab =>
      ⟨by rw [hab.1]; exact Steps.WP.cons (exec_shift_d (by decide)) (WP.block_nil rfl),
       by rw [hab.2]; exact Steps.WP.cons (exec_shift_d (by decide)) (WP.block_nil rfl)⟩) (fun _ _ h => h)
      fun _ _ h => h) ?_
  refine RelCT.ite (fun a b hab => by
    rw [hab.1, hab.2, eval_zero, eval_zero, (Upd.write _ _ _).gpr, (Upd.write _ _ _).gpr, p7]) ?_ ?_
  · have hu₁ := Upd.write s₁ .t1 (s₁.gpr .a4 >>> 8)
    have hu₂ := Upd.write s₂ .t1 (s₂.gpr .a4 >>> 8)
    -- The setup.
    refine RelCT.seq (R := fun a b => MV1 p STK s₁ signRegs (cachedV p s₁) a ∧
        MV1 p STK s₂ signRegs (cachedV p s₂) b)
      (RelCT.mono (relct_wp (ct_prog vcArgs (fun a b hab => by
          rw [hab.1.1, hab.1.2, hu₁.sp, hu₂.sp, psp]) (fun a b hab r hr => by
          rw [hab.1.1, hab.1.2, hu₁.other _ (by revert r; decide), hu₂.other _ (by revert r; decide)]
          exact pr r hr) (cachedEnter_taint p)) fun a b hab => by
          rw [hab.1.1, hab.1.2]
          exact ⟨cachedSetup_ok hF hp₁ hu₁.other hu₁.rd hu₁.wr hu₁.sp rfl hu₁.mem,
            cachedSetup_ok hF hp₂ hu₂.other hu₂.rd hu₂.wr hu₂.sp rfl hu₂.mem⟩) (fun _ _ h => h) fun _ _ h => h) ?_
    -- `μ`.
    refine RelCT.seq (R := fun a b => MV3 p STK s₁ signRegs (cachedV p s₁) a ∧
        MV3 p STK s₂ signRegs (cachedV p s₂) b)
      (relct_wp (hash_ct (by taint_decide) fun a b h =>
          ⟨mu_hashOk hp₁ h48 (vl_cached p s₁) h.1.inv (trPiece_ok hc₁ h48 h.1.inv),
            mu_hashOk hp₂ h48 (vl_cached p s₂) h.2.inv (trPiece_ok hc₂ h48 h.2.inv),
            h.1.inv.sp.trans (psp.trans h.2.inv.sp.symm), fun r hr => vinvG_regs hV h.1.inv h.2.inv r
              (by revert r hr; decide)⟩)
        fun a b hab => ⟨cachedHash_ok hc₁ h48 hab.1, cachedHash_ok hc₂ h48 hab.2⟩) ?_
    -- The call.
    refine RelCT.seq (R := fun a b => VInvG p STK s₁ signRegs (cachedV p s₁) a ∧
        VInvG p STK s₂ signRegs (cachedV p s₂) b)
      (relct_wp ?_ fun a b hab => ⟨WP.mono (verifyCall_ok (vl_cached p s₁) hF hp₁ hc₁.kp hf hS hab.1) fun _ h => h.1,
        WP.mono (verifyCall_ok (vl_cached p s₂) hF hp₂ hc₂.kp hf hS hab.2) fun _ h => h.1⟩)
      (ct_prog [.s8] (fun a b hab => hab.1.sp.trans (psp.trans hab.2.sp.symm))
        (fun a b hab r hr => by rw [List.mem_singleton.mp hr]; exact vinvG_regs hV hab.1 hab.2 _ (by decide))
        (by taint_decide))
    exact verifyCall_ct (n := n) hF hf hS (vl_cached p s₁) (vl_cached p s₂) hp₁ hp₂ hc₁.kp hc₂.kp psp pv hV ek em ec eg
  · -- `ctx_len ≥ 256`.
    exact ct_prog [] (fun a b hab => by rw [hab.1.1, hab.1.2, (Upd.write _ _ _).sp, (Upd.write _ _ _).sp, psp])
      (fun _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide)

end VG.Proof.MlDsa.RISCV64.Message
