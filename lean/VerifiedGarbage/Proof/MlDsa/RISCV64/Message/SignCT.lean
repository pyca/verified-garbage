module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Sign
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Sha3.RISCV64.PiecesCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.Message.Common
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Sign
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
# ML-DSA on RISC-V, `sign_message`: constant time

Two runs from states that satisfy `MSPre` and agree on the arguments in
registers, the stack pointer and `signMessageLeak` (`MSPub`) leak the same
trace (`signMessage_ct`): the length check and the branch on it from
`ctx_len`; the setup from the arguments (`enter_taint`); the hash of `μ` by
`hash_ct`, from the registers the invariant gives the same values in both
runs; the arguments of the call and the restores by the taint analysis
(`ct_prog`); and the call of the signing function on `μ` by its own
constant time, whose leakage `signLeak` of the key, `μ` and the randomness
is `signMessageLeak` of the inputs.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Message
open VG.Impl.Sha3.RISCV64.Pieces (Piece hash)
open VG.Proof.Sha3.RISCV64.Pieces (HashOk hashRegs hash_ct)
open VG.RISCV64.Steps (Upd)
open VG.Proof.MlDsa.RISCV64.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Code the taint analysis checks from the registers `rs`, on which the runs agree. -/
theorem ct_prog {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.RISCV64.taint.T} (h : (VG.RISCV64.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨hsp a b hab, fun r hr => hP a b hab r (Taint.mem_ofRegs.mp hr)⟩) h

/-- The argument registers of `sign_message`. -/
abbrev mArgs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The setup, from the arguments, for any parameter set: the taint analysis reads no immediate. -/
theorem enter_taint (p : Params) : (VG.RISCV64.taint.check (Taint.ofRegs mArgs)
    (.block (enter .a7 p signRegs signMs))
    (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs mArgs) (.block (enter .a7 mlDsa44 signRegs signMs)))).isSome =
    true := rfl

/-- What two runs agree on: `signMessageContract`'s public part. -/
def MSPub (p : Params) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧
    signMessageLeak p (skB p s₁) (msgB s₁) (ctxB s₁) (rndB s₁) =
      signMessageLeak p (skB p s₂) (msgB s₂) (ctxB s₂) (rndB s₂) ∧
    ∀ r ∈ mArgs, s₁.gpr r = s₂.gpr r

theorem signV_eq {p : Params} {s₁ s₂ : State} (h : ∀ r ∈ mArgs, s₁.gpr r = s₂.gpr r) :
    ∀ r ∈ signRegs, signV p s₁ r = signV p s₂ r := by
  intro r hr
  simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 8 exact h _ (by decide)
  show eAt p (s₁.gpr .a7) = eAt p (s₂.gpr .a7)
  rw [h .a7 (by decide)]

theorem sinv_regs {p : Params} {STK : Nat} {s₁ s₂ a b : State} (h : ∀ r ∈ mArgs, s₁.gpr r = s₂.gpr r)
    (ha : SInv p STK s₁ a) (hb : SInv p STK s₂ b) : ∀ r ∈ signRegs, a.gpr r = b.gpr r := fun r hr =>
  (ha.regs r hr).trans ((signV_eq h r hr).trans (hb.regs r hr).symm)

/-- The hash of `μ` may run. -/
theorem ms1_hashOk {p : Params} {q : Bool} {STK : Nat} {s t : State} (hF : MFacts p) (hp : MSPre p q STK s) (h48 : 1168 ≤ STK)
    (h : MS1 p STK s t) :
    HashOk 840 64 .s8 .s8 oMU ((⟨.s0, 64, .imm 64⟩ : Piece) :: fmtPieces) t := by
  have hi := h.inv
  obtain ⟨ke, hin⟩ := signHash_env hF hp h48 hi
  have g30 := s_e hi
  exact ⟨by decide, by decide, by decide, by decide, by simp, by rw [g30]; exact ke, by rw [g30]; exact hin,
    by rw [g30]; exact e_cov hp hi.wr (by decide), by rw [g30]; exact (e_e0 (by decide) (by decide)).symm,
    by rw [g30, hi.sp]; exact (hp.bx.sub_left (below48 hp h48)).sub_right (e_sub (by decide))⟩

theorem signMessage_ct {p : Params} {q : Bool} {STK S : Nat} (hF : MFacts p) (h48 : 1168 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => PreparedKey.signEK p q stk) S) (hS : S ≤ STK) {n : String} :
    ConstantTime isa (MSPre p q STK) (MSPub p) (signMessage n f p) := by
  obtain ⟨stk, hstk, hver⟩ := hf.verified
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ MSPre p q STK x.1 ∧ MSPre p q STK x.2 ∧
    MSPub p x.1 x.2) (RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩) (fun _ _ h => h)
  by_cases hH : MSPre p q STK s₁ ∧ MSPre p q STK s₂ ∧ MSPub p s₁ s₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨hp₁, hp₂, psp, pl, pr⟩ := hH
  refine RelCT.mono (P := fun a b => a = s₁ ∧ b = s₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have p7 : s₁.gpr .a4 = s₂.gpr .a4 := pr _ (by decide)
  unfold signMessage top
  -- The length check.
  refine RelCT.seq (R := fun a b => a = s₁.write .t1 (s₁.gpr .a4 >>> 8) ∧ b = s₂.write .t1 (s₂.gpr .a4 >>> 8))
    (RelCT.mono (relct_wp (ct_prog [.a4] (fun a b hab => by rw [hab.1, hab.2, psp])
      (fun a b hab r hr => by rw [List.mem_singleton.mp hr, hab.1, hab.2, p7]) (by taint_decide)) fun a b hab =>
      ⟨by rw [hab.1]; exact Steps.WP.cons (exec_shift_d (by decide)) (WP.block_nil rfl),
       by rw [hab.2]; exact Steps.WP.cons (exec_shift_d (by decide)) (WP.block_nil rfl)⟩) (fun _ _ h => h)
      fun _ _ h => h) ?_
  refine RelCT.ite (fun a b hab => by
    rw [hab.1, hab.2, eval_zero, eval_zero, (Upd.write _ _ _).gpr, (Upd.write _ _ _).gpr, p7]) ?_ ?_
  · by_cases hcl : (s₁.gpr .a4).toNat < 256
    swap
    · refine RelCT.of_false fun a b ⟨hab, hc⟩ => hcl ?_
      rw [hab.1, eval_zero, (Upd.write _ _ _).gpr, shr8_zero] at hc
      exact of_decide_eq_true (Option.some.inj hc)
    have hcl₂ : (s₂.gpr .a4).toNat < 256 := by rw [← p7]; exact hcl
    have hu₁ := Upd.write s₁ .t1 (s₁.gpr .a4 >>> 8)
    have hu₂ := Upd.write s₂ .t1 (s₂.gpr .a4 >>> 8)
    -- The setup.
    refine RelCT.seq (R := fun a b => MS1 p STK s₁ a ∧ MS1 p STK s₂ b)
      (RelCT.mono (relct_wp (ct_prog mArgs (fun a b hab => by
          rw [hab.1.1, hab.1.2, hu₁.sp, hu₂.sp, psp]) (fun a b hab r hr => by
          rw [hab.1.1, hab.1.2, hu₁.other _ (by revert r; decide), hu₂.other _ (by revert r; decide)]
          exact pr r hr) (enter_taint p)) fun a b hab => by
          rw [hab.1.1, hab.1.2]
          exact ⟨signSetup_ok hF hp₁ hu₁.other hu₁.rd hu₁.wr hu₁.sp rfl hu₁.mem,
            signSetup_ok hF hp₂ hu₂.other hu₂.rd hu₂.wr hu₂.sp rfl hu₂.mem⟩) (fun _ _ h => h) fun _ _ h => h) ?_
    -- `μ`.
    refine RelCT.seq (R := fun a b => MS2 p STK s₁ a ∧ MS2 p STK s₂ b)
      (relct_wp (hash_ct (by taint_decide) fun a b h => ⟨ms1_hashOk hF hp₁ h48 h.1, ms1_hashOk hF hp₂ h48 h.2,
          h.1.inv.sp.trans (psp.trans h.2.inv.sp.symm), fun r hr => sinv_regs pr h.1.inv h.2.inv r
            (by revert r hr; decide)⟩)
        fun a b hab => ⟨signHash_ok hF hp₁ h48 hab.1, signHash_ok hF hp₂ h48 hab.2⟩) ?_
    -- The call.
    refine RelCT.seq (R := fun a b => SInv p STK s₁ a ∧ SInv p STK s₂ b)
      (relct_wp ?_ fun a b hab => ⟨WP.mono (signCall_ok hF hp₁ hf hS hab.1) fun _ h => h.1,
        WP.mono (signCall_ok hF hp₂ hf hS hab.2) fun _ h => h.1⟩)
      (ct_prog [.s8] (fun a b hab => hab.1.sp.trans (psp.trans hab.2.sp.symm))
        (fun a b hab r hr => by rw [List.mem_singleton.mp hr]; exact sinv_regs pr hab.1 hab.2 _ (by decide))
        (by taint_decide))
    refine RelCT.seq (R := fun a b => SA p STK s₁ a ∧ SA p STK s₂ b)
      (relct_wp (ct_prog [.s0, .s5, .s6, .s7, .s8] (fun a b hab => hab.1.inv.sp.trans (psp.trans hab.2.inv.sp.symm))
        (fun a b hab r hr => sinv_regs pr hab.1.inv hab.2.inv r (by revert r hr; decide)) (by taint_decide))
        fun a b hab => ⟨signArgs_ok hab.1, signArgs_ok hab.2⟩) ?_
    refine RelCT.call hver.1 hver.2.1 (sRd p q s₁) (sWr p s₁) fun a b hab => ?_
    have hpre₁ := signCall_pre hF hp₁ (Nat.le_trans hstk hS) hab.1
    have hpre₂ := signCall_pre hF hp₂ (Nat.le_trans hstk hS) hab.2
    have eRd : sRd p q s₂ = sRd p q s₁ := by simp only [sRd, skR, rndR, pr _ (by decide : Reg.a0 ∈ mArgs),
      pr _ (by decide : Reg.a5 ∈ mArgs), pr _ (by decide : Reg.a7 ∈ mArgs)]
    have eWr : sWr p s₂ = sWr p s₁ := by simp only [sWr, sigR, pr _ (by decide : Reg.a6 ∈ mArgs),
      pr _ (by decide : Reg.a7 ∈ mArgs)]
    rw [eRd, eWr] at hpre₂
    refine ⟨hpre₁.1, hpre₂.1, ?_, hpre₁.2.1, hpre₁.2.2, hpre₂.2.1, hpre₂.2.2⟩
    have k₁ := hab.1.ms.inv
    have k₂ := hab.2.ms.inv
    refine sign_pub (by simp only [State.withRegions_sp, State.callEntry_sp, k₁.sp, k₂.sp, psp]) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a0, hab.2.a0, pr _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a1, hab.2.a1, pr _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a2, hab.2.a2, pr _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a3, hab.2.a3, pr _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a4, hab.2.a4, pr _ (by decide)]
    · simp only [State.withRegions_mem, State.callEntry_mem, ce_gpr _ _ _ (show Reg.a0 ∉ linkRegs by decide),
        ce_gpr _ _ _ (show Reg.a1 ∉ linkRegs by decide), ce_gpr _ _ _ (show Reg.a2 ∉ linkRegs by decide),
        hab.1.a0, hab.1.a1, hab.1.a2, hab.2.a0, hab.2.a1, hab.2.a2]
      have ks := skE_sub hF q
      have hl : p.skLen < 2 ^ 64 := by have := hF.skl; omega
      rw [s_keep k₁ (R := ⟨s₁.gpr .a0, p.skLen⟩) hl (hp₁.kg.sub_left (ks s₁)) (hp₁.kc.sub_left (ks s₁))
          (hp₁.bk.sub_right (ks s₁)),
        hab.1.ms.mu, s_keep k₁ (R := rndR s₁) (show (32 : Nat) < 2 ^ 64 by decide) hp₁.rg hp₁.rc hp₁.br,
        s_keep k₂ (R := ⟨s₂.gpr .a0, p.skLen⟩) hl (hp₂.kg.sub_left (ks s₂)) (hp₂.kc.sub_left (ks s₂))
          (hp₂.bk.sub_right (ks s₂)),
        hab.2.ms.mu, s_keep k₂ (R := rndR s₂) (show (32 : Nat) < 2 ^ 64 by decide) hp₂.rg hp₂.rc hp₂.br]
      simp only [signMessageLeak] at pl
      rw [Proof.MlDsa.Message.formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hcl),
        Proof.MlDsa.Message.formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hcl₂)] at pl
      simp only [Proof.MlKem.bytesAt_length] at pl
      exact pl
  · -- `ctx_len ≥ 256`.
    exact ct_prog [] (fun a b hab => by rw [hab.1.1, hab.1.2, (Upd.write _ _ _).sp, (Upd.write _ _ _).sp, psp])
      (fun _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide)

end VG.Proof.MlDsa.RISCV64.Message
