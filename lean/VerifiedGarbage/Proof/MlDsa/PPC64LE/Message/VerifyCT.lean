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
meta import VerifiedGarbage.Impl.MlDsa.PPC64LE.Message
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Message

/-!
# ML-DSA on PPC64LE, `verify_message_cached`: constant time

As signing's (`SignCT.lean`): two runs from states that satisfy `MCPre` and
agree on the arguments in registers, the stack pointer and the inputs, the
leakage of `verifyMessageCachedContract` (`MCPub`), leak the same trace
(`verifyMessageCached_ct`). The hash of `μ` is related by `hash_ct`, and the
call of the verification function on `μ` by its own constant time, whose
leakage is its inputs: the key and the signature, and `μ`, which both runs
compute from the same inputs. The leakage leaves out `tr`, which both runs
hold equal to `H(pk, 64)`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Message

open VG VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Message
open VG.Impl.Sha3.PPC64LE.Pieces (Piece hash)
open VG.Proof.Sha3.PPC64LE.Pieces (HashOk PieceOk hash_ct)
open VG.Proof.MlKem.PPC64LE.Sample (relct_wp)
open VG.Proof.X25519.PPC64LE (Upd WP.cons)
open VG.Proof.MlDsa.PPC64LE.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The argument registers of `verify_message_cached` but `tr` (`r10`). -/
abbrev vArgs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9]

/-- The registers the invariant keeps, which the arguments, `tr` (`r10`) among
them, determine. -/
theorem verifyV_eq {p : Params} {s₁ s₂ : State} (h : ∀ r ∈ vArgs, s₁.gpr r = s₂.gpr r)
    (h10 : s₁.gpr .r10 = s₂.gpr .r10) : ∀ r ∈ cachedRegs, verifyV p s₁ r = verifyV p s₂ r := by
  intro r hr
  simp only [cachedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 6 exact h _ (by decide)
  · exact h10
  · exact h _ (by decide)
  show eAt p (s₁.gpr .r9) = eAt p (s₂.gpr .r9)
  rw [h .r9 (by decide)]

theorem vinv_regs {p : Params} {STK : Nat} {s₁ s₂ a b : State} (h : ∀ r ∈ vArgs, s₁.gpr r = s₂.gpr r)
    (h10 : s₁.gpr .r10 = s₂.gpr .r10) (ha : VInv p STK s₁ a) (hb : VInv p STK s₂ b) :
    ∀ r ∈ cachedRegs, a.gpr r = b.gpr r := fun r hr =>
  (ha.regs r hr).trans ((verifyV_eq h h10 r hr).trans (hb.regs r hr).symm)

section
variable {p : Params} {pr : Bool} {STK : Nat} {s t : State} (hF : MFacts p) (hp : MVPre p pr STK s) (h48 : 48 ≤ STK)
include hF hp h48

omit hF in
/-- The hash of `μ`, from the piece `tr`. -/
theorem mu_hashOk {tr : Piece} (hi : VInv p STK s t) (htr : PieceOk 840 (eAt p (s.gpr .r9)) t tr) :
    HashOk 840 64 .r30 .r30 oMU (tr :: fmtPieces) t := by
  have g30 := v_e hi
  exact ⟨by decide, by decide, by decide, by decide, by simp, by rw [g30]; exact vke hp h48 hi,
    by rw [g30]; exact muHash_ins hp h48 hi htr, by rw [g30]; exact ve_cov hp hi.wr (by decide),
    by rw [g30]; exact (e_e0 (by decide) (by decide)).symm,
    by rw [g30, hi.sp]; exact (hp.bx.sub_left (vbelow48 hp h48)).sub_right (e_sub (by decide))⟩

end

/-- The argument registers of `verify_message_cached`. -/
abbrev cArgs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

theorem center_taint (p : Params) : (VG.PPC64LE.taint.check (Taint.ofRegs cArgs)
    (.block (enter .r9 p cachedRegs cachedMs))
    (VG.Taint.hintOf VG.PPC64LE.taint (Taint.ofRegs cArgs) (.block (enter .r9 mlDsa44 cachedRegs cachedMs)))).isSome =
    true := rfl

/-- What two runs agree on: `verifyMessageCachedContract`'s public part. -/
def MCPub (p : Params) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧
    leakBytes (pkB p s₁ ++ msgB s₁ ++ ctxB s₁ ++ vsigB p s₁) = leakBytes (pkB p s₂ ++ msgB s₂ ++ ctxB s₂ ++ vsigB p s₂) ∧
    ∀ r ∈ cArgs, s₁.gpr r = s₂.gpr r

theorem verifyMessageCached_ct {p : Params} {pr : Bool} {STK S : Nat} (hF : MFacts p) (h48 : 48 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => verifyK p pr PPC64LE.abi stk) S) (hS : S ≤ STK) {n : String} :
    ConstantTime isa (MCPre p pr STK) (MCPub p) (verifyMessageCached n f p) := by
  obtain ⟨stk, hstk, hver⟩ := hf.verified
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ MCPre p pr STK x.1 ∧ MCPre p pr STK x.2 ∧
    MCPub p x.1 x.2) (RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩) (fun _ _ h => h)
  by_cases hH : MCPre p pr STK s₁ ∧ MCPre p pr STK s₂ ∧ MCPub p s₁ s₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨hp₁, hp₂, psp, pl, pc⟩ := hH
  have preg : ∀ r ∈ vArgs, s₁.gpr r = s₂.gpr r := fun r hr => pc r (show r ∈ vArgs ++ [.r10] from List.mem_append_left _ hr)
  have p10 : s₁.gpr .r10 = s₂.gpr .r10 := pc _ (by decide)
  refine RelCT.mono (P := fun a b => a = s₁ ∧ b = s₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have p7 : s₁.gpr .r7 = s₂.gpr .r7 := preg _ (by decide)
  obtain ⟨ek, em, ec, eg⟩ := Proof.MlDsa.Message.leak4 (by simp [Proof.MlKem.bytesAt_length])
    (by simp [Proof.MlKem.bytesAt_length, preg .r5 (by decide)]) (by simp [Proof.MlKem.bytesAt_length, p7]) pl
  unfold verifyMessageCached top
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
      (RelCT.mono (relct_wp (ct_prog cArgs (fun a b hab => by
          rw [hab.1.1, hab.1.2, hu₁.sp, hu₂.sp, psp]) (fun a b hab r hr => by
          rw [hab.1.1, hab.1.2, hu₁.other _ (by revert r; decide), hu₂.other _ (by revert r; decide)]
          exact pc r hr) (center_taint p)) fun a b hab => by
          rw [hab.1.1, hab.1.2]
          exact ⟨cachedSetup_ok hF hp₁ hu₁.other hu₁.rd hu₁.wr hu₁.sp rfl hu₁.mem,
            cachedSetup_ok hF hp₂ hu₂.other hu₂.rd hu₂.wr hu₂.sp rfl hu₂.mem⟩) (fun _ _ h => h) fun _ _ h => h) ?_
    -- `μ`.
    refine RelCT.seq (R := fun a b => MV3 p STK s₁ a ∧ MV3 p STK s₂ b)
      (relct_wp (hash_ct (by taint_decide) fun a b h =>
          ⟨mu_hashOk hp₁.toMVPre h48 h.1.inv (cachedTr_ok hp₁ h48 h.1.inv),
          mu_hashOk hp₂.toMVPre h48 h.2.inv (cachedTr_ok hp₂ h48 h.2.inv),
          h.1.inv.sp.trans (psp.trans h.2.inv.sp.symm), fun r hr => vinv_regs preg p10 h.1.inv h.2.inv r
            (by revert r hr; decide)⟩)
        fun a b hab => ⟨cachedHash_ok hp₁ h48 hab.1, cachedHash_ok hp₂ h48 hab.2⟩) ?_
    -- The call.
    refine RelCT.seq (R := fun a b => VInv p STK s₁ a ∧ VInv p STK s₂ b)
      (relct_wp ?_ fun a b hab => ⟨WP.mono (verifyCall_ok hF hp₁.toMVPre hf hS hab.1 hp₁.x) fun _ h => h.1,
        WP.mono (verifyCall_ok hF hp₂.toMVPre hf hS hab.2 hp₂.x) fun _ h => h.1⟩)
      (ct_prog [.r30] (fun a b hab => hab.1.sp.trans (psp.trans hab.2.sp.symm))
        (fun a b hab r hr => by
          rw [List.mem_singleton.mp hr]; exact vinv_regs preg p10 hab.1 hab.2 _ (by decide))
        (by taint_decide))
    refine RelCT.seq (R := fun a b => VA p STK s₁ a ∧ VA p STK s₂ b)
      (relct_wp (ct_prog [.r22, .r27, .r29, .r30] (fun a b hab => hab.1.inv.sp.trans (psp.trans hab.2.inv.sp.symm))
        (fun a b hab r hr => vinv_regs preg p10 hab.1.inv hab.2.inv r (by revert r hr; decide))
        (by taint_decide))
        fun a b hab => ⟨verifyArgs_ok hab.1, verifyArgs_ok hab.2⟩) ?_
    refine RelCT.call hver.1 hver.2.1 (vRd p pr s₁) (vWr p s₁) fun a b hab => ?_
    have hpre₁ := verifyCall_pre hF hp₁.toMVPre (Nat.le_trans hstk hS) hab.1 hp₁.x
    have hpre₂ := verifyCall_pre hF hp₂.toMVPre (Nat.le_trans hstk hS) hab.2 hp₂.x
    have eRd : vRd p pr s₂ = vRd p pr s₁ := by simp only [vRd, pkR, vsigR, preg _ (by decide : Reg.r3 ∈ vArgs),
      preg _ (by decide : Reg.r8 ∈ vArgs), preg _ (by decide : Reg.r9 ∈ vArgs)]
    have eWr : vWr p s₂ = vWr p s₁ := by simp only [vWr, preg _ (by decide : Reg.r9 ∈ vArgs)]
    rw [eRd, eWr] at hpre₂
    refine ⟨hpre₁.1, hpre₂.1, ?_, hpre₁.2.1, hpre₁.2.2, hpre₂.2.1, hpre₂.2.2⟩
    have k₁ := hab.1.ms.inv
    have k₂ := hab.2.ms.inv
    refine verify_pub (by simp only [State.withRegions_sp, State.callEntry_sp, k₁.sp, k₂.sp, psp]) ?_ ?_ ?_ ?_ ?_
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.r3, hab.2.r3, preg _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.r4, hab.2.r4, preg _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.r5, hab.2.r5, preg _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.r6, hab.2.r6, preg _ (by decide)]
    · simp only [State.withRegions_mem, State.callEntry_mem, ce_gpr _ _ _ (show Reg.r3 ∉ linkRegs by decide),
        ce_gpr _ _ _ (show Reg.r4 ∉ linkRegs by decide), ce_gpr _ _ _ (show Reg.r5 ∉ linkRegs by decide),
        hab.1.r3, hab.1.r4, hab.1.r5, hab.2.r3, hab.2.r4, hab.2.r5]
      rw [v_keep k₁ (R := ⟨s₁.gpr .r3, p.pkLen⟩) (by have := hF.pk; show p.pkLen < 2 ^ 64; omega)
          (hp₁.kc.sub_left hp₁.subK) (hp₁.bk.sub_right hp₁.subK),
        hab.1.ms.mu, v_keep k₁ (R := vsigR p s₁) (by have := hF.sgl; show p.sigLen < 2 ^ 64; omega) hp₁.gc hp₁.bg,
        v_keep k₂ (R := ⟨s₂.gpr .r3, p.pkLen⟩) (by have := hF.pk; show p.pkLen < 2 ^ 64; omega)
          (hp₂.kc.sub_left hp₂.subK) (hp₂.bk.sub_right hp₂.subK),
        hab.2.ms.mu, v_keep k₂ (R := vsigR p s₂) (by have := hF.sgl; show p.sigLen < 2 ^ 64; omega) hp₂.gc hp₂.bg]
      simp only [pkB, vsigB, fmtB, ctxB, msgB] at ek em ec eg ⊢
      rw [ek, em, ec, eg, p7]
  · -- `ctx_len ≥ 256`.
    exact ct_prog [] (fun a b hab => by rw [hab.1.1, hab.1.2, (Upd.write _ _ _).sp, (Upd.write _ _ _).sp, psp])
      (fun _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide)

end VG.Proof.MlDsa.PPC64LE.Message
