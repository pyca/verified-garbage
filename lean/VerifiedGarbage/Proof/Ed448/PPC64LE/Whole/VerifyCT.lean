module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.VerifyMsg
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignCT
import VerifiedGarbage.Proof.Ed448.PPC64LE.VCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.VerifyMsg
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignCT
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.VCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Calls
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.VVerified
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Calls
public import VerifiedGarbage.Impl.Ed448.PPC64LE.Whole
public import VerifiedGarbage.Proof.Ed448.PPC64LE.VVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# `vg_ed448_verify` on PPC64LE in constant time

Two runs from states that satisfy `VerPre` and agree on the arguments in
registers and the stack pointer (`VPub`) leak the same trace
(`verifyMessage_ct`): the length check and the branch on it from `ctxlen`,
the setup from the arguments, the challenge by `hash_then` (the hash, then
the reduction and the arguments of `verify_equation` from `r20`–`r23`), the
call of `verify_equation` by its own constant time, which needs only its
pointers to agree (`veqK`, `RelCT.callEx`), and the restores from `F` in
`r23`.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole
open VG.Proof.MlKem.PPC64LE.Sample (relct_wp)
open VG.Spec.Ed448 (bytesAt)

/-- What two runs agree on: the arguments in registers and the stack pointer. -/
def VPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp

theorem verV_eq {s₁ s₂ : State} (hp : VPub s₁ s₂) : ∀ r ∈ verifyRegs, verV s₁ r = verV s₂ r := by
  obtain ⟨p3, p4, p5, p6, p7, p8, p9, p10, -⟩ := hp
  intro r hr
  simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [p3, p8, p9, p4, p5, p6, p7, p10]

theorem vinv_regs {s₁ s₂ a b : State} (hp : VPub s₁ s₂) (ha : VInv s₁ a) (hb : VInv s₂ b) :
    ∀ r ∈ verifyRegs, a.gpr r = b.gpr r := fun r hr =>
  (ha.regs r hr).trans ((verV_eq hp r hr).trans (hb.regs r hr).symm)

theorem vinv_sp {s₁ s₂ a b : State} (hp : VPub s₁ s₂) (ha : VInv s₁ a) (hb : VInv s₂ b) : a.sp = b.sp :=
  ha.sp.trans (hp.2.2.2.2.2.2.2.2.trans hb.sp.symm)

/-- `verify_equation`'s contract with only its pointers and the stack pointer public, which is all its constant
time needs. -/
def veqK : Contract isa :=
  { Proof.Ed448.PPC64LE.verifyPPC with
    pub := fun s₁ s₂ => s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r3, .r4, .r5, .r6], s₁.gpr r = s₂.gpr r }

/-- The narrowed state `verify_equation` starts in, and its regions' cover. -/
theorem veq_pre {s t : State} (hp : VerPre s) (h : VArgs s t) :
    veqK.pre (t.callEntry.withRegions [⟨s.gpr .r3, 57⟩, ⟨s.gpr .r8, 114⟩, ⟨s.gpr .r10 + BitVec.ofNat 64 136, 57⟩]
      [vscR s]) ∧
    PPC64LE.Covers ([⟨s.gpr .r3, 57⟩, ⟨s.gpr .r8, 114⟩, ⟨s.gpr .r10 + BitVec.ofNat 64 136, 57⟩] ++ [vscR s])
      (t.rd ++ t.wr) ∧ PPC64LE.Covers [vscR s] t.wr := by
  have cr : ∀ R ∈ [vpkR s, vcxR s, vmsR s, vsgR s], PPC64LE.Covers [R] (t.rd ++ t.wr) := fun R hR => by
    rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact hR, hc⟩
  have hW : PPC64LE.Covers [vscR s] t.wr := fun a n ⟨r, hr, hc⟩ => by
    rw [List.mem_singleton.mp hr] at hc; exact ⟨_, vC hp h.inv, hc⟩
  refine ⟨⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide),
      ce_gpr _ _ _ (by decide), h.r3, h.r4, h.r5],
    by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), h.r6],
    by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h.r3, h.r6]; exact hp.cP.symm,
    by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h.r4, h.r6]; exact hp.cS.symm,
    by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h.r5, h.r6]; exact vfsc hp (by decide)⟩, ?_, hW⟩
  intro a n ⟨r, hr, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact cr _ (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
  · exact cr _ (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
  · exact cov_right (cov_in (vF hp h.inv) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
  · exact cov_right hW a n ⟨_, List.mem_singleton_self _, hc⟩

/-- The state after the length check. -/
abbrev vLen (s : State) : State := s.write .r11 (s.gpr .r5 >>> 8)

theorem verifyMessage_ct (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) :
    ConstantTime isa VerPre VPub verifyMessage := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ VerPre x.1 ∧ VerPre x.2 ∧
    VPub x.1 x.2) (RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩) (fun _ _ h => h)
  by_cases hH : VerPre s₁ ∧ VerPre s₂ ∧ VPub s₁ s₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨hp₁, hp₂, hpub⟩ := hH
  refine RelCT.mono (P := fun a b => a = s₁ ∧ b = s₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have pub := hpub
  obtain ⟨p3, p4, p5, p6, p7, p8, p9, p10, psp⟩ := pub
  unfold verifyMessage verifyMain verifyHash
  -- The length check.
  refine RelCT.seq (R := fun a b => a = vLen s₁ ∧ b = vLen s₂)
    (RelCT.mono (relct_wp (ct_prog [.r5] (fun a b hab => by rw [hab.1, hab.2, psp])
      (fun a b hab r hr => by rw [List.mem_singleton.mp hr, hab.1, hab.2, p5]) (by taint_decide)) fun a b hab =>
      ⟨by rw [hab.1]; exact WP.cons (exec_lsr_d (by decide)) (WP.block_nil rfl),
       by rw [hab.2]; exact WP.cons (exec_lsr_d (by decide)) (WP.block_nil rfl)⟩) (fun _ _ h => h)
      fun _ _ h => h) ?_
  refine RelCT.ite (fun a b hab => by
    rw [hab.1, hab.2, eval_zero, eval_zero, (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).gpr, (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).gpr, p5]) ?_ ?_
  · -- The challenge.
    refine RelCT.seq (R := fun a b => VArgs s₁ a ∧ VArgs s₂ b) ?_ ?_
    · refine RelCT.seq (R := fun a b => V1 s₁ a ∧ V1 s₂ b)
        (relct_wp (ct_prog [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] (fun a b hab => by
          rw [hab.1.1, hab.1.2, (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).sp, (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).sp, psp]) (fun a b hab r hr => by
          rw [hab.1.1, hab.1.2]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            rw [(VG.Proof.X25519.PPC64LE.Upd.write _ _ _).other _ (by decide), (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).other _ (by decide)] <;>
            with_reducible assumption) (by taint_decide)) fun a b hab => by
          rw [hab.1.1, hab.1.2]
          exact ⟨verSetup_ok hp₁ (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).other (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).rd (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).wr
              (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).sp rfl (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).mem,
            verSetup_ok hp₂ (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).other (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).rd (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).wr
              (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).sp rfl (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).mem⟩) ?_
      exact relct_wp (hash_then (by taint_decide) (fun a b h => ⟨(h.1.hashOk hp₁).1, (h.2.hashOk hp₂).1,
          vinv_sp hpub h.1.inv h.2.inv, fun r hr => vinv_regs hpub h.1.inv h.2.inv r (by revert r hr; decide)⟩)
        [.r20, .r21, .r22, .r23] (fun a b h r hr =>
          ⟨verifyRegs_pres r (by revert r; decide), vinv_regs hpub h.1.inv h.2.inv r (by revert r; decide)⟩)
        (by taint_decide)) fun a b hab => ⟨verHash_ok hp₁ hab.1, verHash_ok hp₂ hab.2⟩
    -- The call of `verify_equation`, then the restores.
    refine RelCT.seq (R := fun a b => VInv s₁ a ∧ VInv s₂ b)
      (relct_wp (RelCT.callEx (k := veqK) (Proof.Ed448.PPC64LE.verifyEquation_ok hR hV)
        (Proof.Ed448.PPC64LE.verifyEquation_ct fun _ _ _ _ h => h) fun t₁ t₂ ⟨a₁, a₂⟩ => ?_) fun t₁ t₂ ⟨a₁, a₂⟩ =>
        ⟨WP.mono (verCall_ok hR hV hp₁ a₁) fun _ h => h.1, WP.mono (verCall_ok hR hV hp₂ a₂) fun _ h => h.1⟩)
      (ct_prog [.r23] (fun a b hab => vinv_sp hpub hab.1 hab.2)
        (fun a b hab r hr => by rw [List.mem_singleton.mp hr]; exact vinv_regs hpub hab.1 hab.2 _ (by decide))
        (by taint_decide))
    obtain ⟨q₁, c₁, w₁⟩ := veq_pre hp₁ a₁
    obtain ⟨q₂, c₂, w₂⟩ := veq_pre hp₂ a₂
    refine ⟨_, _, _, _, q₁, q₂, ⟨?_, fun r hr => ?_⟩, c₁, w₁, c₂, w₂⟩
    · rw [State.withRegions_sp, State.withRegions_sp, State.callEntry_sp, State.callEntry_sp, a₁.inv.sp,
        a₂.inv.sp, psp]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), a₁.r3, a₂.r3, p3]
      · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), a₁.r4, a₂.r4, p8]
      · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), a₁.r5, a₂.r5, p10]
      · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), a₁.r6, a₂.r6, p9]
  · -- `ctxlen ≥ 256`.
    exact ct_prog [] (fun a b hab => by rw [hab.1.1, hab.1.2, (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).sp, (VG.Proof.X25519.PPC64LE.Upd.write _ _ _).sp, psp])
      (fun _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide)

end VG.Proof.Ed448.PPC64LE.Whole
