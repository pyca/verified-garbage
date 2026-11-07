module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Fn
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Fn
meta import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT

/-!
# AES-GCM decryption out of place, by a copy, PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs whose stack pointer,
arguments and leak agree (`toPub`) leak the same trace, related piece by
piece from the states the correctness proof describes (`Gather.PPC64LE.Eq2`):
the frame's push, the entry, the loads of the call's arguments and of the
return address are at the stack pointer or our frame; the copy is constant
time by the taint analysis from its arguments `src`, `len` and `dst`; the
call is constant time by its callee's contract, whose public data (its
arguments and whether it succeeds, `Ready.leak`) agree; the branch after it
is on whether the tag is right, our leak (`Called.zero`); and `wipe`'s loop
runs on `dst` and `len`. As for `vg_aes_gcm_seal_gather`
(`Gather/CT.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.PPC64LE.OpenTo

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq rel_taint rel_ite ct_of)

/-- The call's public data, from the arguments. -/
theorem Ready.leak {s c : State} (h : Lay s) (hc : Ready s c) : callLeak (xS s c) = toLeak s := by
  obtain ⟨-, c4, -⟩ := hc.callGpr (rdC s) (wrC s)
  simp only [callLeak, toLeak, hc.xres h, c4]

/-- Whether the call failed, from what it left. -/
theorem Called.zero {s z : State} (hz : Called s z) : ((z.gpr .r3).setWidth 32 == 0) = (res s).isNone := by
  have ho := hz.out
  unfold Out at ho
  revert ho
  cases res s with
  | some pt => intro ho; rw [ho.1]; rfl
  | none => intro ho; rw [ho]; rfl

theorem resNone {σ₁ σ₂ : State} (p₁ : ToPre σ₁) (p₂ : ToPre σ₂) (ql : toLeak σ₁ = toLeak σ₂) :
    (res σ₁).isNone = (res σ₂).isNone := by
  simp only [toLeak, p₁.hR, p₂.hR, not_true_eq_false, ↓reduceIte, List.cons.injEq, and_true] at ql
  revert ql
  cases res σ₁ <;> cases res σ₂ <;> simp

theorem openTo_ct (hv : OpenOk)
    (hct : ConstantTime isa (Proof.AesGcm.openRoundsContract PPC64LE.abi 2688).pre
      (Proof.AesGcm.openRoundsContract PPC64LE.abi 2688).pub openCode) :
    ConstantTime isa ToPre toPub openTo := by
  refine ct_of fun s₁ s₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨qsp, ql, q3, q4, q5, q6, q7, q8, q9, q10, qa⟩ := hq
  have hP : Pf s₁ = Pf s₂ := by simp only [Pf, Bs, qsp]
  unfold openTo
  refine (RelCT.alloc (P := Eq2 s₁ s₂) (R := TT) (fun a b ⟨ha, hb⟩ => by subst a b; exact qsp)
    ((?_ : RelCT isa (Eq2 (allocated 160 s₁) (allocated 160 s₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst s t; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
      (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (show s₁.sp - BitVec.ofNat 64 160 = s₂.sp - BitVec.ofNat 64 160 by rw [qsp])
    (by simp) (by taint_decide)) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The copy, from the same arguments.
  refine rel_seq (rel_taint [.r3, .r4, .r9] (by rw [he₁.sp, he₂.sp, hP])
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨by rw [he₁.r3, he₂.r3, Src, Src, q9], by rw [he₁.r4, he₂.r4, q10],
        by rw [he₁.r9, he₂.r9, Dst, Dst, qa 0 (by decide)]⟩)
    (by taint_decide)) (copied_wp h₁ he₁) (copied_wp h₂ he₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_taint [.r12] (by rw [hc₁.sp, hc₂.sp, hP]) (by simp [hc₁.r12, hc₂.r12, hP])
    (by taint_decide)) (ready_wp h₁ hc₁) (ready_wp h₂ hc₂) fun r₁ r₂ hr₁ hr₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC s₂ = rdC s₁ := by
    simp only [rdC, kR, nR, aR, tR, C, Nn, NL, Ad, AL, Tg, TL, fa, Pf, Bs, q3, q5, q6, q7, q8,
      qa 2 (by decide), qa 3 (by decide), qsp]
  have hwr : wrC s₂ = wrC s₁ := by simp only [wrC, dR, Dst, L, qa 0 (by decide), q10]
  have hx₂ : xS s₂ r₂ = r₂.callEntry.withRegions (rdC s₁) (wrC s₁) := by rw [← hrd, ← hwr]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hr₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hr₂.call h₂
  have lk₁ := hr₁.leak h₁
  have lk₂ := hr₂.leak h₂
  rw [hx₂] at cp₂ lk₂
  rw [hrd, hwr] at cv₂
  rw [hwr] at cw₂
  obtain ⟨g3₁, g4₁, g5₁, g6₁, g7₁, g8₁, g9₁, g10₁⟩ := hr₁.callGpr (rdC s₁) (wrC s₁)
  obtain ⟨g3₂, g4₂, g5₂, g6₂, g7₂, g8₂, g9₂, g10₂⟩ := hr₂.callGpr (rdC s₁) (wrC s₁)
  obtain ⟨a0₁, a1₁⟩ := hr₁.args h₁ (rdC s₁) (wrC s₁)
  obtain ⟨a0₂, a1₂⟩ := hr₂.args h₂ (rdC s₁) (wrC s₁)
  refine rel_seq (RelCT.call hv hct (rdC s₁) (wrC s₁) fun x y ⟨hx, hy⟩ => by
      subst hx hy
      refine ⟨openSpec_pre cp₁, openSpec_pre cp₂, openSpec_pub ⟨?_, by rw [lk₁, lk₂, ql], ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_⟩, cv₁, cw₁, cv₂, cw₂⟩
      · simp only [State.withRegions_sp, State.callEntry_sp, hr₁.sp, hr₂.sp, hP]
      · rw [g3₁, g3₂, C, C, q3]
      · rw [g4₁, g4₂, q4]
      · rw [g5₁, g5₂, Nn, Nn, q5]
      · rw [g6₁, g6₂, q6]
      · rw [g7₁, g7₂, Ad, Ad, q7]
      · rw [g8₁, g8₂, q8]
      · rw [g9₁, g9₂, Dst, Dst, qa 0 (by decide)]
      · rw [g10₁, g10₂, q10]
      · rw [a0₁, a0₂, Tg, Tg, qa 2 (by decide)]
      · rw [a1₁, a1₂, qa 3 (by decide)])
    (called_wp hv h₁ hr₁) (called_wp hv h₂ hr₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- After the call: the same branch in both runs.
  have hn := resNone p₁ p₂ ql
  refine rel_seq ?_ (after_wp h₁ hz₁) (after_wp h₂ hz₂) fun u₁ u₂ hu₁ hu₂ => ?_
  · unfold after
    have ev₁ : isa.eval (.zero .w .r3) z₁ = some (res s₁).isNone := by rw [eval_zero_w, hz₁.zero]
    have ev₂ : isa.eval (.zero .w .r3) z₂ = some (res s₁).isNone := by rw [eval_zero_w, hz₂.zero, hn]
    refine rel_ite ev₁ ev₂ (fun _ => ?_) fun _ => ?_
    swap
    · exact rel_taint [] (by rw [hz₁.sp, hz₂.sp, hP]) (by simp) (by taint_decide)
    -- `wipe`, from the same public arguments.
    unfold wipe
    refine rel_seq (rel_taint [] (by rw [hz₁.sp, hz₂.sp, hP]) (by simp) (by taint_decide))
      (wipeArgs_wp h₁ hz₁) (wipeArgs_wp h₂ hz₂) fun w₁ w₂ hw₁ hw₂ => ?_
    exact rel_taint [.r9, .r10] (by rw [hw₁.sp, hw₂.sp, hz₁.sp, hz₂.sp, hP])
      (by
        simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        exact ⟨by rw [hw₁.r9, hw₂.r9, Dst, Dst, qa 0 (by decide)], by rw [hw₁.r10, hw₂.r10, L, L, q10]⟩)
      (by taint_decide)
  -- Our return address.
  exact rel_taint [] (by rw [hu₁.sp, hu₂.sp, hP]) (by simp) (by taint_decide)

end VG.Proof.AesGcm.PPC64LE.OpenTo
