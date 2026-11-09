module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Fn
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Fn
meta import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT

/-!
# AES-GCM decryption out of place, in one pass, PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs whose stack pointer,
arguments and leak agree (`toPub`) leak the same trace, related piece by
piece from the states the correctness proof describes (`Gather.PPC64LE.Eq2`):
the frame's push, the entry and the load of the return address are at the
stack pointer or our frame; the call is constant time by its callee's
contract, whose public data (its arguments and whether it succeeds,
`Entered.leak`) agree; the branch after it is on whether the tag is right,
our leak (`Called.zero`); and `wipe`'s loop runs on `dst` and `len`. As for
`vg_aes_gcm_seal_gather` (`Gather/CT.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.PPC64LE.OpenTo

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq rel_taint rel_ite ct_of)

/-- The call's public data, from the arguments: whether it succeeds. -/
theorem Entered.leak {s c : State} (h : Lay s) (hc : Entered s c) :
    (rounds ((xS s c).gpr .r4) → (openRes (xS s c)).isSome = (res s).isSome) := fun _ => by
  rw [hc.xres h]

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

theorem resSome {σ₁ σ₂ : State} (p₁ : ToPre σ₁) (p₂ : ToPre σ₂) (ql : toLeak σ₁ = toLeak σ₂) :
    (res σ₁).isSome = (res σ₂).isSome := by
  simp only [toLeak, p₁.hR, p₂.hR, not_true_eq_false, ↓reduceIte, List.cons.injEq, and_true] at ql
  revert ql
  cases res σ₁ <;> cases res σ₂ <;> simp

theorem openTo_ct (hv : SplitOk) (hct : ConstantTime isa splitPPC64LE.pre splitPPC64LE.pub openSplit) :
    ConstantTime isa ToPre toPub openTo := by
  refine ct_of fun s₁ s₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨qsp, ql, q3, q4, q5, q6, q7, q8, q9, q10, qa⟩ := hq
  have hP : Pf s₁ = Pf s₂ := by simp only [Pf, qsp]
  unfold openTo
  refine (RelCT.alloc (P := Eq2 s₁ s₂) (R := TT) (fun a b ⟨ha, hb⟩ => by subst a b; exact qsp)
    ((?_ : RelCT isa (Eq2 (allocated 2720 s₁) (allocated 2720 s₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst s t; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
      (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (show s₁.sp - BitVec.ofNat 64 2720 = s₂.sp - BitVec.ofNat 64 2720 by rw [qsp])
    (by simp) (by taint_decide)) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC s₂ = rdC s₁ := by
    simp only [rdC, kR, nR, aR, sR, tR, C, Nn, NL, Ad, AL, Src, L, Tg, TL, fa, Pf, q3, q5, q6, q7, q8, q9, q10,
      qa 2 (by decide), qa 3 (by decide), qsp]
  have hwr : wrC s₂ = wrC s₁ := by simp only [wrC, dR, scR, Dst, L, fa, Pf, qa 0 (by decide), q10, qsp]
  have hx₂ : xS s₂ e₂ = e₂.callEntry.withRegions (rdC s₁) (wrC s₁) := by rw [← hrd, ← hwr]
  obtain ⟨cp₁, cv₁, cw₁⟩ := he₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := he₂.call h₂
  have lk₁ := he₁.leak h₁
  have lk₂ := he₂.leak h₂
  rw [hx₂] at cp₂ lk₂
  rw [hrd, hwr] at cv₂
  rw [hwr] at cw₂
  have g₁ := fun r hr => he₁.callGpr (rdC s₁) (wrC s₁) (r := r) hr
  have g₂ := fun r hr => he₂.callGpr (rdC s₁) (wrC s₁) (r := r) hr
  obtain ⟨a0₁, a1₁, a2₁, a3₁⟩ := he₁.args (rdC s₁) (wrC s₁)
  obtain ⟨a0₂, a1₂, a2₂, a3₂⟩ := he₂.args (rdC s₁) (wrC s₁)
  refine rel_seq (RelCT.call hv hct (rdC s₁) (wrC s₁) fun x y ⟨hx, hy⟩ => by
      subst hx hy
      refine ⟨cp₁, cp₂, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, fun hr => ?_⟩, cv₁, cw₁, cv₂, cw₂⟩
      · rw [g₁ .r3 (by decide), g₂ .r3 (by decide), q3]
      · rw [g₁ .r4 (by decide), g₂ .r4 (by decide), q4]
      · rw [g₁ .r5 (by decide), g₂ .r5 (by decide), q5]
      · rw [g₁ .r6 (by decide), g₂ .r6 (by decide), q6]
      · rw [g₁ .r7 (by decide), g₂ .r7 (by decide), q7]
      · rw [g₁ .r8 (by decide), g₂ .r8 (by decide), q8]
      · rw [g₁ .r9 (by decide), g₂ .r9 (by decide), q9]
      · rw [g₁ .r10 (by decide), g₂ .r10 (by decide), q10]
      · simp only [State.withRegions_sp, State.callEntry_sp, he₁.sp, he₂.sp, hP]
      · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
        · rw [a0₁, a0₂, Tg, Tg, qa 2 (by decide)]
        · rw [a1₁, a1₂, qa 3 (by decide)]
        · rw [a2₁, a2₂, fa, fa, hP]
        · rw [a3₁, a3₂, Dst, Dst, qa 0 (by decide)]
      · have hr₂ := hr
        rw [g₁ .r4 (by decide), q4, ← g₂ .r4 (by decide)] at hr₂
        rw [lk₁ hr, lk₂ hr₂, resSome p₁ p₂ ql])
    (called_wp hv h₁ he₁) (called_wp hv h₂ he₂) fun z₁ z₂ hz₁ hz₂ => ?_
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
