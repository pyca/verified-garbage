module

public import VerifiedGarbage.Proof.AesGcm.Arm.OpenTo.Fn

import VerifiedGarbage.Proof.AesGcm.Arm.Gather.LoopCT
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesGcm.Arm.OpenTo.Fn
meta import VerifiedGarbage.Proof.AesGcm.Arm.Gather.LoopCT
meta import VerifiedGarbage.Proof.AesGcm.Arm.Run
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# AES-GCM decryption out of place, by a copy, ARMv7: constant time

Untrusted: everything here is checked by Lean. Two runs whose stack pointer,
arguments and leak agree (`toPub`) leak the same trace, related piece by
piece from given states (`Gather.Eq2`): the frame's words are read and
written through `r12` at the stack pointer, the same in both runs
(`Gather.rel_fp`); the copy is constant time by `Gather.copySlice_rel`, from
the same descriptor; the call is constant time by its callee's contract,
whose public data (its arguments and whether it succeeds, `Ready.leak`)
agree; the branch after it is on whether the tag is right, our leak
(`Called.zero`); and `wipe`'s loop runs on `dst` and `len` (the taint
analysis from those registers).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm.OpenTo

open VG VG.Arm VG.Impl.AesGcm.Arm VG.Impl.AesGcm.Arm.OpenTo
open VG.Impl.AesGcm.Arm.SealGather (setFp copySlice)
open VG.Proof.AesGcm.Arm (eval_eq')
open VG.Proof.AesGcm.Arm.Gather (Eq2 TT rel_seq rel_taint rel_skip rel_ite rel_alloc ct_of rel_fp copySlice_rel)

/-- The call's public data, from the arguments. -/
theorem Ready.leak {s c : State} (h : Lay s) (hc : Ready s c) : callLeak (xS s c) = toLeak s := by
  obtain ⟨-, c1, -⟩ := hc.callGpr (rdC s) (wrC s)
  simp only [callLeak, toLeak, hc.xres h, c1]

/-- Whether the call failed, from what it left. -/
theorem Called.zero {s z : State} (hz : Called s z) : (z.gpr .r0 == 0) = (res s).isNone := by
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

theorem openTo_ct (F : OpenFn) : ConstantTime isa ToPre toPub (openTo F.name F.code) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨qsp, ql, q0, q1, q2, q3, qa⟩ := hq
  have a (i : Nat) (hi : i < 8) := qa i hi
  have hP : Pf σ₁ = Pf σ₂ := by simp only [Pf, qsp]
  refine rel_alloc ?_
  -- The entry.
  refine rel_seq (rel_fp (l := entryWords) (show Pf σ₁ = Pf σ₂ from hP) ⟨_, by taint_decide⟩)
    (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The copy, from the same descriptor.
  have sp₁ := slicePre_of h₁ he₁
  have sp₂ := slicePre_of h₂ he₂
  rw [← hP] at sp₂
  simp only [Src, Dst, L, ← a 2 (by decide), ← a 3 (by decide), ← a 4 (by decide)] at sp₂
  refine rel_seq (copySlice_rel sp₁ sp₂) (copied_wp h₁ he₁) (copied_wp h₂ he₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_fp (l := argWords) (by rw [hc₁.sp, hc₂.sp, hP]) ⟨_, by taint_decide⟩)
    (ready_wp h₁ hc₁) (ready_wp h₂ hc₂) fun r₁ r₂ hr₁ hr₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by
    simp only [rdC, kR, nR, aR, tR, K, Nn, NL, Ad, AL, Tg, TL, Bs, ← q0, ← q2, ← q3, ← a 0 (by decide),
      ← a 1 (by decide), ← a 6 (by decide), ← a 7 (by decide), qsp]
  have hwr : wrC σ₂ = wrC σ₁ := by
    simp only [wrC, dR, Dst, L, ← a 3 (by decide), ← a 4 (by decide)]
  have hx₂ : xS σ₂ r₂ = r₂.callEntry.withRegions (rdC σ₁) (wrC σ₁) := by rw [← hrd, ← hwr]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hr₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hr₂.call h₂
  have lk₁ := hr₁.leak h₁
  have lk₂ := hr₂.leak h₂
  rw [hx₂] at cp₂ lk₂
  rw [hrd, hwr] at cv₂
  rw [hwr] at cw₂
  obtain ⟨g0₁, g1₁, g2₁, g3₁⟩ := hr₁.callGpr (rdC σ₁) (wrC σ₁)
  obtain ⟨g0₂, g1₂, g2₂, g3₂⟩ := hr₂.callGpr (rdC σ₁) (wrC σ₁)
  obtain ⟨s0₁, s1₁, s2₁, s3₁, s4₁, s5₁⟩ := hr₁.args h₁ (rdC σ₁) (wrC σ₁)
  obtain ⟨s0₂, s1₂, s2₂, s3₂, s4₂, s5₂⟩ := hr₂.args h₂ (rdC σ₁) (wrC σ₁)
  refine rel_seq (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun x y ⟨hx, hy⟩ => by
      subst hx hy
      refine ⟨openSpec_pre cp₁, openSpec_pre cp₂,
        openSpec_pub ⟨?_, by rw [lk₁, lk₂, ql], ?_, ?_, ?_, ?_, fun i hi => ?_⟩, cv₁, cw₁, cv₂, cw₂⟩
      · simp only [State.withRegions_sp, State.callEntry_sp, hr₁.sp, hr₂.sp, hP]
      · rw [g0₁, g0₂, q0]
      · rw [g1₁, g1₂, q1]
      · rw [g2₁, g2₂, q2]
      · rw [g3₁, g3₂, q3]
      · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl
        · rw [s0₁, s0₂]; exact a 0 (by decide)
        · rw [s1₁, s1₂]; exact a 1 (by decide)
        · rw [s2₁, s2₂]; exact a 4 (by decide)
        · rw [s3₁, s3₂]; exact a 3 (by decide)
        · rw [s4₁, s4₂]; exact a 6 (by decide)
        · rw [s5₁, s5₂]; exact a 7 (by decide))
    (called_wp F h₁ hr₁) (called_wp F h₂ hr₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- After the call: the same branch in both runs.
  have hn := resNone p₁ p₂ ql
  refine rel_seq ?_ (after_wp h₁ hz₁) (after_wp h₂ hz₂) fun u₁ u₂ hu₁ hu₂ => ?_
  · unfold after
    refine rel_seq (rel_taint [] (by simp) ⟨_, by taint_decide⟩) (cmp_ok z₁) (cmp_ok z₂)
      fun t₁ t₂ ⟨tm₁, tg₁, tsp₁, tz₁, trd₁, twr₁⟩ ⟨tm₂, tg₂, tsp₂, tz₂, trd₂, twr₂⟩ => ?_
    have ht₁ := hz₁.congr tm₁ tg₁ tsp₁ trd₁ twr₁
    have ht₂ := hz₂.congr tm₂ tg₂ tsp₂ trd₂ twr₂
    have ev₁ : t₁.z = (res σ₁).isNone := by rw [tz₁, hz₁.zero]
    have ev₂ : t₂.z = (res σ₁).isNone := by rw [tz₂, hz₂.zero, hn]
    refine rel_ite (eval_eq' ev₁) (eval_eq' ev₂) (fun _ => ?_) fun _ => rel_skip
    -- `wipe`, from the same public arguments.
    unfold wipe
    refine rel_seq (rel_fp (l := wipeArgs) (by rw [ht₁.sp, ht₂.sp, hP]) ⟨_, by taint_decide⟩)
      (wipeArgs_wp h₁ ht₁) (wipeArgs_wp h₂ ht₂) fun w₁ w₂ hw₁ hw₂ => ?_
    exact rel_taint [.r1, .r2]
      (by simp [hw₁.r1, hw₂.r1, hw₁.r2, hw₂.r2, Dst, L, a 3 (by decide), a 4 (by decide)])
      ⟨_, by taint_decide⟩
  -- Our return address.
  exact rel_fp (l := [Instr.ldr .lr .r12 24]) (by rw [hu₁.sp, hu₂.sp, hP]) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.Arm.OpenTo
