module

public import VerifiedGarbage.Proof.AesGcm.X86.OpenTo.Fn

import VerifiedGarbage.Proof.AesGcm.X86.Gather.LoopCT
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesGcm.X86.OpenTo.Fn
meta import VerifiedGarbage.Proof.AesGcm.X86.Gather.LoopCT
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# AES-GCM decryption out of place, by a copy, x86: constant time

Untrusted: everything here is checked by Lean. Two runs whose stack pointer,
arguments and leak agree (`toPub`) leak the same trace, related piece by
piece from given states (`Gather.Eq2`): the frame's words, our arguments and
`wipe`'s are read and written at `esp`, the same in both runs (the taint
analysis from `esp`); the copy is constant time by `Gather.copySlice_rel`,
from the same descriptor; the call is constant time by its callee's
contract, whose public data (its arguments and whether it succeeds,
`Copied.leak`) agree; the branch after it is on whether the tag is right,
our leak (`Called.zero`); and `wipe`'s loop runs on `dst` and `len` (the
taint analysis from those registers).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86.OpenTo

open VG VG.X86 VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.OpenTo
open VG.Impl.AesGcm.X86.SealGather (copySlice)
open VG.Proof.AesGcm.X86.Gather (Eq2 TT rel_seq rel_taint rel_skip rel_ite rel_alloc ct_of copySlice_rel)

/-- The call's public data, from the arguments. -/
theorem Copied.leak {s c : State} (h : Lay s) (hc : Copied s c) : callLeak (xS s c) = toLeak s := by
  obtain ⟨-, a1, -⟩ := hc.args h
  simp only [callLeak, toLeak, hc.xres h, a1]

/-- Whether the call failed, from what it left. -/
theorem Called.zero {s z : State} (hz : Called s z) : (z.gpr .eax == 0) = (res s).isNone := by
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
  obtain ⟨qsp, ql, qa⟩ := hq
  have a (i : Nat) (hi : i < 12) := qa i hi
  have hP : Pf σ₁ = Pf σ₂ := by simp only [Pf, qsp]
  refine rel_alloc ?_
  -- The entry.
  refine rel_seq (rel_taint [.esp] (by simp [hP]) ⟨_, by taint_decide⟩)
    (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The copy, from the same descriptor.
  have sp₁ := slicePre_of h₁ he₁
  have sp₂ := slicePre_of h₂ he₂
  rw [← hP] at sp₂
  simp only [Src, Dst, L, ← a 6 (by decide), ← a 7 (by decide), ← a 8 (by decide)] at sp₂
  refine rel_seq (copySlice_rel sp₁ sp₂) (copied_wp h₁ he₁) (copied_wp h₂ he₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by
    simp only [rdC, kR, nR, aR, tR, K, Nn, NL, Ad, AL, Tg, TL, ← a 0 (by decide), ← a 2 (by decide),
      ← a 3 (by decide), ← a 4 (by decide), ← a 5 (by decide), ← a 10 (by decide), ← a 11 (by decide)]
  have hwr : wrC σ₂ = wrC σ₁ := by
    simp only [wrC, dR, Dst, L, Bs, ← a 7 (by decide), ← a 8 (by decide), qsp]
  have hx₂ : xS σ₂ c₂ = c₂.callEntry.withRegions (rdC σ₁) (wrC σ₁) := by rw [← hrd, ← hwr]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  have lk₁ := hc₁.leak h₁
  have lk₂ := hc₂.leak h₂
  obtain ⟨s0₁, s1₁, s2₁, s3₁, s4₁, s5₁, s6₁, s7₁, s8₁, s9₁⟩ := hc₁.args h₁
  obtain ⟨s0₂, s1₂, s2₂, s3₂, s4₂, s5₂, s6₂, s7₂, s8₂, s9₂⟩ := hc₂.args h₂
  rw [hx₂] at cp₂ lk₂ s0₂ s1₂ s2₂ s3₂ s4₂ s5₂ s6₂ s7₂ s8₂ s9₂
  rw [hrd, hwr] at cv₂
  rw [hwr] at cw₂
  refine rel_seq (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun x y ⟨hx, hy⟩ => by
      subst hx hy
      refine ⟨openSpec_pre cp₁, openSpec_pre cp₂, openSpec_pub ⟨?_, by rw [lk₁, lk₂, ql], fun i hi => ?_⟩, cv₁, cw₁,
        cv₂, cw₂, by rw [hc₁.esp, hc₂.esp, hP]⟩
      · simp only [State.withRegions_gpr, State.callEntry_esp, hc₁.esp, hc₂.esp, hP]
      · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [s0₁, s0₂]; exact a 0 (by decide)
        · rw [s1₁, s1₂]; exact a 1 (by decide)
        · rw [s2₁, s2₂]; exact a 2 (by decide)
        · rw [s3₁, s3₂]; exact a 3 (by decide)
        · rw [s4₁, s4₂]; exact a 4 (by decide)
        · rw [s5₁, s5₂]; exact a 5 (by decide)
        · rw [s6₁, s6₂]; exact a 8 (by decide)
        · rw [s7₁, s7₂]; exact a 7 (by decide)
        · rw [s8₁, s8₂]; exact a 10 (by decide)
        · rw [s9₁, s9₂]; exact a 11 (by decide))
    (called_wp F h₁ hc₁) (called_wp F h₂ hc₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- After the call: the same branch in both runs.
  have hn := resNone p₁ p₂ ql
  refine rel_seq ?_ (after_wp h₁ hz₁) (after_wp h₂ hz₂) fun u₁ u₂ hu₁ hu₂ => ?_
  · unfold after
    refine rel_seq (rel_taint [] (by simp) ⟨_, by taint_decide⟩) (test_ok z₁) (test_ok z₂)
      fun t₁ t₂ ⟨tm₁, tg₁, tz₁, trd₁, twr₁⟩ ⟨tm₂, tg₂, tz₂, trd₂, twr₂⟩ => ?_
    have ht₁ := hz₁.congr tm₁ tg₁ trd₁ twr₁
    have ht₂ := hz₂.congr tm₂ tg₂ trd₂ twr₂
    have ev₁ : t₁.zf = some (res σ₁).isNone := by rw [tz₁, hz₁.zero]
    have ev₂ : t₂.zf = some (res σ₁).isNone := by rw [tz₂, hz₂.zero, hn]
    refine rel_ite ev₁ ev₂ (fun _ => ?_) fun _ => rel_skip
    -- `wipe`, from the same public arguments.
    unfold wipe
    refine rel_seq (rel_taint [.esp] (by simp [ht₁.esp, ht₂.esp, hP]) ⟨_, by taint_decide⟩)
      (wipeArgs_wp h₁ ht₁) (wipeArgs_wp h₂ ht₂) fun w₁ w₂ hw₁ hw₂ => ?_
    exact rel_taint [.edx, .ecx]
      (by simp [hw₁.edx, hw₂.edx, hw₁.ecx, hw₂.ecx, Dst, L, a 7 (by decide), a 8 (by decide)])
      ⟨_, by taint_decide⟩
  -- Our caller's registers back.
  exact rel_taint [.esp] (by simp [hu₁.esp, hu₂.esp, hP]) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.X86.OpenTo
