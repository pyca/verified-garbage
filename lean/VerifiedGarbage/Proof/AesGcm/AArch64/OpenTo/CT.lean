module

public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenTo.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OpenTo.Fn
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Env
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM decryption out of place, by a copy, AArch64: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments,
stack pointer and leak agree (`toPub`) leak the same trace: the entry, the
loads of the call's arguments, of `wipe`'s and of the return address are at
the stack pointer; the copy runs on `src`, `dst` and `len`, and `wipe`'s
loop on `dst` and `len` (the taint analysis from those registers); the call
is constant time by its callee's contract, whose public data (its arguments
and whether it succeeds, `Ready.leak`) agree; and the branch after it is on
whether the tag is right, our leak (`Called.zero`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.OpenTo

open VG VG.AArch64 VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.OpenTo
open VG.Impl.AesGcm.AArch64.SealGather (copySlice)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint rel_ite ct_of)

/-- The call's public data, from the arguments. -/
theorem Ready.leak {s c : State} (h : Lay s) (hc : Ready s c) : callLeak (xS s c) = toLeak s := by
  obtain ⟨-, c1, -, -, -, -, -, -⟩ := hc.callGpr
  simp only [callLeak, toLeak, hc.xres h, State.withRegions_gpr, c1]

/-- Whether the call failed, from what it left. -/
theorem Called.zero {s z : State} (hz : Called s z) : ((z.gpr .x0).setWidth 32 == 0) = (res s).isNone := by
  have ho := hz.out
  revert ho
  cases res s with
  | some pt => intro ho; rw [ho.1]; rfl
  | none => intro ho; rw [ho]; rfl

theorem resSome {σ₁ σ₂ : State} (p₁ : ToPre σ₁) (p₂ : ToPre σ₂) (ql : toLeak σ₁ = toLeak σ₂) :
    (res σ₁).isNone = (res σ₂).isNone := by
  simp only [toLeak, p₁.hR, p₂.hR, not_true_eq_false, ↓reduceIte, List.cons.injEq, and_true] at ql
  revert ql
  cases res σ₁ <;> cases res σ₂ <;> simp

theorem openTo_rel (F : OpenFn) {σ₁ σ₂ : State} (p₁ : ToPre σ₁) (p₂ : ToPre σ₂) (hq : toPub σ₁ σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (openTo F.fn) TT := by
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨qsp, ql, q0, q1, q2, q3, q4, q5, q6, q7, a0, a1, a2, a3⟩ := hq
  have hB : Bs σ₁ = Bs σ₂ := by simp only [Bs, qsp]
  have hP : P σ₁ = P σ₂ := by simp only [P, hB]
  refine (RelCT.alloc (P := Eq2 σ₁ σ₂) (R := TT)
    ((?_ : RelCT isa (Eq2 (allocated 32 σ₁) (allocated 32 σ₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (by rw [allocated_sp h₁, allocated_sp h₂, hP]) (by agree_tac [])
    ⟨_, by taint_decide⟩) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The copy.
  refine rel_seq (rel_taint [.x11, .x12, .x13] (by rw [he₁.sp, he₂.sp, hP])
    (by agree_tac [he₁.x11, he₂.x11, he₁.x12, he₂.x12, he₁.x13, he₂.x13, Dst, Src, a0, q6, q7])
    ⟨_, by taint_decide⟩) (copied_wp h₁ he₁) (copied_wp h₂ he₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call's argument.
  refine rel_seq (rel_taint [] (by rw [hc₁.sp, hc₂.sp, hP]) (by agree_tac []) ⟨_, by taint_decide⟩)
    (ready_wp h₁ hc₁) (ready_wp h₂ hc₂) fun r₁ r₂ hr₁ hr₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by
    simp only [rdC, kR, nR, aR, tR, K, Nn, NL, Ad, AL, Tg, TL, q0, q2, q3, q4, q5, a2, a3, hP]
  have hwr : wrC σ₂ = wrC σ₁ := by simp only [wrC, dR, Dst, L, a0, q7]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hr₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hr₂.call h₂
  have lk₁ := hr₁.leak h₁
  have lk₂ := hr₂.leak h₂
  have hx₂ : xS σ₂ r₂ = r₂.callEntry.withRegions (rdC σ₁) (wrC σ₁) := by rw [← hrd, ← hwr]
  rw [hx₂] at cp₂ lk₂
  rw [hrd, hwr] at cv₂
  rw [hwr] at cw₂
  obtain ⟨r0₁, r1₁, r2₁, r3₁, r4₁, r5₁, r6₁, r7₁⟩ := hr₁.callGpr
  obtain ⟨r0₂, r1₂, r2₂, r3₂, r4₂, r5₂, r6₂, r7₂⟩ := hr₂.callGpr
  obtain ⟨t0₁, t1₁⟩ := hr₁.stackArgs h₁ (rdC σ₁) (wrC σ₁)
  obtain ⟨t0₂, t1₂⟩ := hr₂.stackArgs h₂ (rdC σ₁) (wrC σ₁)
  refine rel_seq (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun a b ⟨ha, hb⟩ => by
      subst ha hb
      refine ⟨openSpec_pre cp₁, openSpec_pre cp₂, openSpec_pub ⟨?_, by rw [lk₁, lk₂, ql], ?_⟩, cv₁, cw₁, cv₂, cw₂⟩
      · simp only [State.withRegions_sp, State.callEntry_sp, hr₁.sp, hr₂.sp, hP]
      · simp only [State.withRegions_gpr, r0₁, r1₁, r2₁, r3₁, r4₁, r5₁, r6₁, r7₁, r0₂, r1₂, r2₂, r3₂, r4₂, r5₂,
          r6₂, r7₂, t0₁, t0₂, t1₁, t1₂, q0, q1, q2, q3, q4, q5, q7, Dst, Tg, a0, a2, a3, and_self])
    (called_wp F h₁ hr₁) (called_wp F h₂ hr₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- After the call: the same branch in both runs.
  have hn := resSome p₁ p₂ ql
  have ev₁ : isa.eval (.zero .w .x0) z₁ = some (res σ₁).isNone := by
    show some (_ == _) = _; rw [← hz₁.zero]; rfl
  have ev₂ : isa.eval (.zero .w .x0) z₂ = some (res σ₁).isNone := by
    show some (_ == _) = _; rw [hn, ← hz₂.zero]; rfl
  refine rel_seq (rel_ite ev₁ ev₂ (fun _ => ?_) fun _ => ?_) (after_ok h₁ hz₁) (after_ok h₂ hz₂)
    fun u₁ u₂ hu₁ hu₂ => ?_
  · -- `wipe`, from the same public arguments.
    refine rel_seq (rel_taint [] (by rw [hz₁.sp, hz₂.sp, hP]) (by agree_tac []) ⟨_, by taint_decide⟩)
      (wipeArgs_wp h₁ hz₁) (wipeArgs_wp h₂ hz₂) fun w₁ w₂ hw₁ hw₂ => ?_
    exact rel_taint [.x9, .x10] (by rw [hw₁.sp, hw₂.sp, hz₁.sp, hz₂.sp, hP])
      (by agree_tac [hw₁.x9, hw₂.x9, hw₁.x10, hw₂.x10, Dst, L, a0, q7]) ⟨_, by taint_decide⟩
  · exact rel_taint [] (by rw [hz₁.sp, hz₂.sp, hP]) (by agree_tac []) ⟨_, by taint_decide⟩
  -- The return address.
  exact rel_taint [] (by rw [hu₁.sp, hu₂.sp, hP]) (by agree_tac []) ⟨_, by taint_decide⟩

theorem openTo_ct (F : OpenFn) : ConstantTime isa toK.pre toK.pub (openTo F.fn) :=
  ct_of fun _ _ p₁ p₂ hq => openTo_rel F p₁ p₂ hq

end VG.Proof.AesGcm.AArch64.OpenTo
