module

public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenToS.Fn
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenToS.Fn
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenTo.CT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86_64.OpenTo
meta import VerifiedGarbage.Impl.AesGcm.X86_64.OpenToS
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Run
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# AES-GCM decryption out of place, in one pass, x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments,
stack pointer and leak agree (`toPubS`) leak the same trace, as
`open_to`'s (`OpenTo/CT.lean`): the frame is pushed and popped at `rsp`
(`OpenTo.rel_frame`); the call's arguments and `wipe`'s are read at `rsp`;
the call is constant time by its callee's contract, whose public data (its
arguments and whether it succeeds, `Ready.leak`) agree (`call_rel`); and
both runs take the same branches after it (`after_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenToS

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.AesGcm.X86_64.OpenTo (frameRegs wipeArgs wipeBody wipe after)
open VG.Impl.AesGcm.X86_64.OpenToS (callArgs openToS)
open VG.Proof.AesGcm.X86_64.OpenTo (K Nn Ad Src L Dst Tg res kR nR aR sR dR tR toLeak rel_frame test_taint
  wipeArgs_taint zeroLoop_taint)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT rel_seq rel_regs rel_skip rel_ite ct_of)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg)

theorem callArgs_taint : ∃ h, (taint.check (Taint.ofRegs [.rsp]) callArgs h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- Whether the call failed, from what it left. -/
theorem Called.zero {s z : State} (hz : Called s z) : ((z.gpr .rax).setWidth 32 == 0) = (res s).isNone := by
  have ho := hz.out
  revert ho
  generalize res s = o
  cases o with
  | some pt => intro ho; rw [ho.1]; rfl
  | none => intro ho; rw [ho]; rfl

theorem hPe {σ₁ σ₂ : State} (hq : toPubS σ₁ σ₂) : P σ₁ = P σ₂ := by
  obtain ⟨⟨-, -, -, -, -, -, qsp, -⟩, -⟩ := hq
  simp only [P, Bs, qsp]

section
variable {M : CtxMode} {σ₁ σ₂ : State} (h₁ : Lay M σ₁) (h₂ : Lay M σ₂) (hq : toPubS σ₁ σ₂)
include h₁ h₂ hq

theorem resSome : (res σ₁).isSome = (res σ₂).isSome := by
  obtain ⟨-, ql⟩ := hq
  have r₁ := h₁.pre.rounds
  have r₂ := h₂.pre.rounds
  simp only [toLeak, r₁, r₂, not_true_eq_false, ↓reduceIte, List.cons.injEq, and_true] at ql
  revert ql
  cases (res σ₁).isSome <;> cases (res σ₂).isSome <;> simp

/-- The call, in two runs ready for it with the same public arguments. -/
theorem call_rel (F : OpenSplitFn M) {c₁ c₂ : State} (hc₁ : Ready σ₁ c₁) (hc₂ : Ready σ₂ c₂) :
    RelCT isa (Eq2 c₁ c₂) (.call F.fn.name F.fn.code) TT := by
  have hP := hPe hq
  obtain ⟨⟨qdi, qsi, qdx, qcx, q8, q9, qsp, qa⟩, ql⟩ := hq
  have a0 := qa 0 (by decide)
  have a1 := qa 1 (by decide)
  have a2 := qa 2 (by decide)
  have a4 := qa 4 (by decide)
  have a5 := qa 5 (by decide)
  have a6 := qa 6 (by decide)
  have hrd : rdC M σ₂ = rdC M σ₁ := by
    simp only [rdC, kR, nR, aR, tR, sR, K, Nn, OpenTo.NL, Ad, OpenTo.AL, Tg, OpenTo.TL, OpenTo.Src, L, qdi, qdx, qcx, q8, q9,
      a0, a1, a4, a5, hP]
  have hwr : wrC σ₂ = wrC σ₁ := by simp only [wrC, dR, wR, Wk, Dst, L, a1, a2, a6]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.callPre h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.callPre h₂
  have hx₂ : xS M σ₂ c₂ = c₂.callEntry.withRegions (rdC M σ₁) (wrC σ₁) := by rw [← hrd, ← hwr]
  have xa₁ := hc₁.xa h₁
  have xa₂ := hc₂.xa h₂
  have lk₁ := hc₁.leak h₁
  have lk₂ := hc₂.leak h₂
  rw [hx₂] at cp₂ xa₂ lk₂
  rw [hrd, hwr] at cv₂
  rw [hwr] at cw₂
  have g₁ (r : Reg) (hr : r ≠ .rsp) (ha : r ≠ .rax) : (xS M σ₁ c₁).gpr r = σ₁.gpr r :=
    (xgpr_eq hr).trans (hc₁.infr.gpr r ha hr)
  have g₂ (r : Reg) (hr : r ≠ .rsp) (ha : r ≠ .rax) :
      (c₂.callEntry.withRegions (rdC M σ₁) (wrC σ₁)).gpr r = σ₂.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ hr]; exact hc₂.infr.gpr r ha hr
  refine (RelCT.call F.ok F.ct (rdC M σ₁) (wrC σ₁) fun x y ⟨e₁, e₂⟩ => ?_).mono (fun a b h => h) fun _ _ h => h
  subst e₁ e₂
  refine ⟨cp₁, cp₂, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, by rw [lk₁, lk₂, ql]⟩, cv₁, cw₁, cv₂, cw₂,
    by rw [hc₁.infr.rsp, hc₂.infr.rsp, hP]⟩
  · rw [g₁ _ (by decide) (by decide), g₂ _ (by decide) (by decide), qdi]
  · rw [g₁ _ (by decide) (by decide), g₂ _ (by decide) (by decide), qsi]
  · rw [g₁ _ (by decide) (by decide), g₂ _ (by decide) (by decide), qdx]
  · rw [g₁ _ (by decide) (by decide), g₂ _ (by decide) (by decide), qcx]
  · rw [g₁ _ (by decide) (by decide), g₂ _ (by decide) (by decide), q8]
  · rw [g₁ _ (by decide) (by decide), g₂ _ (by decide) (by decide), q9]
  · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, hc₁.infr.rsp,
      hc₂.infr.rsp, hP]
  · obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, b₆⟩ := xa₁
    obtain ⟨c₀, c₁', c₂', c₃, c₄, c₅, c₆⟩ := xa₂
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [b₀, c₀, Dst, Dst, a2]
    · rw [b₁, c₁', a1]
    · rw [b₂, c₂', Tg, Tg, a4]
    · rw [b₃, c₃, a5]
    · rw [b₄, c₄, OpenTo.Src, OpenTo.Src, a0]
    · rw [b₅, c₅, a1]
    · rw [b₆, c₆, Wk, Wk, a6]

/-- After the call, in two runs that it left as they should. -/
theorem after_rel {z₁ z₂ : State} (hz₁ : Called σ₁ z₁) (hz₂ : Called σ₂ z₂) :
    RelCT isa (Eq2 z₁ z₂) after TT := by
  have hP := hPe hq
  have hres := resSome h₁ h₂ hq
  obtain ⟨⟨-, -, -, -, -, -, -, qa⟩, -⟩ := hq
  have a1 := qa 1 (by decide)
  have a2 := qa 2 (by decide)
  have tw (z : State) : ∃ t, runBlock isa [.alu32 .test .rax (.reg .rax)] z = some t ∧
      t.zf = some ((z.gpr .rax).setWidth 32 == 0) ∧ t.gpr = z.gpr ∧ t.mem = z.mem ∧ t.rd = z.rd ∧ t.wr = z.wr ∧
      t.mxcsr = z.mxcsr :=
    ⟨arithFlags z ((z.gpr .rax).setWidth 32 &&& (z.gpr .rax).setWidth 32) false false, by xrun [],
      by simp [zf_arithFlags, BitVec.and_self], rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨t₁, run₁, zf₁, g₁, m₁, rd₁, wr₁, mx₁⟩ := tw z₁
  obtain ⟨t₂, run₂, zf₂, g₂, m₂, rd₂, wr₂, mx₂⟩ := tw z₂
  have hc (s z t : State) (hz : Called s z) (g : t.gpr = z.gpr) (m : t.mem = z.mem) (rd : t.rd = z.rd)
      (wr : t.wr = z.wr) (mx : t.mxcsr = z.mxcsr) : Called s t :=
    ⟨by rw [g, m]; exact hz.out, m ▸ hz.frame, fun r hr hsp => by rw [g]; exact hz.cs r hr hsp,
      by rw [g]; exact hz.rsp, rd.trans hz.rd, wr.trans hz.wr, by rw [mx]; exact hz.mx⟩
  have ht₁ := hc _ _ _ hz₁ g₁ m₁ rd₁ wr₁ mx₁
  have ht₂ := hc _ _ _ hz₂ g₂ m₂ rd₂ wr₂ mx₂
  refine rel_seq (rel_regs [] (by simp) test_taint) (WP.of_runBlock (Q := fun u => u = t₁) ⟨t₁, run₁, rfl⟩)
    (WP.of_runBlock (Q := fun u => u = t₂) ⟨t₂, run₂, rfl⟩) fun u₁ u₂ e₁ e₂ => ?_
  subst e₁ e₂
  have ev₁ : isa.eval .e u₁ = some (res σ₁).isNone := by simp only [eval, zf₁, hz₁.zero]
  have hn : (res σ₂).isNone = (res σ₁).isNone := by
    revert hres
    generalize res σ₁ = o₁
    generalize res σ₂ = o₂
    cases o₁ <;> cases o₂ <;> simp
  have ev₂ : isa.eval .e u₂ = some (res σ₁).isNone := by simp only [eval, zf₂, hz₂.zero, hn]
  refine rel_ite ev₁ ev₂ (fun _ => ?_) fun _ => rel_skip
  -- `wipe`, from the same public arguments.
  refine rel_seq (rel_regs [.rsp] (by simp [ht₁.rsp, ht₂.rsp, hP]) wipeArgs_taint) (wipeArgs_wp h₁ ht₁)
    (wipeArgs_wp h₂ ht₂) fun w₁ w₂ hw₁ hw₂ => ?_
  have hL : L σ₁ = L σ₂ := by simp only [L, a1]
  refine rel_ite (b := decide (0 = L σ₁)) (by simp only [eval, hw₁.zf]) (by simp only [eval, hw₂.zf, hL])
    (fun _ => rel_skip) fun _ => rel_regs [.rdi, .rcx, .r10] ?_ zeroLoop_taint
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by rw [hw₁.rdi, hw₂.rdi, Dst, Dst, a2], by rw [hw₁.rcx, hw₂.rcx, hL], by rw [hw₁.r10, hw₂.r10]⟩

end

theorem openToS_rel {M : CtxMode} (F : OpenSplitFn M) {σ₁ σ₂ : State} (p₁ : ToPreS M σ₁)
    (p₂ : ToPreS M σ₂) (hq : toPubS σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (openToS F.fn) TT := by
  have h₁ := lay p₁
  have h₂ := lay p₂
  have hP := hPe hq
  refine rel_frame hq.1.2.2.2.2.2.2.1 ?_
  -- The call's arguments.
  refine rel_seq (rel_regs [.rsp] (by simp only [List.mem_singleton, forall_eq, OpenToS.hP, hP]) callArgs_taint)
    (ready_wp h₁ (pushed_inFrame h₁)) (ready_wp h₂ (pushed_inFrame h₂)) fun r₁ r₂ hr₁ hr₂ => ?_
  -- The call, by its callee's contract, then what follows it.
  exact rel_seq (call_rel h₁ h₂ hq F hr₁ hr₂) (called_wp F h₁ hr₁) (called_wp F h₂ hr₂)
    fun z₁ z₂ hz₁ hz₂ => after_rel h₁ h₂ hq hz₁ hz₂

theorem openToS_ct {M : CtxMode} (F : OpenSplitFn M) :
    ConstantTime isa (toSK M).pre (toSK M).pub (openToS F.fn) :=
  ct_of fun _ _ p₁ p₂ hq => openToS_rel F p₁ p₂ hq

end VG.Proof.AesGcm.X86_64.OpenToS
