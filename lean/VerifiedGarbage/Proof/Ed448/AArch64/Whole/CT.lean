import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Calls
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT

/-!
# Ed448's complete operations on AArch64: constant time in the frame's body

Two runs whose public data agree have the same `Env`, so in the frame's body
they are related by `Two`: both satisfy `WCtx` with it (and a predicate `P`
of what the next piece needs), whatever their secrets. The facts about one
run (`M`: what the saved arguments are, from the run's initial memory) hold
in both. A block addresses only the stack (`block_ct`); a call's arguments
(`setupS_ct`) have the same values `val` in both runs, which `callS_ct`
passes to constant-time code whose public data they are (`Whole.callEx`).
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)

/-- Two runs, each in the frame's body with `V`, and `P`. -/
abbrev Two (V : Env) (g₁ g₂ : Reg → Addr) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) : Prop :=
  (WCtx V g₁ v₁ m₁ a ∧ P a) ∧ (WCtx V g₂ v₂ m₂ b ∧ P b)

/-- The argument registers hold `val`. -/
abbrev Regs (args : List (Reg × Src)) (val : Reg → Addr) (t : State) : Prop :=
  ∀ p ∈ args, t.gpr p.1 = val p.1

variable {V : Env} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem two_sp {P : State → Prop} {a b : State} (h : Two V g₁ g₂ v₁ v₂ m₁ m₂ P a b) : a.sp = b.sp :=
  h.1.1.1.sp.trans h.2.1.1.sp.symm

/-- A block addressed through the stack pointer, with its effect in each run. -/
theorem block_ct {M : Mem → Prop} (h₁ : M m₁) (h₂ : M m₂) {P Q : State → Prop} {is : List Instr}
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block is) hint).isSome = true)
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      WP isa (.block is) t fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (.block is) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) :=
  VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => two_sp h) ht)
    (fun _ h => hok h₁ h.1 h.2) (fun _ h => hok h₂ h.1 h.2)

/-- A call's arguments, the same values `val` in both runs. -/
theorem setupS_ct (hV : V.Ok) {M : Mem → Prop} (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (.block (setupS args))
      (Two V g₁ g₂ v₁ v₂ m₁ m₂ (Regs args val)) :=
  block_ct h₁ h₂ ht fun hm hc hp => WP.mono (wsetup_ok hV hc hn hv hret hr) fun _ ⟨hu, _, hs⟩ =>
    ⟨hu, fun p hq => (hs p hq).trans (hval hm hc hp p hq)⟩

/-- A call, its arguments the same values in both runs, and its effect in each run. -/
theorem callS_ct (hV : V.Ok) {M : Mem → Prop} (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) {rd wr : List Region}
    (pre : ∀ {g vec m₀ t}, WCtx V g vec m₀ t → Regs args val t →
      k.pre (t.callEntry.withRegions rd wr))
    (hcov : Covers (rd ++ wr) (V.ins ++ FR V.E :: V.outs)) (hw : ∀ r ∈ wr, Writable V r)
    (kp : ∀ a b : State, a.sp = b.sp → (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions rd wr) (b.callEntry.withRegions rd wr))
    {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      WP isa (callS args name c) t fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (callS args name c) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp ?_ (fun _ h => hok h₁ h.1 h.2) (fun _ h => hok h₂ h.1 h.2)
  refine (setupS_ct hV h₁ h₂ hn hv hret hr ht val hval).seq
    (VG.Proof.Ed25519.AArch64.Whole.callEx correct ct fun a b h => ?_)
  let ready : ∀ {g vec m₀ t}, WCtx V g vec m₀ t → Regs args val t →
      VG.Proof.Ed25519.AArch64.Whole.CallReady k V.E V.ins V.outs t := fun hc hs =>
    ⟨rd, wr, pre hc hs, hcov, fun r hr => (hw r hr).imp And.left id⟩
  obtain ⟨ca, wa⟩ := (ready h.1.1 h.1.2).covers_state h.1.1.1
  obtain ⟨cb, wb⟩ := (ready h.2.1 h.2.2).covers_state h.2.1.1
  refine ⟨rd, wr, rd, wr, pre h.1.1 h.1.2, pre h.2.1 h.2.2, kp a b (two_sp h) fun p hp => ?_, ca, wa, cb, wb⟩
  rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2 p hp, h.2.2 p hp]

end VG.Proof.Ed448.AArch64.Whole
