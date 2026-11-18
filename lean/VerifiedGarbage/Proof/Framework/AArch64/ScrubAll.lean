module

public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Returning without secret residue, whatever the code leaves (AArch64)

`ScrubAll.noResidue_scrubAll`: code verified against its contract, whose
frames stay within the `W` bytes below the stack pointer, that writes no
PSTATE.DIT and calls nothing indirectly, followed by `scrubAll W rb`, which
clears every register the calling convention does not preserve but the
result's `rb` bits of `x0`, the flags and the high halves of `v8`–`v15`, and
zeroes those `W` bytes, returns without secret residue. It needs no analysis
of the code: the registers it clears hold constants, those the calling
convention preserves are what they were on entry (`abiPreserved`), the memory
the code may change outside the buffers is within those `W` bytes
(`Exec.frameSp`), which the clearing zeroes, and the two runs end with the
same unknowns, since their traces are the same (`Exec.unknowns_agree`). So it
serves code generic over the implementations of the functions it calls,
whose code is not known, as x86-64's `X86_64.Scrub.withScrubAll` does.
-/

@[expose] public section

namespace VG.AArch64.ScrubAll

open VG.AArch64 VG.AArch64.Residue VG.Impl.Residue.AArch64

/-! ## The unknowns of two runs along the same trace -/

/-- `c` calls nothing indirectly. -/
def noIcall : Prog isa → Bool
  | .block _ => true
  | .seq a b => noIcall a && noIcall b
  | .ite _ t e => noIcall t && noIcall e
  | .loop b _ => noIcall b
  | .call _ b => noIcall b
  | .frame _ b _ => noIcall b
  | .icall .. => false

/-- The functions `c` may call indirectly. -/
def inames : Prog isa → List String
  | .block _ => []
  | .seq a b => inames a ++ inames b
  | .ite _ t e => inames t ++ inames e
  | .loop b _ => inames b
  | .call _ b => inames b
  | .frame _ b _ => inames b
  | .icall _ n b nx => n :: inames b ++ inames nx

theorem inames_of_noIcall : ∀ {c : Prog isa}, noIcall c = true → inames c = []
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [noIcall, Bool.and_eq_true] at h
    simp only [inames, inames_of_noIcall h.1, inames_of_noIcall h.2, List.append_nil]
  | .ite _ t e, h => by
    simp only [noIcall, Bool.and_eq_true] at h
    simp only [inames, inames_of_noIcall h.1, inames_of_noIcall h.2, List.append_nil]
  | .loop b _, h => by simp only [noIcall] at h; simp only [inames, inames_of_noIcall h]
  | .call _ b, h => by simp only [noIcall] at h; simp only [inames, inames_of_noIcall h]
  | .frame _ b _, h => by simp only [noIcall] at h; simp only [inames, inames_of_noIcall h]
  | .icall .., h => by simp only [noIcall, Bool.false_eq_true] at h

theorem execBlock_unknowns : ∀ {is : List Instr} {s₁ s₂ a b : State} {t₁ t₂ : List Leak},
    execBlock isa is s₁ = some (a, t₁) → execBlock isa is s₂ = some (b, t₂) →
      t₁.length = t₂.length ∧ a.unknowns = s₁.unknowns ∧ b.unknowns = s₂.unknowns
  | [], _, _, _, _, _, _, h₁, h₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂; exact ⟨rfl, rfl, rfl⟩
  | i :: is, s₁, s₂, a, b, t₁, t₂, h₁, h₂ => by
    simp only [execBlock] at h₁ h₂
    cases e₁ : exec i s₁ with
    | none => simp only [e₁] at h₁; cases h₁
    | some u₁ =>
      cases e₂ : exec i s₂ with
      | none => simp only [e₂] at h₂; cases h₂
      | some u₂ =>
        simp only [isa, e₁, e₂] at h₁ h₂
        obtain ⟨p₁, hp₁, hq₁⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨p₂, hp₂, hq₂⟩ := Option.map_eq_some_iff.mp h₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq₁
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq₂
        obtain ⟨hl, ha, hb⟩ := execBlock_unknowns (s₁ := u₁) (s₂ := u₂) (by rw [hp₁]) (by rw [hp₂])
        refine ⟨?_, ha.trans (RTaint.exec_ud e₁).1, hb.trans (RTaint.exec_ud e₂).1⟩
        simp only [List.length_append, List.length_map, hl, RTaintCT.addrs_length i s₁ s₂]

theorem push_unknowns {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) : s₁.unknowns = s.unknowns := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h <;> split at h <;> cases h <;> rfl

/-- The unknowns a frame's release uses. -/
def popK : Instr → Nat
  | .pop _ => 4
  | .free b => b / 4
  | _ => 0

theorem pop_unknowns {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s'.unknowns = fun n => s₂.unknowns (n + popK j) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h <;> split at h <;> cases h <;> rfl

theorem call_unknowns {s s₁ : State} (h : isa.call s = some s₁) :
    s₁.unknowns = fun n => s.unknowns (n + 4) := by
  simp only [isa, call, Option.some.injEq] at h; subst h; rfl

theorem ret_unknowns {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') : s'.unknowns = s₂.unknowns := by
  simp only [isa, ret] at h; split at h <;> cases h; rfl

theorem push_syms {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) : s₁.syms = s.syms := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h <;> split at h <;> cases h <;> rfl

theorem call_syms {s s₁ : State} (h : isa.call s = some s₁) : s₁.syms = s.syms := by
  simp only [isa, call, Option.some.injEq] at h; subst h; rfl

/-- The trace of an indirect call: the addresses its instruction reads, then
the address it calls. -/
theorem icall_trace {i : Instr} {n : String} {b nx : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa (.icall i n b nx) s t s') :
    ∃ a rest, isa.icall i s = some a ∧ t = (isa.addrs i s).map .addr ++ .addr a :: rest := by
  cases e with
  | icall h₁ _ _ _ => exact ⟨_, _, h₁, rfl⟩
  | icallNext _ _ e' => exact icall_trace e'

theorem branch_ne {r₁ r₂ : List Leak} : Leak.branch true :: r₁ ≠ Leak.branch false :: r₂ := by
  intro h; cases h

/-- Two runs of code from the same unknowns, whose functions called
indirectly have the same addresses (`inames`), one of whose traces is a
prefix of the other's continued, have the same trace and end with the same
unknowns: each call and each frame's release uses a number of unknowns its
instruction fixes, and the trace says which way each branch went and which
function each indirect call called. -/
theorem Exec.unknowns_agreeS {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak}
    (e₁ : Exec isa c s₁ t₁ s₁') :
    ∀ {s₂ s₂' : State} {t₂ : List Leak} (r₁ r₂ : List Leak), Exec isa c s₂ t₂ s₂' →
      (∀ n ∈ inames c, s₁.syms n = s₂.syms n) → s₁.unknowns = s₂.unknowns → t₁ ++ r₁ = t₂ ++ r₂ → t₁ = t₂ ∧ s₁'.unknowns = s₂'.unknowns := by
  induction e₁ with
  | block h₁ =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | block h₂ =>
      obtain ⟨hl, ha, hb⟩ := execBlock_unknowns h₁ h₂
      exact ⟨(List.append_inj ht hl).1, ha.trans (hu.trans hb.symm)⟩
  | seq x₁ _ ih₁ ih₂ =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    simp only [inames, List.mem_append] at hf
    cases e₂ with
    | seq a₂ b₂ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu'⟩ := ih₁ _ _ a₂ (fun n hn => hf n (.inl hn)) hu ht
      obtain ⟨rfl, hu''⟩ := ih₂ _ _ b₂
        (fun n hn => by rw [Exec.syms x₁, Exec.syms a₂]; exact hf n (.inr hn)) hu' (List.append_cancel_left ht)
      exact ⟨rfl, hu''⟩
  | iteT _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | iteT _ a₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, hu'⟩ := ih _ _ a₂ (fun n hn => hf n (List.mem_append_left _ hn)) hu ht
      exact ⟨rfl, hu'⟩
    | iteF _ _ => exact absurd ht branch_ne
  | iteF _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | iteT _ _ => exact absurd ht.symm branch_ne
    | iteF _ a₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, hu'⟩ := ih _ _ a₂ (fun n hn => hf n (List.mem_append_right _ hn)) hu ht
      exact ⟨rfl, hu'⟩
  | loopExit _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | loopExit b₂ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu'⟩ := ih ([.branch false] ++ r₁) ([.branch false] ++ r₂) b₂ hf hu ht
      exact ⟨rfl, hu'⟩
    | loopNext b₂ _ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, -⟩ := ih _ _ b₂ hf hu ht
      exact absurd (List.append_cancel_left ht).symm branch_ne
  | loopNext x₁ _ _ ih₁ ih₂ =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | loopExit b₂ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, -⟩ := ih₁ _ _ b₂ hf hu ht
      exact absurd (List.append_cancel_left ht) branch_ne
    | loopNext b₂ _ n₂ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu'⟩ := ih₁ _ _ b₂ hf hu ht
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      obtain ⟨rfl, hu''⟩ := ih₂ _ _ n₂ (by rw [Exec.syms x₁, Exec.syms b₂]; exact hf) hu' ht'
      exact ⟨rfl, hu''⟩
  | call hc₁ _ hr ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | call hc₂ b₂ hr₂ =>
      simp only [List.map_nil, List.nil_append, List.append_nil] at ht ⊢
      obtain ⟨rfl, hu'⟩ := ih _ _ b₂ (by rw [call_syms hc₁, call_syms hc₂]; exact hf)
        (by rw [call_unknowns hc₁, call_unknowns hc₂, hu]) ht
      exact ⟨rfl, by rw [ret_unknowns hr, ret_unknowns hr₂, hu']⟩
  | @frame i j _ s₀ _ s₂ _ _ hp _ hq ih =>
    intro s₀' _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | @frame _ _ _ _ _ s₂' _ _ hp₂ b₂ hq₂ =>
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc] at ht
      have hl : (List.map Leak.addr (isa.addrs i s₀)).length = (List.map Leak.addr (isa.addrs i s₀')).length := by
        simp only [List.length_map]; exact RTaintCT.addrs_length i s₀ s₀'
      obtain ⟨h₀, ht'⟩ := List.append_inj ht hl
      obtain ⟨rfl, hu'⟩ := ih _ _ b₂ (by rw [push_syms hp, push_syms hp₂]; exact hf)
        (by rw [push_unknowns hp, push_unknowns hp₂, hu]) ht'
      have hl' : (List.map Leak.addr (isa.addrs j s₂)).length = (List.map Leak.addr (isa.addrs j s₂')).length := by
        simp only [List.length_map]; exact RTaintCT.addrs_length j s₂ s₂'
      have h₃ := (List.append_inj (List.append_cancel_left ht') hl').1
      refine ⟨by rw [h₀, h₃], ?_⟩
      rw [pop_unknowns hq, pop_unknowns hq₂, hu']
  | @icall i _ _ _ s₀ _ s₂ _ _ hi₁ hc₁ _ hr₁ ih =>
    intro s₀' _ _ r₁ r₂ e₂ hf hu ht
    have hn := hf _ (List.mem_cons_self ..)
    cases e₂ with
    | @icall _ _ _ _ _ _ s₂' _ _ hi₂ hc₂ x₂ hr₂ =>
      simp only [List.append_assoc, List.cons_append] at ht
      have hl : (List.map Leak.addr (isa.addrs i s₀)).length = (List.map Leak.addr (isa.addrs i s₀')).length := by
        simp only [List.length_map]; exact RTaintCT.addrs_length i s₀ s₀'
      obtain ⟨h₀, ht'⟩ := List.append_inj ht hl
      simp only [List.cons.injEq] at ht'
      obtain ⟨ha, ht'⟩ := ht'
      simp only [List.map_nil, List.nil_append, List.append_nil] at ht' ⊢
      obtain ⟨rfl, hu'⟩ := ih _ _ x₂ (fun m hm => by
        rw [call_syms hc₁, call_syms hc₂]; exact hf m (by simp [inames, hm]))
        (by rw [call_unknowns hc₁, call_unknowns hc₂, hu]) ht'
      refine ⟨by rw [h₀, ha], ?_⟩
      rw [ret_unknowns hr₁, ret_unknowns hr₂, hu']
    | icallNext hi₂ hne₂ x₂ =>
      exfalso
      obtain ⟨a₂, rest, hi₂', ht₂⟩ := icall_trace x₂
      rw [hi₂] at hi₂'; cases hi₂'
      rw [ht₂] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := List.append_inj ht (by simp only [List.length_map]; exact RTaintCT.addrs_length _ _ _)
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₂
      rw [← ht.1]; exact hn
  | icallNext hi₁ hne₁ x₁ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | icallNext hi₂ hne₂ x₂ =>
      exact ih _ _ x₂ (fun m hm => hf m (List.mem_cons_of_mem _ (List.mem_append_right _ hm))) hu ht
    | icall hi₂ hc₂ x₂ hr₂ =>
      exfalso
      obtain ⟨a₁, rest, hi₁', ht₁⟩ := icall_trace x₁
      rw [hi₁] at hi₁'; cases hi₁'
      rw [ht₁] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := List.append_inj ht (by simp only [List.length_map]; exact RTaintCT.addrs_length _ _ _)
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₁
      rw [ht.1]; exact (hf _ (List.mem_cons_self ..)).symm

theorem Exec.unknowns_agree {c : Prog isa} (hc : noIcall c = true) {s₁ s₁' : State} {t₁ : List Leak}
    (e₁ : Exec isa c s₁ t₁ s₁') {s₂ s₂' : State} {t₂ : List Leak} (r₁ r₂ : List Leak)
    (e₂ : Exec isa c s₂ t₂ s₂') (hu : s₁.unknowns = s₂.unknowns) (ht : t₁ ++ r₁ = t₂ ++ r₂) :
    t₁ = t₂ ∧ s₁'.unknowns = s₂'.unknowns :=
  Exec.unknowns_agreeS e₁ r₁ r₂ e₂ (by rw [inames_of_noIcall hc]; simp) hu ht

/-! ## What the clearing leaves -/

theorem movzs_run : ∀ (rs : List Reg) (u : State),
    execBlock isa (rs.map fun r => .movz .x r 0 0) u =
      some ({ u with gpr := fun q => if q ∈ rs then 0 else u.gpr q }, [])
  | [], u => by
    simp only [List.map_nil, execBlock, List.not_mem_nil, ↓reduceIte]
  | r :: rs, u => by
    simp only [List.map_cons, execBlock, isa, exec, show 16 * 0 < Size.x.bits by decide, ↓reduceIte]
    rw [movzs_run rs]
    simp only [addrs, List.map_nil, List.nil_append, Option.map_some, State.write, List.mem_cons,
      Option.some.injEq, Prod.mk.injEq, and_true]
    congr 1
    funext q
    by_cases h : q ∈ rs
    · simp [h]
    · by_cases hq : q = r
      · subst hq; simp
      · simp [h, hq]

theorem movis_run : ∀ (vs : List VReg) (u : State),
    execBlock isa (vs.map fun v => .vop (.movi0 v)) u =
      some ({ u with v := fun w => if w ∈ vs then 0 else u.v w }, [])
  | [], u => by
    simp only [List.map_nil, execBlock, List.not_mem_nil, ↓reduceIte]
  | v :: vs, u => by
    simp only [List.map_cons, execBlock, isa, exec, VOp.eval, Option.map_some]
    rw [movis_run vs]
    simp only [addrs, List.map_nil, List.nil_append, Option.map_some, State.setV, List.mem_cons,
      Option.some.injEq, Prod.mk.injEq, and_true]
    congr 1
    funext w
    by_cases h : w ∈ vs
    · simp [h]
    · by_cases hw : w = v
      · subst hw; simp
      · simp [h, hw]

theorem inss_run (z : Reg) : ∀ (vs : List VReg) (u : State), u.gpr z = 0 →
    execBlock isa (vs.map fun v => .vop (.ins .d2 v 1 z)) u =
      some ({ u with v := fun w => if w ∈ vs then setLane (u.v w) 64 1 0 else u.v w }, [])
  | [], u, _ => by
    simp only [List.map_nil, execBlock, List.not_mem_nil, ↓reduceIte]
  | v :: vs, u, hz => by
    simp only [List.map_cons, execBlock, isa, exec, VOp.eval, show 1 < 2 by decide, ↓reduceIte,
      Option.map_some, hz]
    rw [inss_run z vs _ (by simp only [State.setV]; exact hz)]
    simp only [addrs, List.map_nil, List.nil_append, Option.map_some, State.setV, List.mem_cons,
      Option.some.injEq, Prod.mk.injEq, and_true]
    congr 1
    funext w
    by_cases h : w ∈ vs
    · by_cases hw : w = v
      · subst hw; simp [h, setLane, BitVec.and_assoc]
      · simp [h, hw]
    · by_cases hw : w = v
      · subst hw; simp [h]
      · simp [h, hw]

/-- The state after `clearsAll` from `u`. -/
def cleared (u : State) : State :=
  { u with
    gpr := fun q => if q ∈ allGprs then 0 else u.gpr q
    v := fun w => if w ∈ hiVecs then setLane (u.v w) 64 1 0 else if w ∈ allVecs then 0 else u.v w
    nf := false, zf := true, c := false, vf := false }

theorem clearsAll_run (u : State) : execBlock isa clearsAll u = some (cleared u, []) := by
  unfold clearsAll
  rw [execBlock_append (M := isa), execBlock_append (M := isa), execBlock_append (M := isa), movzs_run,
    Option.bind_some, movis_run, Option.map_some, Option.bind_some]
  have hx1 : Reg.x1 ∈ allGprs := by decide
  have ht : ∀ w : State, w.gpr .x1 = 0 → execBlock isa [.tst .x .x1 .x1] w =
      some ({ w with nf := false, zf := true, c := false, vf := false }, []) := by
    intro w hw
    simp [execBlock, isa, exec, State.read, hw, addrs]
  rw [ht _ (by simp [hx1]), Option.map_some, Option.bind_some, inss_run .x1 hiVecs _ (by simp [hx1])]
  simp only [Option.map_some, List.append_nil, cleared, Option.some.injEq, Prod.mk.injEq, and_true]
  congr 1
  funext w
  by_cases h : w ∈ hiVecs
  · have : w ∉ allVecs := by revert h; revert w; decide
    simp [h, this]
  · simp [h]

theorem preserved_of {q : Reg} (h0 : q ≠ .x0) (h : q ∉ allGprs) : q ∈ preserved := by
  cases q <;> simp_all [allGprs, preserved]

theorem vreg_cover (w : VReg) (h : w ∉ hiVecs) : w ∈ allVecs := by
  cases w <;> simp_all [hiVecs, allVecs]

theorem preservedV_of {w : VReg} (h : w ∈ hiVecs) : w ∈ preservedV := by
  cases w <;> simp_all [hiVecs, preservedV]

theorem setLane_hi0 {x y : BitVec 128} (h : x.extractLsb' 0 64 = y.extractLsb' 0 64) :
    setLane x 64 1 0 = setLane y 64 1 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb : i < 64 → x.getLsbD i = y.getLsbD i := fun h64 => by
    have := congrArg (fun z : BitVec 64 => z.getLsbD i) h
    simpa [BitVec.getLsbD_extractLsb', h64] using this
  by_cases h64 : i < 64
  · simp [setLane, BitVec.getLsbD_and, hb h64]
  · have hm : (18446744073709551615#128).getLsbD i = false := by
      rw [BitVec.getLsbD_ofNat, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by decide,
        Nat.testBit_two_pow_sub_one]
      simp [h64]
    simp only [setLane]
    simp [hm]

/-- The bits of `x0` above an `rb`-bit result are zero after `retFix rb`, and
its low `rb` bits are what they were. -/
theorem retFix_hi {rb : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (s : State) :
    ∃ g, execBlock isa (retFix rb) s = some ({ s with gpr := g }, []) ∧ (∀ q, q ≠ .x0 → g q = s.gpr q) ∧
      g .x0 >>> rb = (0 : BitVec 64) ∧ (g .x0).setWidth rb = (s.gpr .x0).setWidth rb := by
  rcases hrb with rfl | rfl | rfl
  · refine ⟨fun q => if q = .x0 then 0 else s.gpr q, ?_, fun q hq => by simp [hq], by simp, ?_⟩
    · simp [retFix, execBlock, isa, exec, addrs, State.write]
    · apply BitVec.eq_of_toNat_eq
      have h1 := ((0 : BitVec 64).setWidth 0).isLt
      have h2 := ((s.gpr .x0).setWidth 0).isLt
      simp only [Nat.pow_zero] at h1 h2
      simp only [↓reduceIte]
      omega
  · refine ⟨fun q => if q = .x0 then ((s.gpr .x0).setWidth 32 + 0).setWidth 64 else s.gpr q, ?_,
      fun q hq => by simp [hq], ?_, by simp⟩
    · simp [retFix, execBlock, isa, exec, addrs, State.write, State.read]
    · apply BitVec.eq_of_toNat_eq
      have := ((s.gpr .x0).setWidth 32).isLt
      simp only [↓reduceIte, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_add,
        Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_setWidth] at this
      apply Nat.div_eq_of_lt
      omega
  · refine ⟨s.gpr, by simp [retFix, execBlock], fun _ _ => rfl, ?_, rfl⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (s.gpr .x0).isLt
    exact Nat.div_eq_of_lt this

/-! ## The theorem -/

open VG.AArch64.Scrub VG.AArch64.RTaintG in
theorem withScrubG_range {W : Nat} (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0) (c : Prog isa) :
    withScrubG W (List.range (W / 16)) c = .seq c (scrubTailG W (List.range (W / 16))) := by
  have : List.range (W / 16) ≠ [] := by simp; omega
  cases h : List.range (W / 16) with
  | nil => exact absurd h this
  | cons a l => rfl

theorem range_ok {W : Nat} : ∀ k ∈ List.range (W / 16), 16 * k + 16 ≤ W := by
  intro k hk; have := List.mem_range.mp hk; omega

open VG.AArch64.Scrub in
theorem zeroG_all {W : Nat} (hW : W % 16 = 0) {b x : Addr} (m : Mem) (h : (x - b).toNat < W) :
    zeroG b (List.range (W / 16)) m x = 0 := by
  have hin : inG b (List.range (W / 16)) x = true := by
    simp only [inG, List.any_eq_true, List.mem_range, decide_eq_true_eq]
    exact ⟨(x - b).toNat / 16, by omega, by omega, by omega⟩
  simp [zeroG, hin]

/-- The bytes outside the `W` bytes below `sp` are outside the `n ≤ W` bytes below it. -/
theorem not_below {sp x : Addr} {n W : Nat} (hn : n ≤ W) (hW : W ≤ sp.toNat)
    (h : ¬ (x - (sp - BitVec.ofNat 64 W)).toNat < W) : ¬ (below sp n).Contains x 1 := by
  intro hc
  have hs := below_sub (sp := sp) hn (by have := sp.isLt; omega) x hc
  simp only [Region.Contains] at hs
  omega

open VG.AArch64.Scrub VG.AArch64.RTaintG VG.AArch64.RTaintF in
/-- Code verified against its contract, whose frames stay within the `W`
bytes below the stack pointer (which the contract leaves it), that writes no
PSTATE.DIT and calls indirectly only functions whose addresses two runs
that agree on what is public agree on, run by `scrubAll W rb`, returns
without secret residue with an `rb`-bit result. -/
theorem noResidue_scrubAll {c : Prog isa} {k : Contract isa} {W rb : Nat}
    (hv : Verified target c k) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0)
    (hsp : ∀ s, k.pre s → W ≤ s.sp.toNat) (hd : 16 * c.aarch64Depth ≤ W)
    (hdit : c.all (fun i => !i.writesDit) = true)
    (hsy : ∀ s₁ s₂, k.pub s₁ s₂ → ∀ n ∈ inames c, s₁.syms n = s₂.syms n)
    (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    NoResidue (scrubAll W rb c) k rb := by
  intro s₁ s₂ t₁ t₂ s₁'' s₂'' h₁ h₂ hp ho hu e₁ e₂
  unfold scrubAll at e₁ e₂
  rw [withScrubG_range hW] at e₁ e₂
  -- One run: the code, the clearing, the result's fix and the tail.
  have run : ∀ s t s'', k.pre s → Exec isa (.seq (withRet rb (.seq c (.block clearsAll)))
      (scrubTailG W (List.range (W / 16)))) s t s'' →
      ∃ (t' : List Leak) (u : State) (g : Reg → BitVec 64), Exec isa c s t' u ∧ abiPreserved s u ∧
        (∀ q, q ≠ .x0 → g q = (cleared u).gpr q) ∧ g .x0 >>> rb = (0 : BitVec 64) ∧ TailRunG W (List.range (W / 16)) { cleared u with gpr := g } s'' := by
    intro s t s'' hs e
    obtain ⟨t', u, f, ha, -⟩ := hv.1 s hs
    cases e with
    | seq ea eb =>
    cases ea with
    | seq ea eb' =>
    cases ea with
    | seq ec ecl =>
    obtain ⟨-, rfl⟩ := Exec.det f ec
    cases ecl with
    | block hb =>
    rw [clearsAll_run] at hb
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hb)
    cases eb' with
    | block hb' =>
    obtain ⟨g, hg, hgq, hg0, -⟩ := retFix_hi hrb (cleared u)
    rw [hg] at hb'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hb')
    obtain ⟨u', x, tr⟩ := tailG_run hW range_ok { cleared u with gpr := g }
      (by show W ≤ u.sp.toNat; rw [ha.2.1]; exact hsp s hs)
    obtain ⟨-, rfl⟩ := Exec.det eb x
    exact ⟨t', u, g, f, ha, hgq, hg0, tr⟩
  obtain ⟨t₁', u₁, g₁, f₁, ha₁, hgq₁, hg0₁, tr₁⟩ := run s₁ t₁ s₁'' h₁ e₁
  obtain ⟨t₂', u₂, g₂, f₂, ha₂, hgq₂, hg0₂, tr₂⟩ := run s₂ t₂ s₂'' h₂ e₂
  obtain ⟨hrd, hwr, hg, -, hsp0, hc, hn, hz, hvf, hdi, hvv, hm⟩ := ho
  obtain ⟨hrd₁, hwr₁, hsp₁⟩ := Exec.rdwr f₁
  obtain ⟨hrd₂, hwr₂, hsp₂⟩ := Exec.rdwr f₂
  have hU : u₁.unknowns = u₂.unknowns :=
    (Exec.unknowns_agreeS f₁ [] [] f₂ (hsy s₁ s₂ hp) hu
      (by rw [List.append_nil, List.append_nil]; exact hv.2.1 _ _ _ _ _ _ h₁ h₂ hp f₁ f₂)).2
  have hspu : u₁.sp = u₂.sp := by rw [hsp₁, hsp₂, hsp0]
  refine ⟨by rw [tr₁.rd, tr₂.rd]; exact hrd₁.trans (hrd.trans hrd₂.symm),
    by rw [tr₁.wr, tr₂.wr]; exact hwr₁.trans (hwr.trans hwr₂.symm), fun q hq0 => ?_, ?_,
    by rw [tr₁.sp, tr₂.sp]; exact hspu, by rw [tr₁.c, tr₂.c]; rfl, by rw [tr₁.nf, tr₂.nf]; rfl,
    by rw [tr₁.zf, tr₂.zf]; rfl, by rw [tr₁.vf, tr₂.vf]; rfl,
    by rw [tr₁.dit, tr₂.dit]; exact (Exec.dit hdit f₁).trans (hdi.trans (Exec.dit hdit f₂).symm), ?_, ?_⟩
  · rw [tr₁.gpr, tr₂.gpr]
    by_cases h9 : q = .x9
    · simp only [h9, ↓reduceIte]; show u₁.sp - _ = u₂.sp - _; rw [hspu]
    · simp only [h9, ↓reduceIte, hgq₁ q hq0, hgq₂ q hq0, cleared]
      by_cases hq : q ∈ allGprs
      · simp [hq]
      · simp only [hq, ↓reduceIte]
        have := preserved_of hq0 hq
        rw [ha₁.1 q this, ha₂.1 q this]; exact hg q hq0
  · rw [tr₁.gpr, tr₂.gpr]
    simp only [reduceCtorEq, ↓reduceIte, hg0₁, hg0₂]
  · rw [tr₁.v, tr₂.v]
    funext w
    by_cases h31 : w = .v31
    · simp [h31]
    · simp only [h31, ↓reduceIte, cleared]
      by_cases hh : w ∈ hiVecs
      · simp only [hh, ↓reduceIte]
        apply setLane_hi0
        rw [ha₁.2.2 w (preservedV_of hh), ha₂.2.2 w (preservedV_of hh), hvv]
      · simp [hh, vreg_cover w hh]
  · intro x hx
    rw [tr₁.rd, tr₁.wr] at hx
    change ∀ r ∈ u₁.rd ++ u₁.wr, ¬ r.Contains x 1 at hx
    rw [tr₁.mem, tr₂.mem]
    show lose (zeroG (u₁.sp - _) _ u₁.mem) (u₁.sp - _) W u₁.unknowns x =
      lose (zeroG (u₂.sp - _) _ u₂.mem) (u₂.sp - _) W u₂.unknowns x
    rw [← hspu, ← hU]
    by_cases hin : (x - (u₁.sp - BitVec.ofNat 64 W)).toNat < W
    · exact lose_agree (by rw [zeroG_all hW.2.2 _ hin, zeroG_all hW.2.2 _ hin])
    · rw [lose_out hin, lose_out hin, zeroG_out range_ok _ hin, zeroG_out range_ok _ hin]
      have hd64 : 16 * c.aarch64Depth < 2 ^ 64 := by omega
      have hout : ∀ (s u : State), u.sp = s.sp → u.wr = s.wr → W ≤ s.sp.toNat →
          Frame (s.wr ++ [below s.sp (16 * c.aarch64Depth)]) s.mem u.mem →
          (∀ r ∈ s.wr, ¬ r.Contains x 1) → ¬ (x - (u.sp - BitVec.ofNat 64 W)).toNat < W → u.mem x = s.mem x := by
        intro s u hsp' _ hWs hf hw hn
        refine hf x fun r hr => ?_
        rcases List.mem_append.mp hr with hr | hr
        · exact hw r hr
        · simp only [List.mem_singleton] at hr; subst hr
          rw [hsp'] at hn
          exact not_below hd hWs hn
      rw [hrd₁, hwr₁] at hx
      have hx₂ : ∀ r ∈ s₂.wr, ¬ r.Contains x 1 := fun r hr => hx r (List.mem_append_right _ (hwr ▸ hr))
      rw [hout s₁ u₁ hsp₁ hwr₁ (hsp s₁ h₁) (Exec.frameSp f₁ hd64)
          (fun r hr => hx r (List.mem_append_right _ hr)) hin,
        hout s₂ u₂ hsp₂ hwr₂ (hsp s₂ h₂) (Exec.frameSp f₂ hd64) hx₂ (by rw [← hspu]; exact hin)]
      exact hm x hx

/-! ## Code without frames -/

open VG.AArch64.Scrub VG.AArch64.RTaintG VG.AArch64.RTaintF in
/-- `noResidue_scrubAll` for code without frames, which `scrubAll 0` runs
with no stack zeroed. -/
theorem noResidue_scrubAll0 {c : Prog isa} {k : Contract isa} {rb : Nat}
    (hv : Verified target c k) (hd : c.aarch64Depth = 0)
    (hdit : c.all (fun i => !i.writesDit) = true) (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    NoResidue (scrubAll 0 rb c) k rb := by
  intro s₁ s₂ t₁ t₂ s₁'' s₂'' h₁ h₂ hp ho hu e₁ e₂
  have run : ∀ s t s'', k.pre s → Exec isa (withRet rb (.seq c (.block clearsAll))) s t s'' →
      ∃ (t' : List Leak) (u : State) (g : Reg → BitVec 64), Exec isa c s t' u ∧ abiPreserved s u ∧
        (∀ q, q ≠ .x0 → g q = (cleared u).gpr q) ∧ g .x0 >>> rb = (0 : BitVec 64) ∧
        s'' = { cleared u with gpr := g } := by
    intro s t s'' hs e
    obtain ⟨t', u, f, ha, -⟩ := hv.1 s hs
    cases e with
    | seq ea eb' =>
    cases ea with
    | seq ec ecl =>
    obtain ⟨-, rfl⟩ := Exec.det f ec
    cases ecl with
    | block hb =>
    rw [clearsAll_run] at hb
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hb)
    cases eb' with
    | block hb' =>
    obtain ⟨g, hg, hgq, hg0, -⟩ := retFix_hi hrb (cleared u)
    rw [hg] at hb'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hb')
    exact ⟨t', u, g, f, ha, hgq, hg0, rfl⟩
  obtain ⟨t₁', u₁, g₁, f₁, ha₁, hgq₁, hg0₁, rfl⟩ := run s₁ t₁ s₁'' h₁ e₁
  obtain ⟨t₂', u₂, g₂, f₂, ha₂, hgq₂, hg0₂, rfl⟩ := run s₂ t₂ s₂'' h₂ e₂
  obtain ⟨hrd, hwr, hg, -, hsp0, hc, hn, hz, hvf, hdi, hvv, hm⟩ := ho
  obtain ⟨hrd₁, hwr₁, hsp₁⟩ := Exec.rdwr f₁
  obtain ⟨hrd₂, hwr₂, hsp₂⟩ := Exec.rdwr f₂
  have hspu : u₁.sp = u₂.sp := by rw [hsp₁, hsp₂, hsp0]
  refine ⟨hrd₁.trans (hrd.trans hrd₂.symm), hwr₁.trans (hwr.trans hwr₂.symm), fun q hq0 => ?_,
    by simp only [hg0₁, hg0₂], hspu, rfl, rfl, rfl, rfl,
    (Exec.dit hdit f₁).trans (hdi.trans (Exec.dit hdit f₂).symm), ?_, ?_⟩
  · show g₁ q = g₂ q
    rw [hgq₁ q hq0, hgq₂ q hq0]
    simp only [cleared]
    by_cases hq : q ∈ allGprs
    · simp [hq]
    · simp only [hq, ↓reduceIte]
      have := preserved_of hq0 hq
      rw [ha₁.1 q this, ha₂.1 q this]; exact hg q hq0
  · show (cleared u₁).v = (cleared u₂).v
    funext w
    simp only [cleared]
    by_cases hh : w ∈ hiVecs
    · simp only [hh, ↓reduceIte]
      apply setLane_hi0
      rw [ha₁.2.2 w (preservedV_of hh), ha₂.2.2 w (preservedV_of hh), hvv]
    · simp [hh, vreg_cover w hh]
  · intro x hx
    change ∀ r ∈ u₁.rd ++ u₁.wr, ¬ r.Contains x 1 at hx
    show u₁.mem x = u₂.mem x
    have hd64 : 16 * c.aarch64Depth < 2 ^ 64 := by omega
    have hout : ∀ (s u : State), Frame (s.wr ++ [below s.sp (16 * c.aarch64Depth)]) s.mem u.mem →
        (∀ r ∈ s.wr, ¬ r.Contains x 1) → u.mem x = s.mem x := by
      intro s u hf hw
      refine hf x fun r hr => ?_
      rcases List.mem_append.mp hr with hr | hr
      · exact hw r hr
      · simp only [List.mem_singleton] at hr; subst hr
        rw [hd]
        exact not_below (W := 0) (Nat.le_refl _) (Nat.zero_le _) (by omega)
    rw [hrd₁, hwr₁] at hx
    have hx₂ : ∀ r ∈ s₂.wr, ¬ r.Contains x 1 := fun r hr => hx r (List.mem_append_right _ (hwr ▸ hr))
    rw [hout s₁ u₁ (Exec.frameSp f₁ hd64) (fun r hr => hx r (List.mem_append_right _ hr)),
      hout s₂ u₂ (Exec.frameSp f₂ hd64) hx₂]
    exact hm x hx

/-! ## Keeping the code verified -/

theorem setLane_lo (x : BitVec 128) : (setLane x 64 1 0).extractLsb' 0 64 = x.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i < 128 := by omega
  simp [setLane, hi, hi']
  have hm : (18446744073709551615#128).getLsbD i = true := by
    rw [BitVec.getLsbD_ofNat, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by decide,
      Nat.testBit_two_pow_sub_one]
    simp [hi, hi']
  simp [hm]

/-- What `Verified.scrubAll` needs of a contract: room for the `W` bytes below
the stack pointer, a postcondition that reads neither them, nor any register
but the low `rb` bits of `x0`, and a public stack pointer. -/
structure ScrubAllOk (k : Contract isa) (W rb : Nat) : Prop where
  sp : ∀ s, k.pre s → W ≤ s.sp.toNat
  post : ∀ s u u', k.pre s → k.post s u →
    (∀ a, ¬ (a - (s.sp - BitVec.ofNat 64 W)).toNat < W → u'.mem a = u.mem a) →
    (u'.gpr .x0).setWidth rb = (u.gpr .x0).setWidth rb → k.post s u'
  pub : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.sp = s₂.sp

open VG.AArch64.Scrub VG.AArch64.RTaintG VG.AArch64.RTaintF in
theorem Verified.scrubAll {c : Prog isa} {k : Contract isa} {W rb : Nat} (h : Verified target c k)
    (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0) (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (hk : ScrubAllOk k W rb) :
    Verified target (scrubAll W rb c) k := by
  obtain ⟨hcor, hct, hsat⟩ := h
  have hrun : ∀ s, k.pre s → ∃ t u g u'',
      Exec isa c s t u ∧ abiPreserved s u ∧ k.post s u ∧
      execBlock isa (retFix rb) (cleared u) = some ({ cleared u with gpr := g }, []) ∧
      (∀ q, q ≠ .x0 → g q = (cleared u).gpr q) ∧ (g .x0).setWidth rb = ((cleared u).gpr .x0).setWidth rb ∧
      Exec isa (scrubTailG W (List.range (W / 16))) { cleared u with gpr := g }
        (tailTraceG u.sp W (List.range (W / 16))) u'' ∧
      TailRunG W (List.range (W / 16)) { cleared u with gpr := g } u'' := by
    intro s hs
    obtain ⟨t, u, he, ha, hq⟩ := hcor s hs
    obtain ⟨g, hg, hgq, -, hgx⟩ := retFix_hi hrb (cleared u)
    obtain ⟨u'', ex, tr⟩ := tailG_run hW range_ok { cleared u with gpr := g }
      (by show W ≤ u.sp.toNat; rw [ha.2.1]; exact hk.sp s hs)
    exact ⟨t, u, g, u'', he, ha, hq, hg, hgq, hgx, ex, tr⟩
  have hx0 : Reg.x0 ∉ allGprs := by decide
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, u, g, u'', he, ha, hq, hg, hgq, hgx, ex, tr⟩ := hrun s hs
    refine ⟨((t ++ []) ++ []) ++ tailTraceG u.sp W (List.range (W / 16)), u'', ?_,
      ⟨fun q hq' => ?_, by rw [tr.sp]; exact ha.2.1, fun w hw => ?_⟩, ?_⟩
    · unfold VG.Impl.Residue.AArch64.scrubAll
      rw [withScrubG_range hW]
      exact Exec.seq (Exec.seq (Exec.seq he (Exec.block (clearsAll_run u))) (Exec.block hg)) ex
    · have h9 : q ≠ .x9 := by rintro rfl; simp [preserved] at hq'
      have h0 : q ≠ .x0 := by rintro rfl; simp [preserved] at hq'
      have hng : q ∉ allGprs := by cases q <;> simp_all [preserved, allGprs]
      rw [tr.gpr]; simp only [h9, ↓reduceIte, hgq q h0, cleared, hng]; exact ha.1 q hq'
    · have h31 : w ≠ .v31 := by rintro rfl; simp [preservedV] at hw
      have hh : w ∈ hiVecs := by cases w <;> simp_all [preservedV, hiVecs]
      rw [tr.v]; simp only [h31, ↓reduceIte, cleared, hh, setLane_lo]; exact ha.2.2 w hw
    · refine hk.post s u u'' hs hq (fun a ha' => ?_) ?_
      · have ha'' : ¬ (a - (u.sp - BitVec.ofNat 64 W)).toNat < W := by rw [ha.2.1]; exact ha'
        rw [tr.mem]
        show lose (zeroG (u.sp - BitVec.ofNat 64 W) _ u.mem) (u.sp - BitVec.ofNat 64 W) W _ a = u.mem a
        rw [lose_out ha'', zeroG_out range_ok _ ha'']
      · rw [tr.gpr]
        simp only [reduceCtorEq, ↓reduceIte]
        rw [hgx]
        simp [cleared, hx0]
  · unfold VG.Impl.Residue.AArch64.scrubAll at e₁ e₂
    rw [withScrubG_range hW] at e₁ e₂
    cases e₁ with
    | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
    cases a₁ with
    | seq a₁ r₁ =>
    cases a₂ with
    | seq a₂ r₂ =>
    cases a₁ with
    | seq c₁ l₁ =>
    cases a₂ with
    | seq c₂ l₂ =>
    obtain ⟨_, u₁, g₁, _, f₁, p₁, -, hg₁, -, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨_, u₂, g₂, _, f₂, p₂, -, hg₂, -, -, x₂, -⟩ := hrun s₂ h₂
    obtain ⟨rfl, rfl⟩ := Exec.det c₁ f₁
    obtain ⟨rfl, rfl⟩ := Exec.det c₂ f₂
    cases l₁ with
    | block hl₁ =>
    cases l₂ with
    | block hl₂ =>
    rw [clearsAll_run] at hl₁ hl₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl₁)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl₂)
    cases r₁ with
    | block hr₁ =>
    cases r₂ with
    | block hr₂ =>
    rw [hg₁] at hr₁
    rw [hg₂] at hr₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr₁)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr₂)
    rw [(Exec.det b₁ x₁).1, (Exec.det b₂ x₂).1, p₁.2.1, p₂.2.1,
      hct _ _ _ _ _ _ h₁ h₂ hp c₁ c₂, hk.pub s₁ s₂ hp]

open VG.AArch64.Scrub VG.AArch64.RTaintG VG.AArch64.RTaintF in
/-- `Verified.scrubAll` for code without frames, under `scrubAll 0`. -/
theorem Verified.scrubAll0 {c : Prog isa} {k : Contract isa} {rb : Nat} (h : Verified target c k)
    (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (hk : ScrubAllOk k 0 rb) :
    Verified target (VG.Impl.Residue.AArch64.scrubAll 0 rb c) k := by
  obtain ⟨hcor, hct, hsat⟩ := h
  have hrun : ∀ s, k.pre s → ∃ t u g,
      Exec isa c s t u ∧ abiPreserved s u ∧ k.post s u ∧
      execBlock isa (retFix rb) (cleared u) = some ({ cleared u with gpr := g }, []) ∧
      (∀ q, q ≠ .x0 → g q = (cleared u).gpr q) ∧ (g .x0).setWidth rb = ((cleared u).gpr .x0).setWidth rb := by
    intro s hs
    obtain ⟨t, u, he, ha, hq⟩ := hcor s hs
    obtain ⟨g, hg, hgq, -, hgx⟩ := retFix_hi hrb (cleared u)
    exact ⟨t, u, g, he, ha, hq, hg, hgq, hgx⟩
  have hx0 : Reg.x0 ∉ allGprs := by decide
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, u, g, he, ha, hq, hg, hgq, hgx⟩ := hrun s hs
    refine ⟨(t ++ []) ++ [], { cleared u with gpr := g }, ?_,
      ⟨fun q hq' => ?_, ha.2.1, fun w hw => ?_⟩, ?_⟩
    · exact Exec.seq (Exec.seq he (Exec.block (clearsAll_run u))) (Exec.block hg)
    · have h0 : q ≠ .x0 := by rintro rfl; simp [preserved] at hq'
      have hng : q ∉ allGprs := by cases q <;> simp_all [preserved, allGprs]
      show g q = _
      simp only [hgq q h0, cleared, hng, ↓reduceIte]; exact ha.1 q hq'
    · have hh : w ∈ hiVecs := by cases w <;> simp_all [preservedV, hiVecs]
      show BitVec.extractLsb' 0 64 ((cleared u).v w) = _
      simp only [cleared, hh, ↓reduceIte, setLane_lo]; exact ha.2.2 w hw
    · refine hk.post s u _ hs hq (fun a _ => rfl) ?_
      show (g .x0).setWidth rb = _
      rw [hgx]
      simp [cleared, hx0]
  · cases e₁ with
    | seq a₁ r₁ =>
    cases e₂ with
    | seq a₂ r₂ =>
    cases a₁ with
    | seq c₁ l₁ =>
    cases a₂ with
    | seq c₂ l₂ =>
    obtain ⟨_, u₁, g₁, f₁, p₁, -, hg₁, -⟩ := hrun s₁ h₁
    obtain ⟨_, u₂, g₂, f₂, p₂, -, hg₂, -⟩ := hrun s₂ h₂
    obtain ⟨rfl, rfl⟩ := Exec.det c₁ f₁
    obtain ⟨rfl, rfl⟩ := Exec.det c₂ f₂
    cases l₁ with
    | block hl₁ =>
    cases l₂ with
    | block hl₂ =>
    rw [clearsAll_run] at hl₁ hl₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl₁)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl₂)
    cases r₁ with
    | block hr₁ =>
    cases r₂ with
    | block hr₂ =>
    rw [hg₁] at hr₁
    rw [hg₂] at hr₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr₁)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr₂)
    rw [hct _ _ _ _ _ _ h₁ h₂ hp c₁ c₂]

/-! ## Contracts that `Sig.contract` derives -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- `ScrubAllOk` of a contract whose arguments are all in registers, whose
stack holds the `W` bytes and whose postcondition reads the memory on return
only within the buffers. -/
theorem scrubAllOk_regs (hk : (sig.words abi.ptrBits).length ≤ 8) {W : Nat} (hW : 0 < W)
    (hWs : W ≤ stack)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubAllOk (sig.contract abi pre post wa stack leak) W (sig.retBits abi.ptrBits) where
  sp s hs := (RTaintF.scrubOk_regs (pre := pre) (post := post) (wa := wa) (leak := leak) hk hW hWs hpost).sp s hs
  post s u u' hs hq hm hx := by
    rw [post_regs hk] at hq ⊢
    rw [hx]
    refine hpost _ _ _ _ _ (regArgs_length sig s hk) (fun b hb a ha' => ?_) hq
    have hd := RTaintF.scrub_disjoint hk hW hWs hs b hb a ha'
    exact (hm a fun hlt => hd (show (a - (s.sp - BitVec.ofNat 64 W)).toNat + 1 ≤ W by omega)).symm
  pub s₁ s₂ hp := ((pub_regs hk).mp hp).1.1.1

/-- `scrubAllOk_regs` for a postcondition that reads the memory on return
only within the buffers given the precondition. -/
theorem scrubAllOk_regs_pre (hk : (sig.words abi.ptrBits).length ≤ 8) {W : Nat} (hW : 0 < W)
    (hWs : W ≤ stack)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubAllOk (sig.contract abi pre post wa stack leak) W (sig.retBits abi.ptrBits) where
  sp := RTaintG.sp_of_pre hk hW hWs
  post s u u' hs hq hm hx := by
    have hp := ((pre_regs hk).mp hs).2.2.2.2.2.2
    rw [post_regs hk] at hq ⊢
    rw [hx]
    refine hpost _ _ _ _ _ (regArgs_length sig s hk) hp (fun b hb a ha' => ?_) hq
    have hd := RTaintF.scrub_disjoint hk hW hWs hs b hb a ha'
    exact (hm a fun hlt => hd (show (a - (s.sp - BitVec.ofNat 64 W)).toNat + 1 ≤ W by omega)).symm
  pub s₁ s₂ hp := ((pub_regs hk).mp hp).1.1.1

/-- The `W ≤ stack` bytes below the stack pointer on entry are apart from the
buffers, for a signature with arguments on the stack too. -/
theorem args_disjoint (hl : Sig.noLists sig.params = true) {W : Nat} (hW : 0 < W) (hWs : W ≤ stack)
    {s : State} (hs : (sig.contract abi pre post wa stack leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (allArgs sig s), b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 W, W⟩ := by
  intro b hb
  obtain ⟨-, -, -, -, hres, -, -⟩ := (pre_args (argsOk_of_pre hs) hl).mp hs
  have hst : stackBelow s.sp stack = [⟨s.sp - BitVec.ofNat 64 stack, stack⟩] := by
    cases stack with
    | zero => omega
    | succ n => rfl
  have hr := hres ⟨s.sp - BitVec.ofNat 64 stack, stack⟩ (by rw [hst]; exact List.mem_singleton_self _)
    b (List.mem_append_left _ hb)
  exact hr.symm.sub_right (Offset.sub_below _ hWs (by omega))

/-- `scrubAllOk_regs` for a signature with arguments on the stack too
(`allArgs`): they are above the stack pointer, apart from the `W` bytes below
it, and the postcondition reads them from the memory on entry. -/
theorem scrubAllOk_args (hl : Sig.noLists sig.params = true) {W : Nat} (hW : 0 < W) (hWs : W ≤ stack)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubAllOk (sig.contract abi pre post wa stack leak) W (sig.retBits abi.ptrBits) where
  sp s hs := by
    obtain ⟨⟨h0, -⟩, -⟩ := (pre_args (argsOk_of_pre hs) hl).mp hs
    rcases h0 with h0 | h0 <;> omega
  post s u u' hs hq hm hx := by
    have hA := argsOk_of_pre hs
    rw [post_args hA] at hq ⊢
    rw [hx]
    refine hpost _ _ _ _ _ (allArgs_length sig s) (fun b hb a ha' => ?_) hq
    have hd := args_disjoint hl hW hWs hs b hb a ha'
    exact (hm a fun hlt => hd (show (a - (s.sp - BitVec.ofNat 64 W)).toNat + 1 ≤ W by omega)).symm
  pub s₁ s₂ hp := by
    rcases args_cases sig with h | h
    · simp only [Sig.contract, h] at hp
    · exact ((pub_args h hl).mp hp).1.1.1

/-- `scrubAllOk_args` with no stack zeroed, for code without frames. -/
theorem scrubAllOk_args0 (hl : Sig.noLists sig.params = true)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubAllOk (sig.contract abi pre post wa stack leak) 0 (sig.retBits abi.ptrBits) where
  sp _ _ := Nat.zero_le _
  post s u u' hs hq hm hx := by
    have hA := argsOk_of_pre hs
    rw [post_args hA] at hq ⊢
    rw [hx]
    exact hpost _ _ _ _ _ (allArgs_length sig s) (fun _ _ a _ => (hm a (Nat.not_lt_zero _)).symm) hq
  pub s₁ s₂ hp := by
    rcases args_cases sig with h | h
    · simp only [Sig.contract, h] at hp
    · exact ((pub_args h hl).mp hp).1.1.1

/-- `scrubAllOk_args` over the whole stack, whatever its size. -/
theorem scrubAllOk_args_any (hl : Sig.noLists sig.params = true)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubAllOk (sig.contract abi pre post wa stack leak) stack (sig.retBits abi.ptrBits) := by
  cases stack with
  | zero => exact scrubAllOk_args0 hl hpost
  | succ n => exact scrubAllOk_args hl (Nat.succ_pos n) (Nat.le_refl _) hpost

/-- `scrubAllOk_args_any` for a postcondition that reads the memory on return
only within the buffers given the precondition. -/
theorem scrubAllOk_args_pre_any (hl : Sig.noLists sig.params = true)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubAllOk (sig.contract abi pre post wa stack leak) stack (sig.retBits abi.ptrBits) where
  sp s hs := by
    obtain ⟨⟨h0, -⟩, -⟩ := (pre_args (argsOk_of_pre hs) hl).mp hs
    rcases h0 with h0 | h0 <;> omega
  post s u u' hs hq hm hx := by
    have hA := argsOk_of_pre hs
    have hp := ((pre_args hA hl).mp hs).2.2.2.2.2.2
    rw [post_args hA] at hq ⊢
    rw [hx]
    refine hpost _ _ _ _ _ (allArgs_length sig s) hp (fun b hb a ha' => ?_) hq
    cases stack with
    | zero => exact (hm a (Nat.not_lt_zero _)).symm
    | succ n =>
      have hd := args_disjoint hl (Nat.succ_pos n) (Nat.le_refl _) hs b hb a ha'
      exact (hm a fun hlt => hd (show (a - (s.sp - BitVec.ofNat 64 (n + 1))).toNat + 1 ≤ n + 1 by omega)).symm
  pub s₁ s₂ hp := by
    rcases args_cases sig with h | h
    · simp only [Sig.contract, h] at hp
    · exact ((pub_args h hl).mp hp).1.1.1

/-- `scrubAllOk_regs` with no stack zeroed, for code without frames. -/
theorem scrubAllOk_regs0 (hk : (sig.words abi.ptrBits).length ≤ 8)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubAllOk (sig.contract abi pre post wa stack leak) 0 (sig.retBits abi.ptrBits) where
  sp _ _ := Nat.zero_le _
  post s u u' _ hq hm hx := by
    rw [post_regs hk] at hq ⊢
    rw [hx]
    exact hpost _ _ _ _ _ (regArgs_length sig s hk) (fun _ _ a _ => (hm a (Nat.not_lt_zero _)).symm) hq
  pub s₁ s₂ hp := ((pub_regs hk).mp hp).1.1.1

/-- `ScrubAllOk` under the calling convention with tables of constants. -/
theorem scrubAllOk_consts {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (hk : (sig.words abi.ptrBits).length ≤ 8) {W : Nat} (hW : 0 < W) (hWs : W ≤ stack)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubAllOk (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa stack leak) W
      (sig.retBits abi.ptrBits) where
  sp s hs := (scrubAllOk_regs (pre := pre) (post := post) (wa := wa) (leak := leak) hk hW hWs hpost).sp
    (stripConsts (c₀ :: cs) s) (pre_consts.mp hs).1
  post s u u' hs hq hm hx := by
    have e : ∀ v, (sig.contract abi pre post wa stack leak).post s v ↔
        (sig.contract abi pre post wa stack leak).post (stripConsts (c₀ :: cs) s) v := fun v => by
      rw [post_regs hk, post_regs hk]; rfl
    exact post_consts.mpr ((e u').mpr
      ((scrubAllOk_regs (pre := pre) (post := post) (wa := wa) (leak := leak) hk hW hWs hpost).post
        _ u u' (pre_consts.mp hs).1 ((e u).mp (post_consts.mp hq)) hm hx))
  pub s₁ s₂ hp := (scrubAllOk_regs (pre := pre) (post := post) (wa := wa) (leak := leak) hk hW hWs
    hpost).pub s₁ s₂ (pub_consts.mp hp).1


/-- `scrubAllOk_consts` with no stack zeroed, for code without frames. -/
theorem scrubAllOk_consts0 {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (hk : (sig.words abi.ptrBits).length ≤ 8)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubAllOk (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa stack leak) 0
      (sig.retBits abi.ptrBits) where
  sp s hs := (scrubAllOk_regs0 (pre := pre) (post := post) (wa := wa) (leak := leak) hk hpost).sp
    (stripConsts (c₀ :: cs) s) (pre_consts.mp hs).1
  post s u u' hs hq hm hx := by
    have e : ∀ v, (sig.contract abi pre post wa stack leak).post s v ↔
        (sig.contract abi pre post wa stack leak).post (stripConsts (c₀ :: cs) s) v := fun v => by
      rw [post_regs hk, post_regs hk]; rfl
    exact post_consts.mpr ((e u').mpr
      ((scrubAllOk_regs0 (pre := pre) (post := post) (wa := wa) (leak := leak) hk hpost).post
        _ u u' (pre_consts.mp hs).1 ((e u).mp (post_consts.mp hq)) hm hx))
  pub s₁ s₂ hp := (scrubAllOk_regs0 (pre := pre) (post := post) (wa := wa) (leak := leak) hk
    hpost).pub s₁ s₂ (pub_consts.mp hp).1


/-- `ScrubAllOk` over the whole stack, whatever its size: `scrubAllOk_regs0`
if it is 0, `scrubAllOk_regs` otherwise. -/
theorem scrubAllOk_any (hk : (sig.words abi.ptrBits).length ≤ 8)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubAllOk (sig.contract abi pre post wa stack leak) stack (sig.retBits abi.ptrBits) := by
  cases stack with
  | zero => exact scrubAllOk_regs0 hk hpost
  | succ n => exact scrubAllOk_regs hk (Nat.succ_pos n) (Nat.le_refl _) hpost

/-- `scrubAllOk_any` under the calling convention with tables of constants. -/
theorem scrubAllOk_consts_any {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (hk : (sig.words abi.ptrBits).length ≤ 8)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubAllOk (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa stack leak) stack
      (sig.retBits abi.ptrBits) := by
  cases stack with
  | zero => exact scrubAllOk_consts0 hk hpost
  | succ n => exact scrubAllOk_consts hk (Nat.succ_pos n) (Nat.le_refl _) hpost
end

/-! ## Tables of functions -/

section
variable {A : Abi isa} {sig : Sig} {t : String × List FnTable} {ts : List (String × List FnTable)}
  {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

theorem pre_of_tables {s : State} (h : (sig.contract (A.withTables sig (t :: ts)) pre post wa stack leak).pre s) :
    (sig.contract A pre post wa stack leak).pre s := by
  revert h
  simp only [Sig.contract, Abi.withTables]
  split
  · exact id
  · exact fun h => ⟨h.1.1, h.2⟩

theorem pub_of_tables {s₁ s₂ : State}
    (h : (sig.contract (A.withTables sig (t :: ts)) pre post wa stack leak).pub s₁ s₂) :
    (sig.contract A pre post wa stack leak).pub s₁ s₂ := by
  revert h
  simp only [Sig.contract, Abi.withTables]
  split
  · exact id
  · cases leak with
    | none => exact fun h => ⟨h.1.1, h.2⟩
    | some f => exact fun h => ⟨⟨h.1.1.1, h.1.2⟩, h.2⟩

/-- `ScrubAllOk` under a calling convention with tables of functions, from
`ScrubAllOk` under the convention without them: the tables only add to what
the precondition requires and to what two runs agree on. -/
theorem scrubAllOk_tables {W rb : Nat} (hk : ScrubAllOk (sig.contract A pre post wa stack leak) W rb) :
    ScrubAllOk (sig.contract (A.withTables sig (t :: ts)) pre post wa stack leak) W rb where
  sp s hs := hk.sp s (pre_of_tables hs)
  post s u u' hs hq hm hx := hk.post s u u' (pre_of_tables hs) hq hm hx
  pub s₁ s₂ hp := hk.pub s₁ s₂ (pub_of_tables hp)

end

/-! ## Registering scrubbed code -/

/-- The functions the tables `ts` name. -/
def tableFns (ts : List (String × List FnTable)) : List String := ts.flatMap fun t => t.2.flatMap (·.fns)

/-- The code calls indirectly only the functions of the tables `ts`, whose
addresses two runs agree on (`tables_pub_syms`). -/
def tablesCall (c : Prog isa) (ts : List (String × List FnTable)) : Bool :=
  (inames c).all fun f => decide (f ∈ tableFns ts)

theorem contract_pub {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (h : (sig.contract A pre post wa stack leak).pub s₁ s₂) : A.pub s₁ s₂ := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact h.1
    | some f => exact h.1.1

/-- The functions of the tables have the same addresses in two runs that
agree on what is public. -/
theorem tables_pub_syms {A : Abi isa} {sig : Sig} {ts : List (String × List FnTable)} {pm : Bool}
    {s₁ s₂ : State} (h : ((A.withTables sig ts).withMode pm).pub s₁ s₂) :
    ∀ f ∈ tableFns ts, s₁.syms f = s₂.syms f := by
  have h' : (A.withTables sig ts).pub s₁ s₂ := by
    cases pm
    · exact h
    · exact h.1
  intro f hf
  cases ts with
  | nil => simp [tableFns] at hf
  | cons t ts => exact h'.2.1 f hf

theorem tablesCall_syms {api : Api} {r : Registration api target} (h : tablesCall r.code r.tables = true) :
    ∀ s₁ s₂, r.contract.pub s₁ s₂ → ∀ n ∈ inames r.code, s₁.syms n = s₂.syms n := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  intro s₁ s₂ hp n hn
  rw [e] at hp
  have := List.all_eq_true.mp h n hn
  simp only [decide_eq_true_eq] at this
  exact tables_pub_syms (contract_pub hp) n this

theorem all_true : ∀ c : Prog isa, c.all (fun _ => true) = true
  | .block is => by simp [Code.all]
  | .seq a b => by simp [Code.all, all_true a, all_true b]
  | .ite _ t e => by simp [Code.all, all_true t, all_true e]
  | .loop b _ => by simp [Code.all, all_true b]
  | .call _ b => by simp [Code.all, all_true b]
  | .frame _ b _ => by simp [Code.all, all_true b]
  | .icall _ _ b n => by simp [Code.all, all_true b, all_true n]

theorem all_spSafe (c : Prog isa) : c.all (fun i => !isa.writesSp i) = true := by
  simpa [isa] using all_true c

/-- The result's bits of `r`'s function. -/
abbrev retBitsOf {api : Api} (r : Registration api target) : Nat :=
  api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits

/-- `r`, its code run by `scrubAll` over its whole stack (`r.stack` bytes),
returning without secret residue, if its side conditions hold (checked when
the registration is evaluated); otherwise `r` itself, which then has no
proof (`Registration.residue`), as the emitter allows only of what
`ci/residue_allowlist.txt` lists. For a caller generic over the
implementations of the functions it calls, whose code the residue analysis
does not follow, as x86-64's `X86_64.Scrub.withScrubAll`. -/
def withScrubAll {api : Api} (r : Registration api target) (hok : ScrubAllOk r.contract r.stack (retBitsOf r)) :
    Registration api target :=
  if h : (0 < r.stack ∧ r.stack < 4096 ∧ r.stack % 16 = 0) ∧ 16 * r.code.aarch64Depth ≤ r.stack ∧
      r.code.all (fun i => !i.writesDit) = true ∧ tablesCall r.code r.tables = true ∧
      (retBitsOf r = 0 ∨ retBitsOf r = 32 ∨ retBitsOf r = 64) ∧ r.written = [] then
    { suffix := r.suffix
      tables := r.tables
      code := scrubAll r.stack (retBitsOf r) r.code
      contract := r.contract
      verified := Verified.scrubAll r.verified h.1 h.2.2.2.2.1 hok
      consts := r.consts
      stack := r.stack
      ofApi := r.ofApi
      ofSig := r.ofSig
      spSafe := all_spSafe _
      written := r.written
      writtenOk := by rw [h.2.2.2.2.2]; exact fun _ _ _ _ _ => True.intro
      extra := r.extra
      vendor := r.vendor
      notWith := r.notWith
      residue := some ⟨noResidue_scrubAll r.verified h.1 hok.sp h.2.1 h.2.2.1 (tablesCall_syms h.2.2.2.1)
        h.2.2.2.2.1⟩ }
  else if h : r.stack = 0 ∧ r.code.aarch64Depth = 0 ∧ r.code.all (fun i => !i.writesDit) = true ∧
      (retBitsOf r = 0 ∨ retBitsOf r = 32 ∨ retBitsOf r = 64) ∧ r.written = [] then
    { suffix := r.suffix
      tables := r.tables
      code := scrubAll 0 (retBitsOf r) r.code
      contract := r.contract
      verified := Verified.scrubAll0 r.verified h.2.2.2.1 (h.1 ▸ hok)
      consts := r.consts
      stack := r.stack
      ofApi := r.ofApi
      ofSig := r.ofSig
      spSafe := all_spSafe _
      written := r.written
      writtenOk := by rw [h.2.2.2.2]; exact fun _ _ _ _ _ => True.intro
      extra := r.extra
      vendor := r.vendor
      notWith := r.notWith
      residue := some ⟨noResidue_scrubAll0 r.verified h.2.1 h.2.2.1 h.2.2.2.1⟩ }
  else r

end VG.AArch64.ScrubAll
