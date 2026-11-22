module

public import VerifiedGarbage.Proof.Sha3.AArch64.CallD8
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# Calls of a function made calls by its address in `d8`

`Code.viaD8At n c` is `c` with each call of the function `n` made a call by
the address in `d8` (`umov x16, v8.d[0]`, then `blr x16`, one candidate):
the code of a caller that is the same for every implementation of `n` it
calls. Where `d8` holds `n`'s address (`D8 n`) and `c` writes no `v8`, so
that it still does at each call, each run of `c` is one of `c` made so
(`Exec.toD8`), from the same state to the same state: `blr` enters `n` from
the state the call does, `x16` aside, which the call overwrites. So code
verified against a contract `k` is verified made so against
`Contract.d8 n k` (`Verified.viaD8At`), constant time included: a run of it
leaks what the run of `c` does, with `n`'s address, which two runs agree on,
at each call (`Exec.ofD8`), at the same places in two runs whose runs of `c`
leak the same, since what code leaks tells where each part of it ends
(`Exec.prefix`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64

/-- `umov x16, v8.d[0]; blr x16`: the call of `n`, whose code is `b`, by the
address in `d8`. -/
def callD8 (n : String) (b : Prog isa) : Prog isa :=
  .seq (.block [.umov .x .x16 .v8 0]) (.icall (.blr .x16) n b (.block []))

/-- `c` with each call of `n` made a call by the address in `d8`, in the
bodies of the functions it calls too. -/
def Code.viaD8At (n : String) : Prog isa → Prog isa
  | .block is => .block is
  | .seq a b => .seq (viaD8At n a) (viaD8At n b)
  | .ite cd a b => .ite cd (viaD8At n a) (viaD8At n b)
  | .loop b cd => .loop (viaD8At n b) cd
  | .call m b => if m = n then callD8 n (viaD8At n b) else .call m (viaD8At n b)
  | .frame i b j => .frame i (viaD8At n b) j
  | .icall i m b nx => .icall i m b nx

/-! ## `d8` along a run -/

theorem call_syms {s s' : State} (h : isa.call s = some s') : s'.syms = s.syms := by
  simp only [isa, call, Option.some.injEq] at h
  subst h; rfl

theorem push_syms {i : Instr} {s s' : State} (h : isa.push i s = some s') : s'.syms = s.syms := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  all_goals split at h <;> cases h
  all_goals rfl

/-- `d8` keeps `n`'s address through code that writes no `v8`. -/
theorem D8.exec {n : String} {c : Prog isa} {s s' : State} {t : List Leak} (e : Exec isa c s t s')
    (hv : ∀ i ∈ instrs c, vdstOf i ≠ some .v8) (h : D8 n s) : D8 n s' := by
  unfold D8 at h ⊢; rw [Exec.vec hv e, Exec.syms e]; exact h

theorem D8.call {n : String} {s s' : State} (hc : isa.call s = some s') (h : D8 n s) : D8 n s' := by
  unfold D8 at h ⊢; rw [call_vec hc, call_syms hc]; exact h

theorem D8.push {n : String} {i : Instr} {s s' : State} (hc : isa.push i s = some s') (h : D8 n s) :
    D8 n s' := by
  unfold D8 at h ⊢; rw [push_vec hc, push_syms hc]; exact h

/-- A call enters its callee from the same state whatever `x16` held. -/
theorem callEntry_write_x16 (s : State) (x : BitVec 64) : (s.write .x .x16 x).callEntry = s.callEntry := by
  unfold State.callEntry
  congr 1
  funext r
  by_cases h30 : r = .x30
  · simp only [h30, ↓reduceIte]; rfl
  · by_cases h16 : r = .x16
    · simp only [h16, ↓reduceIte, reduceCtorEq]; rfl
    · simp only [h30, h16, ↓reduceIte]
      split
      · rfl
      · exact RegUpd.gpr_write_of_ne _ _ _ h16

/-- The run of `callD8 n b` from a state where `d8` holds `n`'s address,
from the run of the call of `n`. -/
theorem Exec.callD8 {n : String} {b : Prog isa} {s s₁ s₂ s' : State} {t : List Leak}
    (hd : D8 n s) (hc : isa.call s = some s₁) (e : Exec isa b s₁ t s₂) (hr : isa.ret s₁ s₂ = some s') :
    Exec isa (callD8 n b) s (.addr (s.syms n) :: t) s' := by
  have hu : execBlock isa [.umov .x .x16 .v8 0] s = some (s.write .x .x16 (laneOf s .v8 0), []) := by
    simp only [execBlock, isa, exec_umov (s := s) (r := .x16) (v := .v8) (l := 0) (by decide),
      Option.map_some, addrs, List.map_nil, List.append_nil]
  have hl : laneOf s .v8 0 = s.syms n := hd
  have hi : isa.icall (.blr .x16) (s.write .x .x16 (laneOf s .v8 0)) =
      some (isa.fnAddr (s.write .x .x16 (laneOf s .v8 0)) n) := by
    show some ((s.write .x .x16 (laneOf s .v8 0)).gpr .x16) = some ((s.write .x .x16 (laneOf s .v8 0)).syms n)
    rw [RegUpd.gpr_write_self, hl]; rfl
  have hc' : isa.call (s.write .x .x16 (laneOf s .v8 0)) = some s₁ := by
    rw [show isa.call (s.write .x .x16 (laneOf s .v8 0)) = some (s.write .x .x16 (laneOf s .v8 0)).callEntry
      from rfl, callEntry_write_x16]
    exact hc
  have e' := Exec.seq (Exec.block hu) (Exec.icall (next := .block []) hi hc' e hr)
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at e'
  exact e'

/-- **The run of `c` made to call `n` by `d8`**, from a run of `c`. -/
theorem Exec.toD8 {n : String} {c : Prog isa} {s s' : State} {t : List Leak} (e : Exec isa c s t s')
    (hv : ∀ i ∈ instrs c, vdstOf i ≠ some .v8) (hd : D8 n s) : ∃ t', Exec isa (Code.viaD8At n c) s t' s' := by
  induction e with
  | block h => exact ⟨_, Exec.block h⟩
  | seq e₁ e₂ ih₁ ih₂ =>
    have hv₁ : ∀ i ∈ instrs _, vdstOf i ≠ some .v8 := fun i hi => hv i (List.mem_append_left _ hi)
    have hv₂ : ∀ i ∈ instrs _, vdstOf i ≠ some .v8 := fun i hi => hv i (List.mem_append_right _ hi)
    obtain ⟨_, e₁'⟩ := ih₁ hv₁ hd
    obtain ⟨_, e₂'⟩ := ih₂ hv₂ (D8.exec e₁ hv₁ hd)
    exact ⟨_, Exec.seq e₁' e₂'⟩
  | iteT hc _ ih =>
    obtain ⟨_, e'⟩ := ih (fun i hi => hv i (List.mem_append_left _ hi)) hd
    exact ⟨_, Exec.iteT hc e'⟩
  | iteF hc _ ih =>
    obtain ⟨_, e'⟩ := ih (fun i hi => hv i (List.mem_append_right _ hi)) hd
    exact ⟨_, Exec.iteF hc e'⟩
  | loopExit _ hc ih =>
    obtain ⟨_, e'⟩ := ih hv hd
    exact ⟨_, Exec.loopExit e' hc⟩
  | loopNext e₁ hc _ ih₁ ih₂ =>
    obtain ⟨_, e₁'⟩ := ih₁ hv hd
    obtain ⟨_, e₂'⟩ := ih₂ hv (D8.exec e₁ hv hd)
    exact ⟨_, Exec.loopNext e₁' hc e₂'⟩
  | @call m b _ _ _ _ _ hc _ hr ih =>
    obtain ⟨_, e'⟩ := ih hv (D8.call hc hd)
    by_cases hm : m = n
    · subst hm
      exact ⟨_, by simp only [Code.viaD8At, ↓reduceIte]; exact Exec.callD8 hd hc e' hr⟩
    · exact ⟨_, by simp only [Code.viaD8At, hm, ↓reduceIte]; exact Exec.call hc e' hr⟩
  | frame hp _ hq ih =>
    obtain ⟨_, e'⟩ := ih (fun i hi => hv i (by simp [instrs, hi])) (D8.push hp hd)
    exact ⟨_, Exec.frame hp e' hq⟩
  | icall h₁ h₂ e h₃ _ => exact ⟨_, Exec.icall h₁ h₂ e h₃⟩
  | icallNext h₁ h₂ e _ => exact ⟨_, Exec.icallNext h₁ h₂ e⟩

/-! ## Where a run's leaks end -/

/-- Whether code makes no indirect call. -/
def Code.icallFree : Prog isa → Bool
  | .block _ => true
  | .seq a b => icallFree a && icallFree b
  | .ite _ a b => icallFree a && icallFree b
  | .loop b _ => icallFree b
  | .call _ b => icallFree b
  | .frame _ b _ => icallFree b
  | .icall .. => false

/-- How many addresses an instruction leaks does not depend on the state. -/
theorem addrs_length (i : Instr) (s₁ s₂ : State) : (addrs i s₁).length = (addrs i s₂).length := by
  cases i <;> rfl

theorem execBlock_length {is : List Instr} {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (h₁ : execBlock isa is s₁ = some (s₁', t₁)) (h₂ : execBlock isa is s₂ = some (s₂', t₂)) :
    t₁.length = t₂.length := by
  induction is generalizing s₁ s₂ s₁' s₂' t₁ t₂ with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    rw [← h₁.2, ← h₂.2]
  | cons i is ih =>
    simp only [execBlock] at h₁ h₂
    split at h₁ <;> rename_i heq₁
    · cases h₁
    split at h₂ <;> rename_i heq₂
    · cases h₂
    obtain ⟨⟨a₁, r₁⟩, ha₁, e₁⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨⟨a₂, r₂⟩, ha₂, e₂⟩ := Option.map_eq_some_iff.mp h₂
    simp only [Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2, List.length_append, List.length_append, List.length_map, List.length_map,
      addrs_length i _ s₂, ih ha₁ ha₂]

/-- **What a run of code without indirect calls leaks tells where it ends**:
of two runs, whose leaks followed by others are the same, the two leak the
same. -/
theorem Exec.prefix {c : Prog isa} (hc : Code.icallFree c = true) {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (e₁ : Exec isa c s₁ t₁ s₁') (e₂ : Exec isa c s₂ t₂ s₂') {u₁ u₂ : List Leak} (h : t₁ ++ u₁ = t₂ ++ u₂) :
    t₁ = t₂ := by
  induction e₁ generalizing s₂ s₂' t₂ u₁ u₂ with
  | block h₁ =>
    cases e₂ with
    | block h₂ => exact (List.append_inj h (execBlock_length h₁ h₂)).1
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e₂ with
    | seq f₁ f₂ =>
      rw [List.append_assoc, List.append_assoc] at h
      have ha := ih₁ hc.1 f₁ h
      rw [ha] at h
      rw [ha, ih₂ hc.2 f₂ (List.append_cancel_left h)]
  | iteT _ _ ih =>
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ f => simp only [List.cons_append, List.cons.injEq, true_and] at h; rw [ih hc.1 f h]
    | iteF _ _ => simp only [List.cons_append, List.cons.injEq, Leak.branch.injEq] at h; exact absurd h.1 (by decide)
  | iteF _ _ ih =>
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ _ => simp only [List.cons_append, List.cons.injEq, Leak.branch.injEq] at h; exact absurd h.1 (by decide)
    | iteF _ f => simp only [List.cons_append, List.cons.injEq, true_and] at h; rw [ih hc.2 f h]
  | loopExit _ _ ih =>
    simp only [Code.icallFree] at hc
    cases e₂ with
    | loopExit f _ =>
      simp only [List.append_assoc, List.singleton_append] at h
      rw [ih hc f h]
    | loopNext f _ _ =>
      simp only [List.append_assoc, List.cons_append] at h
      have hb := ih hc f h
      rw [hb] at h
      simp only [List.append_cancel_left_eq, List.cons.injEq, Leak.branch.injEq] at h
      exact absurd h.1 (by decide)
  | loopNext _ _ _ ih₁ ih₂ =>
    have hc' := hc
    simp only [Code.icallFree] at hc
    cases e₂ with
    | loopExit f _ =>
      simp only [List.append_assoc, List.cons_append] at h
      have hb := ih₁ hc f h
      rw [hb] at h
      simp only [List.append_cancel_left_eq, List.cons.injEq, Leak.branch.injEq] at h
      exact absurd h.1 (by decide)
    | loopNext f _ f' =>
      simp only [List.append_assoc, List.cons_append] at h
      have hb := ih₁ hc f h
      rw [hb] at h
      simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at h
      rw [hb, ih₂ hc' f' h]
  | call _ _ _ ih =>
    simp only [Code.icallFree] at hc
    cases e₂ with
    | call _ f _ =>
      simp only [List.map_nil, List.nil_append, List.append_nil] at h ⊢
      exact ih hc f h
  | frame _ _ _ ih =>
    simp only [Code.icallFree] at hc
    cases e₂ with
    | frame _ f _ =>
      simp only [List.append_assoc] at h
      have hA := List.append_inj h (by simp only [List.length_map]; exact addrs_length _ _ _)
      have hT := ih hc f hA.2
      rw [hT] at hA
      have hB := List.append_inj (List.append_cancel_left hA.2)
        (by simp only [List.length_map]; exact addrs_length _ _ _)
      rw [hA.1, hT, hB.1]
  | icall => simp only [Code.icallFree, Bool.false_eq_true] at hc
  | icallNext => simp only [Code.icallFree, Bool.false_eq_true] at hc

end VG.Proof.Sha3.AArch64
