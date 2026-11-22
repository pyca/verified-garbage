module

public import VerifiedGarbage.Proof.Sha3.AArch64.CallD8
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
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
theorem Exec.callByD8 {n : String} {b : Prog isa} {s s₁ s₂ s' : State} {t : List Leak}
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
      exact ⟨_, by simp only [Code.viaD8At, ↓reduceIte]; exact Exec.callByD8 hd hc e' hr⟩
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

/-! ## Runs of the code made so are runs of the code -/

theorem umov_run (s : State) :
    execBlock isa [.umov .x .x16 .v8 0] s = some (s.write .x .x16 (laneOf s .v8 0), []) := by
  simp only [execBlock, isa, exec_umov (s := s) (r := .x16) (v := .v8) (l := 0) (by decide),
    Option.map_some, addrs, List.map_nil, List.append_nil]

/-- A run of `callD8 n b`: the call of `n` from the state it starts in, the
address of `n` leaked first. -/
theorem Exec.callD8_inv {n : String} {b : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa (callD8 n b) s t s') :
    ∃ s₁ s₂ tb, isa.call s = some s₁ ∧ Exec isa b s₁ tb s₂ ∧ isa.ret s₁ s₂ = some s' ∧
      t = .addr (s.syms n) :: tb := by
  unfold callD8 at e
  cases e with
  | seq e₁ e₂ =>
    cases e₁ with
    | block hu =>
      rw [umov_run, Option.some.injEq, Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      cases e₂ with
      | icall _ hc fb hr =>
        refine ⟨_, _, _, ?_, fb, hr, ?_⟩
        · show some s.callEntry = some _
          rw [← callEntry_write_x16 s (laneOf s .v8 0)]; exact hc
        · simp only [addrs, List.map_nil, List.nil_append, List.append_nil]; rfl

/-- **A run of `c` made to call `n` by `d8` is a run of `c`**, from and to the
same states. -/
theorem Exec.ofD8₁ {n : String} : ∀ (c : Prog isa), Code.icallFree c = true →
    (∀ i ∈ instrs c, vdstOf i ≠ some .v8) → ∀ {s s' : State} {t' : List Leak},
    Exec isa (Code.viaD8At n c) s t' s' → D8 n s → ∃ t, Exec isa c s t s'
  | .block is, _, _, _, _, _, e, _ => ⟨_, e⟩
  | .seq a b, hc, hv, _, _, _, e, hd => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e with
    | seq e₁ e₂ =>
      have hv₁ : ∀ i ∈ instrs a, vdstOf i ≠ some .v8 := fun i hi => hv i (List.mem_append_left _ hi)
      obtain ⟨_, o₁⟩ := Exec.ofD8₁ a hc.1 hv₁ e₁ hd
      obtain ⟨_, o₂⟩ := Exec.ofD8₁ b hc.2 (fun i hi => hv i (List.mem_append_right _ hi)) e₂ (D8.exec o₁ hv₁ hd)
      exact ⟨_, Exec.seq o₁ o₂⟩
  | .ite cd a b, hc, hv, _, _, _, e, hd => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e with
    | iteT h e =>
      obtain ⟨_, o⟩ := Exec.ofD8₁ a hc.1 (fun i hi => hv i (List.mem_append_left _ hi)) e hd
      exact ⟨_, Exec.iteT h o⟩
    | iteF h e =>
      obtain ⟨_, o⟩ := Exec.ofD8₁ b hc.2 (fun i hi => hv i (List.mem_append_right _ hi)) e hd
      exact ⟨_, Exec.iteF h o⟩
  | .loop b cd, hc, hv, s, s', t', e, hd => by
    simp only [Code.icallFree] at hc
    change Exec isa (.loop (Code.viaD8At n b) cd) s t' s' at e
    have ihb := fun {s s' : State} {t' : List Leak} (e : Exec isa (Code.viaD8At n b) s t' s') (hd : D8 n s) =>
      Exec.ofD8₁ b hc hv e hd
    generalize hL : (Code.loop (Code.viaD8At n b) cd : Prog isa) = L at e
    induction e with
    | loopExit f h =>
      cases hL
      obtain ⟨_, o⟩ := ihb f hd
      exact ⟨_, Exec.loopExit o h⟩
    | loopNext f h _ _ ihr =>
      cases hL
      obtain ⟨_, o⟩ := ihb f hd
      obtain ⟨_, r⟩ := ihr (D8.exec o hv hd) rfl
      exact ⟨_, Exec.loopNext o h r⟩
    | _ => cases hL
  | .call m b, hc, hv, s, s', t', e, hd => by
    simp only [Code.icallFree] at hc
    by_cases hm : m = n
    · subst hm
      have e' : Exec isa (callD8 m (Code.viaD8At m b)) s t' s' := by
        rw [Code.viaD8At, ite_eq_left rfl] at e; exact e
      obtain ⟨s₁, _, _, hcall, fb, hr, -⟩ := Exec.callD8_inv e'
      obtain ⟨_, o⟩ := Exec.ofD8₁ b hc hv fb (D8.call hcall hd)
      exact ⟨_, Exec.call hcall o hr⟩
    · have e' : Exec isa (.call m (Code.viaD8At n b)) s t' s' := by
        rw [Code.viaD8At, ite_eq_right hm] at e; exact e
      cases e' with
      | call hcall fb hr =>
        obtain ⟨_, o⟩ := Exec.ofD8₁ b hc hv fb (D8.call hcall hd)
        exact ⟨_, Exec.call hcall o hr⟩
  | .frame i b j, hc, hv, _, _, _, e, hd => by
    simp only [Code.icallFree] at hc
    cases e with
    | frame hp fb hq =>
      obtain ⟨_, o⟩ := Exec.ofD8₁ b hc (fun i hi => hv i (by simp [instrs, hi])) fb (D8.push hp hd)
      exact ⟨_, Exec.frame hp o hq⟩
  | .icall .., hc, _, _, _, _, _, _ => by simp only [Code.icallFree, Bool.false_eq_true] at hc

/-! ## Two runs leak the same if the runs of the code do -/

/-- The run of the code that a run of it made to call `n` by `d8` is: from
the same state, to the same state. -/
theorem Exec.ofD8_det {n : String} {c : Prog isa} (hc : Code.icallFree c = true)
    (hv : ∀ i ∈ instrs c, vdstOf i ≠ some .v8) {s s' s'' : State} {t' t : List Leak}
    (e : Exec isa (Code.viaD8At n c) s t' s') (o : Exec isa c s t s'') (hd : D8 n s) : s'' = s' := by
  obtain ⟨_, x⟩ := Exec.ofD8₁ c hc hv e hd
  exact (Exec.det o x).2

/-- **Two runs of `c` made to call `n` by `d8`, from states where `d8` holds
`n`'s address, leak the same if the runs of `c` do**: each leaks what that
run of `c` does, with `n`'s address at the same places. -/
theorem Exec.ofD8₂ {n : String} : ∀ (c : Prog isa), Code.icallFree c = true →
    (∀ i ∈ instrs c, vdstOf i ≠ some .v8) → ∀ {s₁ s₂ s₁' s₂' : State} {t₁' t₂' t₁ t₂ : List Leak},
    Exec isa (Code.viaD8At n c) s₁ t₁' s₁' → Exec isa (Code.viaD8At n c) s₂ t₂' s₂' → D8 n s₁ → D8 n s₂ →
    s₁.syms n = s₂.syms n → Exec isa c s₁ t₁ s₁' → Exec isa c s₂ t₂ s₂' → t₁ = t₂ → t₁' = t₂'
  | .block is, _, _, _, _, _, _, _, _, _, _, e₁, e₂, _, _, _, o₁, o₂, h => by
    rw [(Exec.det e₁ o₁).1, (Exec.det e₂ o₂).1]; exact h
  | .seq a b, hc, hv, _, _, _, _, _, _, _, _, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    have hva : ∀ i ∈ instrs a, vdstOf i ≠ some .v8 := fun i hi => hv i (List.mem_append_left _ hi)
    have hvb : ∀ i ∈ instrs b, vdstOf i ≠ some .v8 := fun i hi => hv i (List.mem_append_right _ hi)
    cases e₁ with
    | seq f₁ g₁ =>
    cases e₂ with
    | seq f₂ g₂ =>
    cases o₁ with
    | seq p₁ q₁ =>
    cases o₂ with
    | seq p₂ q₂ =>
    obtain rfl := Exec.ofD8_det hc.1 hva f₁ p₁ hd₁
    obtain rfl := Exec.ofD8_det hc.1 hva f₂ p₂ hd₂
    have hA := Exec.prefix hc.1 p₁ p₂ h
    rw [hA] at h
    have hB := List.append_cancel_left h
    rw [Exec.ofD8₂ a hc.1 hva f₁ f₂ hd₁ hd₂ hy p₁ p₂ hA,
      Exec.ofD8₂ b hc.2 hvb g₁ g₂ (D8.exec p₁ hva hd₁) (D8.exec p₂ hva hd₂)
        (by rw [Exec.syms p₁, Exec.syms p₂]; exact hy) q₁ q₂ hB]
  | .ite cd a b, hc, hv, _, _, _, _, _, _, _, _, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    have hva : ∀ i ∈ instrs a, vdstOf i ≠ some .v8 := fun i hi => hv i (List.mem_append_left _ hi)
    have hvb : ∀ i ∈ instrs b, vdstOf i ≠ some .v8 := fun i hi => hv i (List.mem_append_right _ hi)
    cases e₁ with
    | iteT c₁ f₁ =>
      cases o₁ with
      | iteF c₁' _ => rw [c₁] at c₁'; cases c₁'
      | iteT _ p₁ =>
        cases e₂ with
        | iteF c₂ _ =>
          cases o₂ with
          | iteT c₂' _ => rw [c₂] at c₂'; cases c₂'
          | iteF _ _ => simp only [List.cons.injEq, Leak.branch.injEq] at h; exact absurd h.1 (by decide)
        | iteT c₂ f₂ =>
          cases o₂ with
          | iteF c₂' _ => rw [c₂] at c₂'; cases c₂'
          | iteT _ p₂ =>
            simp only [List.cons.injEq, true_and] at h ⊢
            exact Exec.ofD8₂ a hc.1 hva f₁ f₂ hd₁ hd₂ hy p₁ p₂ h
    | iteF c₁ f₁ =>
      cases o₁ with
      | iteT c₁' _ => rw [c₁] at c₁'; cases c₁'
      | iteF _ p₁ =>
        cases e₂ with
        | iteT c₂ _ =>
          cases o₂ with
          | iteF c₂' _ => rw [c₂] at c₂'; cases c₂'
          | iteT _ _ => simp only [List.cons.injEq, Leak.branch.injEq] at h; exact absurd h.1 (by decide)
        | iteF c₂ f₂ =>
          cases o₂ with
          | iteT c₂' _ => rw [c₂] at c₂'; cases c₂'
          | iteF _ p₂ =>
            simp only [List.cons.injEq, true_and] at h ⊢
            exact Exec.ofD8₂ b hc.2 hvb f₁ f₂ hd₁ hd₂ hy p₁ p₂ h
  | .loop b cd, hc, hv, s₁, s₂, s₁', s₂', t₁', t₂', t₁, t₂, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree] at hc
    have ihb := fun {s₁ s₂ s₁' s₂' : State} {t₁' t₂' t₁ t₂ : List Leak}
      (e₁ : Exec isa (Code.viaD8At n b) s₁ t₁' s₁') (e₂ : Exec isa (Code.viaD8At n b) s₂ t₂' s₂')
      (hd₁ : D8 n s₁) (hd₂ : D8 n s₂) (hy : s₁.syms n = s₂.syms n) (o₁ : Exec isa b s₁ t₁ s₁')
      (o₂ : Exec isa b s₂ t₂ s₂') (h : t₁ = t₂) => Exec.ofD8₂ b hc hv e₁ e₂ hd₁ hd₂ hy o₁ o₂ h
    change Exec isa (.loop (Code.viaD8At n b) cd) s₁ t₁' s₁' at e₁
    change Exec isa (.loop (Code.viaD8At n b) cd) s₂ t₂' s₂' at e₂
    generalize hL : (Code.loop (Code.viaD8At n b) cd : Prog isa) = L at e₁ e₂
    induction e₁ generalizing s₂ s₂' t₂' t₁ t₂ with
    | loopExit f₁ c₁ =>
      cases hL
      cases o₁ with
      | loopNext p₁ c₁' _ =>
        rw [Exec.ofD8_det hc hv f₁ p₁ hd₁, c₁] at c₁'; cases c₁'
      | loopExit p₁ _ =>
        cases e₂ with
        | loopExit f₂ c₂ =>
          cases o₂ with
          | loopNext p₂ c₂' _ => rw [Exec.ofD8_det hc hv f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopExit p₂ _ =>
            have hb := Exec.prefix hc p₁ p₂ h
            rw [ihb f₁ f₂ hd₁ hd₂ hy p₁ p₂ hb]
        | loopNext f₂ c₂ _ =>
          cases o₂ with
          | loopExit p₂ c₂' => rw [Exec.ofD8_det hc hv f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopNext p₂ _ _ =>
            have hb := Exec.prefix hc p₁ p₂ h
            rw [hb, List.append_cancel_left_eq] at h
            simp at h
      | _ => skip
    | loopNext f₁ c₁ r₁ _ ihr =>
      cases hL
      cases o₁ with
      | loopExit p₁ c₁' =>
        rw [Exec.ofD8_det hc hv f₁ p₁ hd₁, c₁] at c₁'; cases c₁'
      | loopNext p₁ _ q₁ =>
        obtain rfl := Exec.ofD8_det hc hv f₁ p₁ hd₁
        cases e₂ with
        | loopExit f₂ c₂ =>
          cases o₂ with
          | loopNext p₂ c₂' _ => rw [Exec.ofD8_det hc hv f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopExit p₂ _ =>
            have hb := Exec.prefix hc p₁ p₂ h
            rw [hb, List.append_cancel_left_eq] at h
            simp at h
        | loopNext f₂ c₂ r₂ =>
          cases o₂ with
          | loopExit p₂ c₂' => rw [Exec.ofD8_det hc hv f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopNext p₂ _ q₂ =>
            obtain rfl := Exec.ofD8_det hc hv f₂ p₂ hd₂
            have hb := Exec.prefix hc p₁ p₂ h
            rw [hb, List.append_cancel_left_eq, List.cons.injEq] at h
            rw [ihb f₁ f₂ hd₁ hd₂ hy p₁ p₂ hb,
              ihr _ _ _ _ _ (D8.exec p₁ hv hd₁) (D8.exec p₂ hv hd₂)
                (by rw [Exec.syms p₁, Exec.syms p₂]; exact hy) q₁ q₂ h.2 rfl r₂]
    | _ => cases hL
  | .call m b, hc, hv, s₁, s₂, s₁', s₂', t₁', t₂', t₁, t₂, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree] at hc
    cases o₁ with
    | call hco₁ p₁ hro₁ =>
    cases o₂ with
    | call hco₂ p₂ hro₂ =>
    simp only [List.map_nil, List.nil_append, List.append_nil] at h
    by_cases hm : m = n
    · subst hm
      have e₁' : Exec isa (callD8 m (Code.viaD8At m b)) s₁ t₁' s₁' := by
        rw [Code.viaD8At, ite_eq_left rfl] at e₁; exact e₁
      have e₂' : Exec isa (callD8 m (Code.viaD8At m b)) s₂ t₂' s₂' := by
        rw [Code.viaD8At, ite_eq_left rfl] at e₂; exact e₂
      obtain ⟨r₁, q₁, _, hc₁, fb₁, hr₁, rfl⟩ := Exec.callD8_inv e₁'
      obtain ⟨r₂, q₂, _, hc₂, fb₂, hr₂, rfl⟩ := Exec.callD8_inv e₂'
      rw [hc₁, Option.some.injEq] at hco₁
      rw [hc₂, Option.some.injEq] at hco₂
      subst hco₁ hco₂
      obtain rfl := Exec.ofD8_det hc hv fb₁ p₁ (D8.call hc₁ hd₁)
      obtain rfl := Exec.ofD8_det hc hv fb₂ p₂ (D8.call hc₂ hd₂)
      rw [hy, Exec.ofD8₂ b hc hv fb₁ fb₂ (D8.call hc₁ hd₁) (D8.call hc₂ hd₂)
        (by rw [call_syms hc₁, call_syms hc₂]; exact hy) p₁ p₂ h]
    · have e₁' : Exec isa (.call m (Code.viaD8At n b)) s₁ t₁' s₁' := by
        rw [Code.viaD8At, ite_eq_right hm] at e₁; exact e₁
      have e₂' : Exec isa (.call m (Code.viaD8At n b)) s₂ t₂' s₂' := by
        rw [Code.viaD8At, ite_eq_right hm] at e₂; exact e₂
      cases e₁' with
      | call hc₁ fb₁ hr₁ =>
      cases e₂' with
      | call hc₂ fb₂ hr₂ =>
      rw [hc₁, Option.some.injEq] at hco₁
      rw [hc₂, Option.some.injEq] at hco₂
      subst hco₁ hco₂
      obtain rfl := Exec.ofD8_det hc hv fb₁ p₁ (D8.call hc₁ hd₁)
      obtain rfl := Exec.ofD8_det hc hv fb₂ p₂ (D8.call hc₂ hd₂)
      simp only [List.map_nil, List.nil_append, List.append_nil]
      exact Exec.ofD8₂ b hc hv fb₁ fb₂ (D8.call hc₁ hd₁) (D8.call hc₂ hd₂)
        (by rw [call_syms hc₁, call_syms hc₂]; exact hy) p₁ p₂ h
  | .frame i b j, hc, hv, s₁, s₂, s₁', s₂', t₁', t₂', t₁, t₂, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree] at hc
    have hvb : ∀ i ∈ instrs b, vdstOf i ≠ some .v8 := fun i' hi => hv i' (by simp [instrs, hi])
    cases e₁ with
    | frame hp₁ fb₁ hq₁ =>
    cases e₂ with
    | frame hp₂ fb₂ hq₂ =>
    cases o₁ with
    | frame hpo₁ p₁ hqo₁ =>
    cases o₂ with
    | frame hpo₂ p₂ hqo₂ =>
    rw [hp₁, Option.some.injEq] at hpo₁
    rw [hp₂, Option.some.injEq] at hpo₂
    subst hpo₁ hpo₂
    obtain rfl := Exec.ofD8_det hc hvb fb₁ p₁ (D8.push hp₁ hd₁)
    obtain rfl := Exec.ofD8_det hc hvb fb₂ p₂ (D8.push hp₂ hd₂)
    simp only [List.append_assoc] at h ⊢
    have hA := List.append_inj h (by simp only [List.length_map]; exact addrs_length _ _ _)
    have hT := Exec.prefix hc p₁ p₂ hA.2
    rw [hT] at hA
    rw [hA.1, Exec.ofD8₂ b hc hvb fb₁ fb₂ (D8.push hp₁ hd₁) (D8.push hp₂ hd₂)
      (by rw [push_syms hp₁, push_syms hp₂]; exact hy) p₁ p₂ hT, List.append_cancel_left hA.2]
  | .icall .., hc, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp only [Code.icallFree, Bool.false_eq_true] at hc

/-- **Code verified against `k` that writes no `v8` and calls no function
by its address is verified made to call `n` by the address in `d8`**, against
`k` from states where `d8` holds `n`'s address, for runs that agree on it. -/
theorem Verified.viaD8At {n : String} {c : Prog isa} {k : Contract isa}
    (h : Verified target c k) (hc : Code.icallFree c = true)
    (hv : ∀ i ∈ instrs c, vdstOf i ≠ some .v8) (hsat : ∃ s, (Contract.d8 n k).pre s) :
    Verified target (Code.viaD8At n c) (Contract.d8 n k) := by
  obtain ⟨hok, hct, -⟩ := h
  refine ⟨fun s ⟨hp, hd⟩ => ?_, fun s₁ s₂ t₁' t₂' s₁' s₂' ⟨hp₁, hd₁⟩ ⟨hp₂, hd₂⟩ ⟨hpub, hy⟩ e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', e, ha, hq⟩ := hok s hp
    obtain ⟨t', e'⟩ := Exec.toD8 e hv hd
    exact ⟨t', s', e', ha, hq⟩
  · obtain ⟨t₁, o₁⟩ := Exec.ofD8₁ c hc hv e₁ hd₁
    obtain ⟨t₂, o₂⟩ := Exec.ofD8₁ c hc hv e₂ hd₂
    exact Exec.ofD8₂ c hc hv e₁ e₂ hd₁ hd₂ hy o₁ o₂ (hct _ _ _ _ _ _ hp₁ hp₂ hpub o₁ o₂)

end VG.Proof.Sha3.AArch64
