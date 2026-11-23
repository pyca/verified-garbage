module

public import VerifiedGarbage.Impl.ICall.Arm
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.TCB.Artifact

/-!
# Calls of a function made calls by its address in a register, on ARMv7

`Code.viaRegAt n r c` is `c` with each call of the function `n` made a call
by the address in `r` (`blx r`, one candidate): the code of a caller that is
the same for every implementation of `n` it calls. Where `r` holds `n`'s
address (`RegAt n r`) and no instruction of `c` writes `r`, which a call does
not change (`r ∉ linkRegs`), so that it still does at each call, each run of
`c` is one of `c` made so (`Exec.toReg`), from the same state to the same
state. So code verified against a contract `k` is verified made so against
`Contract.reg n r k` (`Verified.viaRegAt`), constant time included: a run of
it leaks what the run of `c` does, with `n`'s address, which two runs agree
on, at each call (`Exec.ofReg₂`), at the same places in two runs whose runs
of `c` leak the same, since what code leaks tells where each part of it ends
(`Exec.prefix`).
-/

@[expose] public section

namespace VG.Proof.Arm

open VG VG.Arm VG.Impl.Arm

/-- `r` holds `n`'s address. -/
def RegAt (n : String) (r : Reg) (s : State) : Prop := s.gpr r = s.syms n

/-- `k` from states where `r` holds `n`'s address, for runs that agree on it. -/
def Contract.reg (n : String) (r : Reg) (k : Contract isa) : Contract isa :=
  ⟨fun s => k.pre s ∧ RegAt n r s, k.post, fun s t => k.pub s t ∧ s.syms n = t.syms n⟩

/-- What the lift needs of the code: no instruction writes `r`, which a call
does not change. -/
def KeepsReg (r : Reg) (c : Prog isa) : Prop := r ∉ linkRegs ∧ ∀ i ∈ instrs c, clobbers i r = false

theorem call_syms {s s' : State} (h : isa.call s = some s') : s'.syms = s.syms := by
  simp only [isa, call, Option.some.injEq] at h
  subst h; rfl

theorem KeepsReg.seq₁ {r : Reg} {a b : Prog isa} (h : KeepsReg r (.seq a b)) : KeepsReg r a :=
  ⟨h.1, fun i hi => h.2 i (List.mem_append_left _ hi)⟩

theorem KeepsReg.seq₂ {r : Reg} {a b : Prog isa} (h : KeepsReg r (.seq a b)) : KeepsReg r b :=
  ⟨h.1, fun i hi => h.2 i (List.mem_append_right _ hi)⟩

theorem KeepsReg.ite₁ {r : Reg} {cd : Cond} {a b : Prog isa} (h : KeepsReg r (.ite cd a b)) : KeepsReg r a :=
  ⟨h.1, fun i hi => h.2 i (List.mem_append_left _ hi)⟩

theorem KeepsReg.ite₂ {r : Reg} {cd : Cond} {a b : Prog isa} (h : KeepsReg r (.ite cd a b)) : KeepsReg r b :=
  ⟨h.1, fun i hi => h.2 i (List.mem_append_right _ hi)⟩

theorem KeepsReg.frame {r : Reg} {i j : Instr} {b : Prog isa} (h : KeepsReg r (.frame i b j)) :
    KeepsReg r b :=
  ⟨h.1, fun i' hi => h.2 i' (by simp [instrs, hi])⟩

/-! ## `r` along a run -/

theorem RegAt.exec {n : String} {r : Reg} {c : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa c s t s') (hv : KeepsReg r c) (h : RegAt n r s) : RegAt n r s' := by
  unfold RegAt at h ⊢; rw [Exec.gpr hv.2 e (.inr hv.1), Exec.syms e]; exact h

theorem RegAt.call {n : String} {r : Reg} {s s' : State} (hc : isa.call s = some s') (hl : r ∉ linkRegs)
    (h : RegAt n r s) : RegAt n r s' := by
  unfold RegAt at h ⊢; rw [(call_eq hc).2.2.2.2 r hl, call_syms hc]; exact h

theorem RegAt.push {n : String} {r : Reg} {i : Instr} {s s' : State} (hc : isa.push i s = some s')
    (h : RegAt n r s) : RegAt n r s' := by
  obtain ⟨_, -, -, hg, -⟩ := push_eq hc
  unfold RegAt at h ⊢; rw [hg, push_syms hc]; exact h

theorem icall_reg {n : String} {r : Reg} {s : State} (hd : RegAt n r s) :
    isa.icall (.blx r) s = some (isa.fnAddr s n) := by
  show some ((s.gpr r).setWidth 64) = some ((s.syms n).setWidth 64)
  rw [hd]

/-- The run of `callReg n r b` from a state where `r` holds `n`'s address,
from the run of the call of `n`. -/
theorem Exec.callByReg {n : String} {r : Reg} {b : Prog isa} {s s₁ s₂ s' : State} {t : List Leak}
    (hd : RegAt n r s) (hc : isa.call s = some s₁) (e : Exec isa b s₁ t s₂) (hr : isa.ret s₁ s₂ = some s') :
    Exec isa (callReg n r b) s (.addr ((s.syms n).setWidth 64) :: t) s' := by
  have e' := Exec.icall (next := .block []) (icall_reg hd) hc e hr
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at e'
  exact e'

/-- **The run of `c` made to call `n` by `r`**, from a run of `c`. -/
theorem Exec.toReg {n : String} {r : Reg} {c : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa c s t s') (hv : KeepsReg r c) (hd : RegAt n r s) :
    ∃ t', Exec isa (Code.viaRegAt n r c) s t' s' := by
  induction e with
  | block h => exact ⟨_, Exec.block h⟩
  | seq e₁ e₂ ih₁ ih₂ =>
    obtain ⟨_, e₁'⟩ := ih₁ hv.seq₁ hd
    obtain ⟨_, e₂'⟩ := ih₂ hv.seq₂ (RegAt.exec e₁ hv.seq₁ hd)
    exact ⟨_, Exec.seq e₁' e₂'⟩
  | iteT hc _ ih =>
    obtain ⟨_, e'⟩ := ih hv.ite₁ hd
    exact ⟨_, Exec.iteT hc e'⟩
  | iteF hc _ ih =>
    obtain ⟨_, e'⟩ := ih hv.ite₂ hd
    exact ⟨_, Exec.iteF hc e'⟩
  | loopExit _ hc ih =>
    obtain ⟨_, e'⟩ := ih hv hd
    exact ⟨_, Exec.loopExit e' hc⟩
  | loopNext e₁ hc _ ih₁ ih₂ =>
    obtain ⟨_, e₁'⟩ := ih₁ hv hd
    obtain ⟨_, e₂'⟩ := ih₂ hv (RegAt.exec e₁ hv hd)
    exact ⟨_, Exec.loopNext e₁' hc e₂'⟩
  | @call m b _ _ _ _ _ hc _ hr ih =>
    obtain ⟨_, e'⟩ := ih hv (RegAt.call hc hv.1 hd)
    by_cases hm : m = n
    · subst hm
      exact ⟨_, by simp only [Code.viaRegAt, ↓reduceIte]; exact Exec.callByReg hd hc e' hr⟩
    · exact ⟨_, by simp only [Code.viaRegAt, hm, ↓reduceIte]; exact Exec.call hc e' hr⟩
  | frame hp _ hq ih =>
    obtain ⟨_, e'⟩ := ih hv.frame (RegAt.push hp hd)
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
  cases i <;> simp [addrs, words]

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
      show (isa.addrs i _).length = (isa.addrs i s₂).length from addrs_length i _ s₂, ih ha₁ ha₂]

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

/-- A run of `callReg n r b`: the call of `n` from the state it starts in, the
address of `n` leaked first. -/
theorem Exec.callReg_inv {n : String} {r : Reg} {b : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa (callReg n r b) s t s') :
    ∃ s₁ s₂ tb, isa.call s = some s₁ ∧ Exec isa b s₁ tb s₂ ∧ isa.ret s₁ s₂ = some s' ∧
      t = .addr ((s.syms n).setWidth 64) :: tb := by
  unfold callReg Code.icalls Code.icalls at e
  cases e with
  | icall _ hc fb hr =>
    refine ⟨_, _, _, hc, fb, hr, ?_⟩
    simp only [addrs, List.map_nil, List.nil_append, List.append_nil]

/-- **A run of `c` made to call `n` by `r` is a run of `c`**, from and to the
same states. -/
theorem Exec.ofReg₁ {n : String} {r : Reg} : ∀ (c : Prog isa), Code.icallFree c = true →
    KeepsReg r c → ∀ {s s' : State} {t' : List Leak},
    Exec isa (Code.viaRegAt n r c) s t' s' → RegAt n r s → ∃ t, Exec isa c s t s'
  | .block is, _, _, _, _, _, e, _ => ⟨_, e⟩
  | .seq a b, hc, hv, _, _, _, e, hd => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e with
    | seq e₁ e₂ =>
      have hv₁ : KeepsReg r a := ⟨hv.1, fun i hi => hv.2 i (List.mem_append_left _ hi)⟩
      obtain ⟨_, o₁⟩ := Exec.ofReg₁ a hc.1 hv₁ e₁ hd
      obtain ⟨_, o₂⟩ := Exec.ofReg₁ b hc.2 ⟨hv.1, fun i hi => hv.2 i (List.mem_append_right _ hi)⟩ e₂ (RegAt.exec o₁ hv₁ hd)
      exact ⟨_, Exec.seq o₁ o₂⟩
  | .ite cd a b, hc, hv, _, _, _, e, hd => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e with
    | iteT h e =>
      obtain ⟨_, o⟩ := Exec.ofReg₁ a hc.1 ⟨hv.1, fun i hi => hv.2 i (List.mem_append_left _ hi)⟩ e hd
      exact ⟨_, Exec.iteT h o⟩
    | iteF h e =>
      obtain ⟨_, o⟩ := Exec.ofReg₁ b hc.2 ⟨hv.1, fun i hi => hv.2 i (List.mem_append_right _ hi)⟩ e hd
      exact ⟨_, Exec.iteF h o⟩
  | .loop b cd, hc, hv, s, s', t', e, hd => by
    simp only [Code.icallFree] at hc
    change Exec isa (.loop (Code.viaRegAt n r b) cd) s t' s' at e
    have ihb := fun {s s' : State} {t' : List Leak} (e : Exec isa (Code.viaRegAt n r b) s t' s') (hd : RegAt n r s) =>
      Exec.ofReg₁ b hc hv e hd
    generalize hL : (Code.loop (Code.viaRegAt n r b) cd : Prog isa) = L at e
    induction e with
    | loopExit f h =>
      cases hL
      obtain ⟨_, o⟩ := ihb f hd
      exact ⟨_, Exec.loopExit o h⟩
    | loopNext f h _ _ ihr =>
      cases hL
      obtain ⟨_, o⟩ := ihb f hd
      obtain ⟨_, r⟩ := ihr (RegAt.exec o hv hd) rfl
      exact ⟨_, Exec.loopNext o h r⟩
    | _ => cases hL
  | .call m b, hc, hv, s, s', t', e, hd => by
    simp only [Code.icallFree] at hc
    by_cases hm : m = n
    · subst hm
      have e' : Exec isa (callReg m r (Code.viaRegAt m r b)) s t' s' := by
        rw [Code.viaRegAt, ite_eq_left rfl] at e; exact e
      obtain ⟨s₁, _, _, hcall, fb, hr, -⟩ := Exec.callReg_inv e'
      obtain ⟨_, o⟩ := Exec.ofReg₁ b hc hv fb (RegAt.call hcall hv.1 hd)
      exact ⟨_, Exec.call hcall o hr⟩
    · have e' : Exec isa (.call m (Code.viaRegAt n r b)) s t' s' := by
        rw [Code.viaRegAt, ite_eq_right hm] at e; exact e
      cases e' with
      | call hcall fb hr =>
        obtain ⟨_, o⟩ := Exec.ofReg₁ b hc hv fb (RegAt.call hcall hv.1 hd)
        exact ⟨_, Exec.call hcall o hr⟩
  | .frame i b j, hc, hv, _, _, _, e, hd => by
    simp only [Code.icallFree] at hc
    cases e with
    | frame hp fb hq =>
      obtain ⟨_, o⟩ := Exec.ofReg₁ b hc hv.frame fb (RegAt.push hp hd)
      exact ⟨_, Exec.frame hp o hq⟩
  | .icall .., hc, _, _, _, _, _, _ => by simp only [Code.icallFree, Bool.false_eq_true] at hc

/-! ## Two runs leak the same if the runs of the code do -/

/-- The run of the code that a run of it made to call `n` by `r` is: from
the same state, to the same state. -/
theorem Exec.ofReg_det {n : String} {r : Reg} {c : Prog isa} (hc : Code.icallFree c = true)
    (hv : KeepsReg r c) {s s' s'' : State} {t' t : List Leak}
    (e : Exec isa (Code.viaRegAt n r c) s t' s') (o : Exec isa c s t s'') (hd : RegAt n r s) : s'' = s' := by
  obtain ⟨_, x⟩ := Exec.ofReg₁ c hc hv e hd
  exact (Exec.det o x).2

/-- **Two runs of `c` made to call `n` by `r`, from states where `r` holds
`n`'s address, leak the same if the runs of `c` do**: each leaks what that
run of `c` does, with `n`'s address at the same places. -/
theorem Exec.ofReg₂ {n : String} {r : Reg} : ∀ (c : Prog isa), Code.icallFree c = true →
    KeepsReg r c → ∀ {s₁ s₂ s₁' s₂' : State} {t₁' t₂' t₁ t₂ : List Leak},
    Exec isa (Code.viaRegAt n r c) s₁ t₁' s₁' → Exec isa (Code.viaRegAt n r c) s₂ t₂' s₂' → RegAt n r s₁ → RegAt n r s₂ →
    s₁.syms n = s₂.syms n → Exec isa c s₁ t₁ s₁' → Exec isa c s₂ t₂ s₂' → t₁ = t₂ → t₁' = t₂'
  | .block is, _, _, _, _, _, _, _, _, _, _, e₁, e₂, _, _, _, o₁, o₂, h => by
    rw [(Exec.det e₁ o₁).1, (Exec.det e₂ o₂).1]; exact h
  | .seq a b, hc, hv, _, _, _, _, _, _, _, _, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    have hva : KeepsReg r a := ⟨hv.1, fun i hi => hv.2 i (List.mem_append_left _ hi)⟩
    have hvb : KeepsReg r b := ⟨hv.1, fun i hi => hv.2 i (List.mem_append_right _ hi)⟩
    cases e₁ with
    | seq f₁ g₁ =>
    cases e₂ with
    | seq f₂ g₂ =>
    cases o₁ with
    | seq p₁ q₁ =>
    cases o₂ with
    | seq p₂ q₂ =>
    obtain rfl := Exec.ofReg_det hc.1 hva f₁ p₁ hd₁
    obtain rfl := Exec.ofReg_det hc.1 hva f₂ p₂ hd₂
    have hA := Exec.prefix hc.1 p₁ p₂ h
    rw [hA] at h
    have hB := List.append_cancel_left h
    rw [Exec.ofReg₂ a hc.1 hva f₁ f₂ hd₁ hd₂ hy p₁ p₂ hA,
      Exec.ofReg₂ b hc.2 hvb g₁ g₂ (RegAt.exec p₁ hva hd₁) (RegAt.exec p₂ hva hd₂)
        (by rw [Exec.syms p₁, Exec.syms p₂]; exact hy) q₁ q₂ hB]
  | .ite cd a b, hc, hv, _, _, _, _, _, _, _, _, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    have hva : KeepsReg r a := ⟨hv.1, fun i hi => hv.2 i (List.mem_append_left _ hi)⟩
    have hvb : KeepsReg r b := ⟨hv.1, fun i hi => hv.2 i (List.mem_append_right _ hi)⟩
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
            exact Exec.ofReg₂ a hc.1 hva f₁ f₂ hd₁ hd₂ hy p₁ p₂ h
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
            exact Exec.ofReg₂ b hc.2 hvb f₁ f₂ hd₁ hd₂ hy p₁ p₂ h
  | .loop b cd, hc, hv, s₁, s₂, s₁', s₂', t₁', t₂', t₁, t₂, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree] at hc
    have ihb := fun {s₁ s₂ s₁' s₂' : State} {t₁' t₂' t₁ t₂ : List Leak}
      (e₁ : Exec isa (Code.viaRegAt n r b) s₁ t₁' s₁') (e₂ : Exec isa (Code.viaRegAt n r b) s₂ t₂' s₂')
      (hd₁ : RegAt n r s₁) (hd₂ : RegAt n r s₂) (hy : s₁.syms n = s₂.syms n) (o₁ : Exec isa b s₁ t₁ s₁')
      (o₂ : Exec isa b s₂ t₂ s₂') (h : t₁ = t₂) => Exec.ofReg₂ b hc hv e₁ e₂ hd₁ hd₂ hy o₁ o₂ h
    change Exec isa (.loop (Code.viaRegAt n r b) cd) s₁ t₁' s₁' at e₁
    change Exec isa (.loop (Code.viaRegAt n r b) cd) s₂ t₂' s₂' at e₂
    generalize hL : (Code.loop (Code.viaRegAt n r b) cd : Prog isa) = L at e₁ e₂
    induction e₁ generalizing s₂ s₂' t₂' t₁ t₂ with
    | loopExit f₁ c₁ =>
      cases hL
      cases o₁ with
      | loopNext p₁ c₁' _ =>
        rw [Exec.ofReg_det hc hv f₁ p₁ hd₁, c₁] at c₁'; cases c₁'
      | loopExit p₁ _ =>
        cases e₂ with
        | loopExit f₂ c₂ =>
          cases o₂ with
          | loopNext p₂ c₂' _ => rw [Exec.ofReg_det hc hv f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopExit p₂ _ =>
            have hb := Exec.prefix hc p₁ p₂ h
            rw [ihb f₁ f₂ hd₁ hd₂ hy p₁ p₂ hb]
        | loopNext f₂ c₂ _ =>
          cases o₂ with
          | loopExit p₂ c₂' => rw [Exec.ofReg_det hc hv f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopNext p₂ _ _ =>
            have hb := Exec.prefix hc p₁ p₂ h
            rw [hb, List.append_cancel_left_eq] at h
            simp at h
      | _ => skip
    | loopNext f₁ c₁ r₁ _ ihr =>
      cases hL
      cases o₁ with
      | loopExit p₁ c₁' =>
        rw [Exec.ofReg_det hc hv f₁ p₁ hd₁, c₁] at c₁'; cases c₁'
      | loopNext p₁ _ q₁ =>
        obtain rfl := Exec.ofReg_det hc hv f₁ p₁ hd₁
        cases e₂ with
        | loopExit f₂ c₂ =>
          cases o₂ with
          | loopNext p₂ c₂' _ => rw [Exec.ofReg_det hc hv f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopExit p₂ _ =>
            have hb := Exec.prefix hc p₁ p₂ h
            rw [hb, List.append_cancel_left_eq] at h
            simp at h
        | loopNext f₂ c₂ r₂ =>
          cases o₂ with
          | loopExit p₂ c₂' => rw [Exec.ofReg_det hc hv f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopNext p₂ _ q₂ =>
            obtain rfl := Exec.ofReg_det hc hv f₂ p₂ hd₂
            have hb := Exec.prefix hc p₁ p₂ h
            rw [hb, List.append_cancel_left_eq, List.cons.injEq] at h
            rw [ihb f₁ f₂ hd₁ hd₂ hy p₁ p₂ hb,
              ihr _ _ _ _ _ (RegAt.exec p₁ hv hd₁) (RegAt.exec p₂ hv hd₂)
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
      have e₁' : Exec isa (callReg m r (Code.viaRegAt m r b)) s₁ t₁' s₁' := by
        rw [Code.viaRegAt, ite_eq_left rfl] at e₁; exact e₁
      have e₂' : Exec isa (callReg m r (Code.viaRegAt m r b)) s₂ t₂' s₂' := by
        rw [Code.viaRegAt, ite_eq_left rfl] at e₂; exact e₂
      obtain ⟨r₁, q₁, _, hc₁, fb₁, hr₁, rfl⟩ := Exec.callReg_inv e₁'
      obtain ⟨r₂, q₂, _, hc₂, fb₂, hr₂, rfl⟩ := Exec.callReg_inv e₂'
      rw [hc₁, Option.some.injEq] at hco₁
      rw [hc₂, Option.some.injEq] at hco₂
      subst hco₁ hco₂
      obtain rfl := Exec.ofReg_det hc hv fb₁ p₁ (RegAt.call hc₁ hv.1 hd₁)
      obtain rfl := Exec.ofReg_det hc hv fb₂ p₂ (RegAt.call hc₂ hv.1 hd₂)
      rw [hy, Exec.ofReg₂ b hc hv fb₁ fb₂ (RegAt.call hc₁ hv.1 hd₁) (RegAt.call hc₂ hv.1 hd₂)
        (by rw [call_syms hc₁, call_syms hc₂]; exact hy) p₁ p₂ h]
    · have e₁' : Exec isa (.call m (Code.viaRegAt n r b)) s₁ t₁' s₁' := by
        rw [Code.viaRegAt, ite_eq_right hm] at e₁; exact e₁
      have e₂' : Exec isa (.call m (Code.viaRegAt n r b)) s₂ t₂' s₂' := by
        rw [Code.viaRegAt, ite_eq_right hm] at e₂; exact e₂
      cases e₁' with
      | call hc₁ fb₁ hr₁ =>
      cases e₂' with
      | call hc₂ fb₂ hr₂ =>
      rw [hc₁, Option.some.injEq] at hco₁
      rw [hc₂, Option.some.injEq] at hco₂
      subst hco₁ hco₂
      obtain rfl := Exec.ofReg_det hc hv fb₁ p₁ (RegAt.call hc₁ hv.1 hd₁)
      obtain rfl := Exec.ofReg_det hc hv fb₂ p₂ (RegAt.call hc₂ hv.1 hd₂)
      simp only [List.map_nil, List.nil_append, List.append_nil]
      exact Exec.ofReg₂ b hc hv fb₁ fb₂ (RegAt.call hc₁ hv.1 hd₁) (RegAt.call hc₂ hv.1 hd₂)
        (by rw [call_syms hc₁, call_syms hc₂]; exact hy) p₁ p₂ h
  | .frame i b j, hc, hv, s₁, s₂, s₁', s₂', t₁', t₂', t₁, t₂, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree] at hc
    have hvb : KeepsReg r b := hv.frame
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
    obtain rfl := Exec.ofReg_det hc hvb fb₁ p₁ (RegAt.push hp₁ hd₁)
    obtain rfl := Exec.ofReg_det hc hvb fb₂ p₂ (RegAt.push hp₂ hd₂)
    simp only [List.append_assoc] at h ⊢
    have hA := List.append_inj h (by simp only [List.length_map]; exact addrs_length _ _ _)
    have hT := Exec.prefix hc p₁ p₂ hA.2
    rw [hT] at hA
    rw [hA.1, Exec.ofReg₂ b hc hvb fb₁ fb₂ (RegAt.push hp₁ hd₁) (RegAt.push hp₂ hd₂)
      (by rw [push_syms hp₁, push_syms hp₂]; exact hy) p₁ p₂ hT, List.append_cancel_left hA.2]
  | .icall .., hc, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp only [Code.icallFree, Bool.false_eq_true] at hc

/-- What runs of `c` from states where `k.pre` holds reach, runs of `c` made
to call `n` by `r` reach, from states where `r` also holds `n`'s address. -/
theorem Exec.viaRegAt_ok {n : String} {r : Reg} {c : Prog isa} {k : Contract isa}
    (h : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s') (hv : KeepsReg r c) :
    ∀ s, (Contract.reg n r k).pre s →
      ∃ t s', Exec isa (Code.viaRegAt n r c) s t s' ∧ abiPreserved s s' ∧ (Contract.reg n r k).post s s' :=
  fun s ⟨hp, hd⟩ => by
    obtain ⟨_, s', e, ha, hq⟩ := h s hp
    obtain ⟨t', e'⟩ := Exec.toReg e hv hd
    exact ⟨t', s', e', ha, hq⟩

/-- Code that leaks the same from states that `k` relates, made to call `n`
by `r`, leaks the same from states that `Contract.reg n r k` relates. -/
theorem ConstantTime.viaRegAt {n : String} {r : Reg} {c : Prog isa} {k : Contract isa}
    (h : ConstantTime isa k.pre k.pub c) (hc : Code.icallFree c = true) (hv : KeepsReg r c) :
    ConstantTime isa (Contract.reg n r k).pre (Contract.reg n r k).pub (Code.viaRegAt n r c) :=
  fun s₁ s₂ _ _ _ _ ⟨hp₁, hd₁⟩ ⟨hp₂, hd₂⟩ ⟨hpub, hy⟩ e₁ e₂ => by
    obtain ⟨t₁, o₁⟩ := Exec.ofReg₁ c hc hv e₁ hd₁
    obtain ⟨t₂, o₂⟩ := Exec.ofReg₁ c hc hv e₂ hd₂
    exact Exec.ofReg₂ c hc hv e₁ e₂ hd₁ hd₂ hy o₁ o₂ (h _ _ _ _ _ _ hp₁ hp₂ hpub o₁ o₂)

/-- **Code verified against `k` that writes no `r` and calls no function
by its address is verified made to call `n` by the address in `r`**, against
`k` from states where `r` holds `n`'s address, for runs that agree on it. -/
theorem Verified.viaRegAt {n : String} {r : Reg} {c : Prog isa} {k : Contract isa}
    (h : Verified target c k) (hc : Code.icallFree c = true)
    (hv : KeepsReg r c) (hsat : ∃ s, (Contract.reg n r k).pre s) :
    Verified target (Code.viaRegAt n r c) (Contract.reg n r k) :=
  ⟨Exec.viaRegAt_ok h.1 hv, ConstantTime.viaRegAt h.2.1 hc hv, hsat⟩

/-- Code made to call a function by its address has the frames it had. -/
theorem noFrames_viaRegAt (n : String) (r : Reg) (c : Prog isa) :
    (Code.viaRegAt n r c).noFrames = c.noFrames := by
  induction c with
  | call m b ih =>
    simp only [Code.viaRegAt]
    split
    · simp only [callReg, Code.icalls, Code.noFrames, ih, Bool.and_true]
    · simp only [Code.noFrames, ih]
  | _ => simp only [Code.viaRegAt, Code.noFrames, *]

end VG.Proof.Arm
