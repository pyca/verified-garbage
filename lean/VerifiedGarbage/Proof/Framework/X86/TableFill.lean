module

public import VerifiedGarbage.Proof.Framework.FillCode
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Impl.ICall
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The cleanup of code that calls implementations through tables (x86, 32-bit)

A function that calls through a table has in its code, at each indirect call,
the code of each implementation the table may hold (`Code.icalls`). What its
cleanup needs of that code (`scrubFSide`), as
`Proof/Framework/X86_64/TableFill.lean` on x86-64, comes from what is
evaluated once of the function's code over a stub (`tableStub m`, `stubSide`)
and of each implementation's (`calleeSide _ m`): `TFill` says the code is
that of the stub with the implementations in its place (`tfill_calls`), and
`TFill.ok` gives it.
-/

@[expose] public section

namespace VG.X86.Scrub

open VG.X86

/-- A stub of an implementation that uses at most `m` bytes of stack. -/
def tableStub (m : Nat) : Prog isa := .frame (.alloc m) (.block []) (.free m)

/-- `scrubFSide` of code over stubs, whose calls through the tables are of
"t". Only the kernel evaluates it. -/
noncomputable def stubSide (a : Prog isa) (W : Nat) : Bool :=
  Nat.ble (stackK a) W && CodeWalk.sideAll (fun i => !i.isMmxK) ["t"] a && decide (0 < W) && W % 4 == 0

theorem of_stubSide {a : Prog isa} {W : Nat} (h : stubSide a W = true) :
    stackUse a ≤ W ∧ a.allInstrs (fun i => !i.isMmx) = true ∧ 0 < W ∧ W % 4 = 0 := by
  simp only [stubSide, Bool.and_eq_true, Nat.ble_eq, stackK_eq, CodeWalk.sideAll_iff, Instr.isMmxK_fn,
    decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2.1, h.1.2, h.2⟩

theorem calleeSide_parts {c : Prog isa} {m : Nat} (h : calleeSide c m = true) :
    stackUse c ≤ m ∧ c.allInstrs (fun i => !i.isMmx) = true ∧ inames c = [] := by
  rw [calleeSide_iff, calleeOk_iff] at h
  exact ⟨h.1, h.2.2, inames_of_noIcall h.2.1⟩

theorem inames_of_namesIn {c : Prog isa} (h : CodeWalk.namesIn [] c = true) : inames c = [] := by
  rw [← inames_walk]
  exact List.eq_nil_iff_forall_not_mem.mpr fun f hf => nomatch CodeWalk.namesIn_iff.mp h f hf

/-- `b` is `a` with each indirect call of a stub (`Code.icalls i
[("t", tableStub m)]`) replaced by indirect calls by the same instruction of
implementations that meet `calleeSide _ m`, `m` the stub's, of names in `N`; the rest is
`a`'s, but for code that calls nothing indirectly, which both share
(`same`). -/
inductive TFill (N : List String) : Prog isa → Prog isa → Prop
  | block (is : List Instr) : TFill N (.block is) (.block is)
  | same (a : Prog isa) : inames a = [] → TFill N a a
  | tab {m : Nat} (i : Instr) (ts : List (String × Prog isa)) : (∀ q ∈ ts, calleeSide q.2 m = true ∧ q.1 ∈ N) →
      TFill N (Code.icalls i [("t", tableStub m)]) (Code.icalls i ts)
  | seq {a b a' b' : Prog isa} : TFill N a a' → TFill N b b' → TFill N (.seq a b) (.seq a' b')
  | ite {t e t' e' : Prog isa} (c : Cond) : TFill N t t' → TFill N e e' →
      TFill N (.ite c t e) (.ite c t' e')
  | loop {b b' : Prog isa} (c : Cond) : TFill N b b' → TFill N (.loop b c) (.loop b' c)
  | call {b b' : Prog isa} (f g : String) : TFill N b b' → TFill N (.call f b) (.call g b')
  | frame {b b' : Prog isa} (i j : Instr) : TFill N b b' → TFill N (.frame i b j) (.frame i b' j)

namespace TFill

variable {N : List String}

theorem icalls_stack {m : Nat} (i : Instr) : ∀ ts : List (String × Prog isa), (∀ q ∈ ts, calleeSide q.2 m = true) →
    stackUse (Code.icalls i ts) ≤ m + 4
  | [], _ => by simp [Code.icalls, stackUse]
  | q :: ts, h => by
    have h1 := (calleeSide_parts (h q (List.mem_cons_self ..))).1
    have h2 := icalls_stack i ts fun r hr => h r (List.mem_cons_of_mem _ hr)
    simp only [Code.icalls, stackUse]; omega_using [h1, h2]

/-- The stack `b` uses is at most `a`'s. -/
theorem stack_le {a b : Prog isa} (h : TFill N a b) : stackUse b ≤ stackUse a := by
  induction h with
  | block | same => exact Nat.le_refl _
  | @tab m i ts hts =>
    have := icalls_stack i ts fun q hq => (hts q hq).1
    simp only [Code.icalls, stackUse, tableStub, frameBytes]; omega_using [this]
  | seq _ _ iha ihb | ite _ _ _ iha ihb => simp only [stackUse]; omega_using [iha, ihb]
  | loop _ _ ih => simp only [stackUse]; exact ih
  | call _ _ _ ih | frame _ _ _ ih => simp only [stackUse]; omega_using [ih]

theorem icalls_all {m : Nat} (i : Instr) (hi : (!i.isMmx) = true) :
    ∀ ts : List (String × Prog isa), (∀ q ∈ ts, calleeSide q.2 m = true) →
      (Code.icalls i ts).allInstrs (fun i => !i.isMmx) = true
  | [], _ => rfl
  | q :: ts, h => by
    simp only [Code.icalls, Code.allInstrs, Bool.and_eq_true]
    exact ⟨⟨hi, (calleeSide_parts (h q (List.mem_cons_self ..))).2.1⟩,
      icalls_all i hi ts fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

/-- `b` has no MMX instruction if `a` has none. -/
theorem all {a b : Prog isa} (h : TFill N a b) (ha : a.allInstrs (fun i => !i.isMmx) = true) :
    b.allInstrs (fun i => !i.isMmx) = true := by
  induction h with
  | block | same => exact ha
  | @tab m i ts hts =>
    simp only [Code.icalls, Code.allInstrs, Bool.and_eq_true] at ha
    exact icalls_all i ha.1.1 ts fun q hq => (hts q hq).1
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨iha ha.1, ihb ha.2⟩
  | loop _ _ ih | call _ _ _ ih => simp only [Code.allInstrs] at ha ⊢; exact ih ha
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ih ha.1.2⟩, ha.2⟩

theorem icalls_inames {m : Nat} (i : Instr) : ∀ ts : List (String × Prog isa),
    (∀ q ∈ ts, calleeSide q.2 m = true ∧ q.1 ∈ N) → ∀ f ∈ X86.inames (Code.icalls i ts), f ∈ N
  | [], _ => by simp [Code.icalls, X86.inames]
  | q :: ts, h => by
    intro f hf
    simp only [Code.icalls, X86.inames, List.mem_cons, List.mem_append] at hf
    rcases hf with (rfl | hf) | hf
    · exact (h q (List.mem_cons_self ..)).2
    · rw [(calleeSide_parts (h q (List.mem_cons_self ..)).1).2.2] at hf; simp at hf
    · exact icalls_inames i ts (fun r hr => h r (List.mem_cons_of_mem _ hr)) f hf

/-- Every function `b` calls indirectly has a name of `N`. -/
theorem names {a b : Prog isa} (h : TFill N a b) : ∀ f ∈ X86.inames b, f ∈ N := by
  induction h with
  | block => simp [X86.inames]
  | same _ he => simp [he]
  | @tab m i ts hts => exact icalls_inames i ts hts
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    intro f hf; simp only [X86.inames, List.mem_append] at hf
    exact hf.elim (iha f) (ihb f)
  | loop _ _ ih | call _ _ _ ih | frame _ _ _ ih => intro f hf; simp only [X86.inames] at hf; exact ih f hf

/-- `TFill` into code that both sides choose by the same condition. -/
theorem ifp {p : Prop} [Decidable p] {a a' x y : Prog isa} (h : TFill N a x) (h' : TFill N a' y) :
    TFill N (if p then a else a') (if p then x else y) := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left hp]; exact h
  · rw [ite_eq_right hp, ite_eq_right hp]; exact h'

/-- What the cleanup of `b` needs, from what is evaluated of its code over
stubs, `a`, given that the names `N` of the implementations are those of the
tables `ts`. -/
theorem ok {a b : Prog isa} {ts : List (String × List FnTable)} {W : Nat} (h : TFill N a b)
    (hN : ∀ f ∈ N, f ∈ tableFns ts) (ha : stubSide a W = true) : scrubFSide b ts W = true := by
  obtain ⟨hs, hm, hp, h4⟩ := of_stubSide ha
  exact scrubFSide_iff.mpr ⟨Nat.le_trans h.stack_le hs,
    List.all_eq_true.mpr fun f hf => decide_eq_true (hN f (h.names f hf)), h.all hm, hp, h4⟩

end TFill

/-- Proves `TFill N a b` of a function's code over stubs (`a`) and over
implementations (`b`), from hypotheses of each list of implementations
(`∀ q ∈ ts, calleeSide q.2 m = true ∧ q.1 ∈ N`) and of the code that calls
nothing indirectly (`inames c = []`): it walks the function's code, unfolding
its definitions. -/
macro "tfill_calls" : tactic => `(tactic| fill_code)

end VG.X86.Scrub
