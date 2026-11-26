module

public import VerifiedGarbage.Proof.Framework.AArch64.SideFillT
public import VerifiedGarbage.Proof.Framework.FillCode
public import VerifiedGarbage.Impl.ICall

/-!
# The cleanup of code that calls implementations through tables (AArch64)

A function that calls through a table has in its code, at each indirect call,
the code of each implementation the table may hold (`Code.icalls`). What its
cleanup needs of that code, as `Proof/Framework/X86_64/TableFill.lean` on
x86-64, comes from what is evaluated once of the function's code over a stub
(`tableStub m`) and of each implementation's (`tabCallee _ m`): `TFill` says
the code is that of the stub with the implementations in its place
(`tfill_calls`), and `TFill.ok` gives it.
-/

@[expose] public section

namespace VG.AArch64.Scrub

open VG.AArch64 VG.Impl.Scrub.AArch64

/-- What the cleanup of a function that calls `c` through a table needs of
it: no write of PSTATE.DIT, no indirect call, and frames at most `16 m` bytes
deep. Only the kernel evaluates it. -/
noncomputable def tabCallee (c : Prog isa) (m : Nat) : Bool :=
  sideAll (fun i => !i.writesDit) c && Nat.ble c.aarch64Depth m

/-- A stub of an implementation whose frames are at most `16 m` bytes deep. -/
def tableStub (m : Nat) : Prog isa := .frame (.alloc (16 * m)) (.block []) (.free (16 * m))

theorem tabCallee_parts {c : Prog isa} {m : Nat} (h : tabCallee c m = true) :
    c.allInstrs (fun i => !i.writesDit) = true ∧ inames c = [] ∧ c.aarch64Depth ≤ m := by
  simp only [tabCallee, Bool.and_eq_true] at h
  exact ⟨allInstrs_of_sideAll h.1, inames_of_noIcall (noIcall_of_sideAll h.1), Nat.le_of_ble_eq_true h.2⟩

/-- `b` is `a` with each indirect call of a stub (`Code.icalls i
[("t", tableStub m)]`) replaced by indirect calls by the same instruction of
implementations that meet `tabCallee _ m`, of names in `N`; the rest is
`a`'s, but for code that calls nothing indirectly, which both share
(`same`). -/
inductive TFill (m : Nat) (N : List String) : Prog isa → Prog isa → Prop
  | block (is : List Instr) : TFill m N (.block is) (.block is)
  | same (a : Prog isa) : inames a = [] → TFill m N a a
  | tab (i : Instr) (ts : List (String × Prog isa)) : (∀ q ∈ ts, tabCallee q.2 m = true ∧ q.1 ∈ N) →
      TFill m N (Code.icalls i [("t", tableStub m)]) (Code.icalls i ts)
  | seq {a b a' b' : Prog isa} : TFill m N a a' → TFill m N b b' → TFill m N (.seq a b) (.seq a' b')
  | ite {t e t' e' : Prog isa} (c : Cond) : TFill m N t t' → TFill m N e e' →
      TFill m N (.ite c t e) (.ite c t' e')
  | loop {b b' : Prog isa} (c : Cond) : TFill m N b b' → TFill m N (.loop b c) (.loop b' c)
  | call {b b' : Prog isa} (f g : String) : TFill m N b b' → TFill m N (.call f b) (.call g b')
  | frame {b b' : Prog isa} (i j : Instr) : TFill m N b b' → TFill m N (.frame i b j) (.frame i b' j)

namespace TFill

variable {m : Nat} {N : List String}

theorem icalls_depth (i : Instr) : ∀ ts : List (String × Prog isa), (∀ q ∈ ts, tabCallee q.2 m = true) →
    (Code.icalls i ts).aarch64Depth ≤ m
  | [], _ => by simp [Code.icalls, Code.aarch64Depth]
  | q :: ts, h => by
    have h1 := (tabCallee_parts (h q (List.mem_cons_self ..))).2.2
    have h2 := icalls_depth i ts fun r hr => h r (List.mem_cons_of_mem _ hr)
    simp only [Code.icalls, Code.aarch64Depth]; omega

/-- The stack `b` uses is at most `a`'s. -/
theorem depth_le {a b : Prog isa} (h : TFill m N a b) : b.aarch64Depth ≤ a.aarch64Depth := by
  induction h with
  | block | same => exact Nat.le_refl _
  | tab i ts hts =>
    have := icalls_depth (m := m) i ts fun q hq => (hts q hq).1
    simp only [Code.icalls, Code.aarch64Depth, tableStub, AArch64.Instr.frameUnits]; omega
  | seq _ _ iha ihb | ite _ _ _ iha ihb => simp only [Code.aarch64Depth]; omega
  | loop _ _ ih | call _ _ _ ih => simp only [Code.aarch64Depth]; exact ih
  | frame _ _ _ ih => simp only [Code.aarch64Depth]; omega

theorem icalls_all (i : Instr) (hi : (!i.writesDit) = true) :
    ∀ ts : List (String × Prog isa), (∀ q ∈ ts, tabCallee q.2 m = true) →
      (Code.icalls i ts).allInstrs (fun i => !i.writesDit) = true
  | [], _ => rfl
  | q :: ts, h => by
    simp only [Code.icalls, Code.allInstrs, Bool.and_eq_true]
    exact ⟨⟨hi, (tabCallee_parts (h q (List.mem_cons_self ..))).1⟩,
      icalls_all i hi ts fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

/-- `b` writes PSTATE.DIT nowhere if `a` does not. -/
theorem all {a b : Prog isa} (h : TFill m N a b) (ha : a.allInstrs (fun i => !i.writesDit) = true) :
    b.allInstrs (fun i => !i.writesDit) = true := by
  induction h with
  | block | same => exact ha
  | tab i ts hts =>
    simp only [Code.icalls, Code.allInstrs, Bool.and_eq_true] at ha
    exact icalls_all i ha.1.1 ts fun q hq => (hts q hq).1
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨iha ha.1, ihb ha.2⟩
  | loop _ _ ih | call _ _ _ ih => simp only [Code.allInstrs] at ha ⊢; exact ih ha
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ih ha.1.2⟩, ha.2⟩

theorem icalls_inames (i : Instr) : ∀ ts : List (String × Prog isa),
    (∀ q ∈ ts, tabCallee q.2 m = true ∧ q.1 ∈ N) → ∀ f ∈ Scrub.inames (Code.icalls i ts), f ∈ N
  | [], _ => by simp [Code.icalls, Scrub.inames]
  | q :: ts, h => by
    intro f hf
    simp only [Code.icalls, Scrub.inames, List.mem_cons, List.mem_append] at hf
    rcases hf with (rfl | hf) | hf
    · exact (h q (List.mem_cons_self ..)).2
    · rw [(tabCallee_parts (h q (List.mem_cons_self ..)).1).2.1] at hf; simp at hf
    · exact icalls_inames i ts (fun r hr => h r (List.mem_cons_of_mem _ hr)) f hf

/-- Every function `b` calls indirectly has a name of `N`. -/
theorem names {a b : Prog isa} (h : TFill m N a b) : ∀ f ∈ Scrub.inames b, f ∈ N := by
  induction h with
  | block => simp [Scrub.inames]
  | same _ he => simp [he]
  | tab i ts hts => exact icalls_inames i ts hts
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    intro f hf; simp only [Scrub.inames, List.mem_append] at hf
    exact hf.elim (iha f) (ihb f)
  | loop _ _ ih | call _ _ _ ih | frame _ _ _ ih => intro f hf; simp only [Scrub.inames] at hf; exact ih f hf

/-- `TFill` into code that both sides choose by the same condition. -/
theorem ifp {p : Prop} [Decidable p] {a a' x y : Prog isa} (h : TFill m N a x) (h' : TFill m N a' y) :
    TFill m N (if p then a else a') (if p then x else y) := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left hp]; exact h
  · rw [ite_eq_right hp, ite_eq_right hp]; exact h'

/-- What the cleanup of `b` needs (`verifiedScrubbedOfT`), from what is
evaluated of its code over stubs, `a`, given that the names `N` of the
implementations are those of the tables `ts`. -/
theorem ok {a b : Prog isa} {ts : List (String × List FnTable)} {d : Nat} (h : TFill m N a b)
    (hN : ∀ f ∈ N, f ∈ tableFns ts) (ha : a.allInstrs (fun i => !i.writesDit) = true) (hd : a.aarch64Depth ≤ d) :
    b.all (fun i => !i.writesDit) = true ∧ tablesCall b ts = true ∧ b.aarch64Depth ≤ d :=
  ⟨Code.all_of_allInstrs (h.all ha),
    List.all_eq_true.mpr fun f hf => decide_eq_true (hN f (h.names f hf)), Nat.le_trans h.depth_le hd⟩

end TFill

/-- `Code.allInstrs` of code with its holes filled, from the code's and the
fillings'. -/
theorem allInstrs_fill2 {p : Instr → Bool} {a b e : Prog isa} (ha : a.allInstrs p = true)
    (hb : b.allInstrs p = true) (he : e.allInstrs p = true) : (Code.fill2 a b e).allInstrs p = true := by
  induction e with
  | block is => exact he
  | seq x y ihx ihy | ite _ x y ihx ihy =>
    simp only [Code.fill2, Code.allInstrs, Bool.and_eq_true] at he ⊢
    exact ⟨ihx he.1, ihy he.2⟩
  | loop x cd ih => simp only [Code.fill2, Code.allInstrs] at he ⊢; exact ih he
  | call m body ih =>
    unfold Code.fill2
    split
    · exact ha
    · exact hb
    · simp only [Code.allInstrs] at he ⊢; exact ih he
  | frame i x j ih =>
    simp only [Code.fill2, Code.allInstrs, Bool.and_eq_true] at he ⊢
    exact ⟨⟨he.1.1, ih he.1.2⟩, he.2⟩
  | icall i m x y => exact he

/-- Proves `TFill m N a b` of a function's code over stubs (`a`) and over
implementations (`b`), from hypotheses of each list of implementations
(`∀ q ∈ ts, tabCallee q.2 m = true ∧ q.1 ∈ N`) and of the code that calls
nothing indirectly (`inames c = []`): it walks the function's code, unfolding
its definitions. -/
macro "tfill_calls" : tactic => `(tactic| fill_code)

end VG.AArch64.Scrub
