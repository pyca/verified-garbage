module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubUpFn
public import VerifiedGarbage.Impl.ICall

/-!
# The cleanup of a function generic over the tables of functions it takes (x86-64)

A function that calls the functions of a table of functions indirectly has
code with the code of every implementation the table may hold
(`Code.icalls`), of every variant of its interface: its facts are not a
closed term, and each implementation is evaluated where it is defined, never
in its callers. `TFill m N a b` says that `b` is the code `a` with each of
its indirect calls of a stub (`Code.icalls i [("t", tableStub m)]`) replaced
by indirect calls of implementations each of which meets `upCallee _ m` and
has a name of `N`. A function proves it once of every implementation, by
`tfill_calls` (which walks the function's code, not the implementations'),
and `verifiedScrubbedAllUpFill` gives `VerifiedScrubbed` of `scrubAll .sse`
of `b` (`verifiedScrubbedAllUp`) from `stubUp` of `a`, which the kernel
evaluates once.
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64 VG.Impl.Scrub.X86_64

/-- What the cleanup of a function that calls `c` through a table at the
level `sse` needs of it (`verifiedScrubbedAllUp`): at most `m` bytes of
stack, instructions below the level `evex`, upper halves that agree after it
if they did before, and no indirect call. Only the kernel evaluates it. -/
noncomputable def upCallee (c : Prog isa) (m : Nat) : Bool :=
  decide (c.x86_64Depth ≤ m) && c.allInstrs (fun i => decide (i.vecLevel ≤ 1)) &&
    UpperLock.up c true && (UpperLock.inames c).isEmpty

/-- A stub of an implementation that needs `m` bytes of stack. -/
def tableStub (m : Nat) : Prog isa := .frame (.alloc m) (.block []) (.free m)

/-- `UpperLock.stepI` along `is` from `a`, each step's answer evaluated
before the next (`UpperLock.up`'s `foldl` leaves the kernel a chain of them,
as deep as the block is long). -/
def stepsF : Bool → List Instr → Bool
  | a, [] => a
  | a, i :: is => match UpperLock.stepI a i with
    | true => stepsF true is
    | false => stepsF false is

/-- `UpperLock.up`, each answer evaluated before the code after it is
followed (`stepsF`), which the kernel evaluates on long code. -/
def upF : Prog isa → Bool → Bool
  | .block is, a => stepsF a is
  | .seq x y, a => match upF x a with
    | true => upF y true
    | false => upF y false
  | .ite _ t e, a => upF t a && upF e a
  | .loop b _, a => upF b a
  | .call _ b, a => upF b a
  | .frame _ b _, a => upF b a
  | .icall _ _ b n, a => upF b a && upF n a

theorem stepsF_eq : ∀ (a : Bool) (is : List Instr), stepsF a is = is.foldl UpperLock.stepI a
  | a, [] => rfl
  | a, i :: is => by
    simp only [stepsF, List.foldl]
    cases h : UpperLock.stepI a i <;> exact stepsF_eq _ is

theorem upF_eq : ∀ (c : Prog isa) (a : Bool), upF c a = UpperLock.up c a
  | .block is, a => stepsF_eq a is
  | .seq x y, a => by
    simp only [upF, UpperLock.up, ← upF_eq x a]
    cases upF x a <;> exact upF_eq y _
  | .ite _ t e, a => by simp only [upF, UpperLock.up, upF_eq t a, upF_eq e a]
  | .loop b _, a | .call _ b, a | .frame _ b _, a => by simp only [upF, UpperLock.up, upF_eq b a]
  | .icall _ _ b n, a => by simp only [upF, UpperLock.up, upF_eq b a, upF_eq n a]

/-- What `verifiedScrubbedAllUp` needs of a function's code `a` with stubs
in the place of its tables' implementations, which need at most `m` bytes of
stack (`tableStub`): its stack at most `stack`, instructions below the level
`evex` and upper halves that agree after it if they did before (`upF`). -/
noncomputable def stubUp (a : Prog isa) (stack : Nat) : Bool :=
  decide (a.x86_64Depth ≤ stack) && a.allInstrs (fun i => decide (i.vecLevel ≤ 1)) && upF a true

/-- `b` is `a` with each indirect call of a stub (`Code.icalls i
[("t", tableStub m)]`) replaced by indirect calls by the same instruction of
implementations that meet `upCallee _ m`, of names in `N`; the rest is
`a`'s, but for code that calls nothing indirectly, which both share
(`same`). -/
inductive TFill (m : Nat) (N : List String) : Prog isa → Prog isa → Prop
  | block (is : List Instr) : TFill m N (.block is) (.block is)
  | same (a : Prog isa) : UpperLock.inames a = [] → TFill m N a a
  | tab (i : Instr) (ts : List (String × Prog isa)) : (∀ q ∈ ts, upCallee q.2 m = true ∧ q.1 ∈ N) →
      TFill m N (Code.icalls i [("t", tableStub m)]) (Code.icalls i ts)
  | seq {a b a' b' : Prog isa} : TFill m N a a' → TFill m N b b' → TFill m N (.seq a b) (.seq a' b')
  | ite {t e t' e' : Prog isa} (c : Cond) : TFill m N t t' → TFill m N e e' →
      TFill m N (.ite c t e) (.ite c t' e')
  | loop {b b' : Prog isa} (c : Cond) : TFill m N b b' → TFill m N (.loop b c) (.loop b' c)
  | call {b b' : Prog isa} (f g : String) : TFill m N b b' → TFill m N (.call f b) (.call g b')
  | frame {b b' : Prog isa} (i j : Instr) : TFill m N b b' → TFill m N (.frame i b j) (.frame i b' j)

namespace TFill

variable {m : Nat} {N : List String}

theorem upCallee_parts {c : Prog isa} (h : upCallee c m = true) :
    c.x86_64Depth ≤ m ∧ c.allInstrs (fun i => decide (i.vecLevel ≤ 1)) = true ∧
      UpperLock.up c true = true ∧ UpperLock.inames c = [] := by
  simp only [upCallee, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem icalls_depth (i : Instr) : ∀ ts : List (String × Prog isa), (∀ q ∈ ts, upCallee q.2 m = true) →
    (Code.icalls i ts).x86_64Depth ≤ m + 8
  | [], _ => by simp [Code.icalls, Code.x86_64Depth]
  | q :: ts, h => by
    have h1 := (upCallee_parts (h q (List.mem_cons_self ..))).1
    have h2 := icalls_depth i ts fun r hr => h r (List.mem_cons_of_mem _ hr)
    simp only [Code.icalls, Code.x86_64Depth]; omega

/-- The stack `b` uses is at most `a`'s. -/
theorem depth_le {a b : Prog isa} (h : TFill m N a b) : b.x86_64Depth ≤ a.x86_64Depth := by
  induction h with
  | block | same => exact Nat.le_refl _
  | tab i ts hts =>
    have := icalls_depth (m := m) i ts fun q hq => (hts q hq).1
    simp only [Code.icalls, Code.x86_64Depth, tableStub, X86_64.Instr.frameBytes]; omega
  | seq _ _ iha ihb | ite _ _ _ iha ihb => simp only [Code.x86_64Depth]; omega
  | loop _ _ ih => simp only [Code.x86_64Depth]; exact ih
  | call _ _ _ ih | frame _ _ _ ih => simp only [Code.x86_64Depth]; omega

theorem icalls_all (i : Instr) {p : Instr → Bool} (hi : p i = true)
    (hp : ∀ c : Prog isa, upCallee c m = true → c.allInstrs p = true) :
    ∀ ts : List (String × Prog isa), (∀ q ∈ ts, upCallee q.2 m = true) → (Code.icalls i ts).allInstrs p = true
  | [], _ => rfl
  | q :: ts, h => by
    simp only [Code.icalls, Code.allInstrs, Bool.and_eq_true]
    exact ⟨⟨hi, hp _ (h q (List.mem_cons_self ..))⟩, icalls_all i hi hp ts fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

/-- What every instruction of `a` and of the implementations meets, every
instruction of `b` does. -/
theorem all {a b : Prog isa} (h : TFill m N a b) {p : Instr → Bool}
    (hp : ∀ c : Prog isa, upCallee c m = true → c.allInstrs p = true) (ha : a.allInstrs p = true) :
    b.allInstrs p = true := by
  induction h with
  | block | same => exact ha
  | tab i ts hts =>
    simp only [Code.icalls, Code.allInstrs, Bool.and_eq_true] at ha
    exact icalls_all i ha.1.1 hp ts fun q hq => (hts q hq).1
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨iha ha.1, ihb ha.2⟩
  | loop _ _ ih | call _ _ _ ih => simp only [Code.allInstrs] at ha ⊢; exact ih ha
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ih ha.1.2⟩, ha.2⟩

theorem icalls_up (i : Instr) : ∀ ts : List (String × Prog isa), (∀ q ∈ ts, upCallee q.2 m = true) →
    UpperLock.up (Code.icalls i ts) true = true
  | [], _ => rfl
  | q :: ts, h => by
    simp only [Code.icalls, UpperLock.up, Bool.and_eq_true]
    exact ⟨(upCallee_parts (h q (List.mem_cons_self ..))).2.2.1,
      icalls_up i ts fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

/-- If the upper halves agree after `a`, they do after `b`. -/
theorem up {a b : Prog isa} (h : TFill m N a b) : ∀ s, UpperLock.up a s = true → UpperLock.up b s = true := by
  induction h with
  | block | same => exact fun _ h => h
  | tab i ts hts =>
    intro s hs
    simp only [Code.icalls, UpperLock.up, List.foldl, Bool.and_eq_true] at hs
    rw [hs.2]
    exact icalls_up i ts fun q hq => (hts q hq).1
  | @seq x y x' y' _ _ ihx ihy =>
    intro s hs
    simp only [UpperLock.up] at hs ⊢
    cases hx : UpperLock.up x s
    · rw [hx] at hs
      exact UpperLock.up_mono y' (a := false) (a' := UpperLock.up x' s) (fun h => absurd h (by decide))
        (ihy false hs)
    · rw [hx] at hs
      rw [ihx s hx]; exact ihy true hs
  | ite _ _ _ iht ihe =>
    intro s hs
    simp only [UpperLock.up, Bool.and_eq_true] at hs ⊢; exact ⟨iht s hs.1, ihe s hs.2⟩
  | loop _ _ ih | call _ _ _ ih | frame _ _ _ ih => intro s hs; simp only [UpperLock.up] at hs ⊢; exact ih s hs

theorem icalls_inames (i : Instr) : ∀ ts : List (String × Prog isa), (∀ q ∈ ts, upCallee q.2 m = true ∧ q.1 ∈ N) →
    ∀ f ∈ UpperLock.inames (Code.icalls i ts), f ∈ N
  | [], _ => by simp [Code.icalls, UpperLock.inames]
  | q :: ts, h => by
    intro f hf
    simp only [Code.icalls, UpperLock.inames, List.mem_cons, List.mem_append] at hf
    rcases hf with (rfl | hf) | hf
    · exact (h q (List.mem_cons_self ..)).2
    · rw [(upCallee_parts (h q (List.mem_cons_self ..)).1).2.2.2] at hf; simp at hf
    · exact icalls_inames i ts (fun r hr => h r (List.mem_cons_of_mem _ hr)) f hf

/-- Every function `b` calls indirectly has a name of `N`. -/
theorem inames {a b : Prog isa} (h : TFill m N a b) : ∀ f ∈ UpperLock.inames b, f ∈ N := by
  induction h with
  | block => simp [UpperLock.inames]
  | same _ he => simp [he]
  | tab i ts hts => exact icalls_inames i ts hts
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    intro f hf; simp only [UpperLock.inames, List.mem_append] at hf
    exact hf.elim (iha f) (ihb f)
  | loop _ _ ih | call _ _ _ ih | frame _ _ _ ih => intro f hf; simp only [UpperLock.inames] at hf; exact ih f hf

/-- `TFill` into code that both sides choose by the same condition. -/
theorem ifp {p : Prop} [Decidable p] {a a' x y : Prog isa} (h : TFill m N a x) (h' : TFill m N a' y) :
    TFill m N (if p then a else a') (if p then x else y) := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left hp]; exact h
  · rw [ite_eq_right hp, ite_eq_right hp]; exact h'

end TFill

/-- `r`'s code `b`, generic over the implementations of the tables it takes
(`TFill m N a b`), followed by `scrubAll .sse rb stack`, meets `r`'s
contract in constant time and returns without secret residue: from `stubUp`
of its code with stubs (`a`), which the kernel evaluates once, and what each
implementation proves of its own code where it is defined (in `hf`), given
that the names `N` of the implementations are its tables' functions'. -/
theorem verifiedScrubbedAllUpFill {api : Api} (r : Unscrubbed api target) {a : Prog isa} {m : Nat}
    {N : List String} {stack rb : Nat}
    (hpost : PostOut r.contract (retBitsOf r)) (hf : TFill m N a r.code)
    (hN : ∀ f ∈ N, f ∈ tableFns r.tables)
    (hn : r.stack = stack := by rfl) (hb : retBitsOf r = rb := by rfl)
    (ha : stubUp a stack = true := by lit_decide)
    (hl : litSide stack rb = true := by decide) :
    VerifiedScrubbed target (scrubAll .sse rb stack r.code) r.contract rb := by
  subst hn hb
  simp only [stubUp, Bool.and_eq_true, decide_eq_true_eq] at ha
  obtain ⟨⟨hd, hl1⟩, hup⟩ := ha
  rw [upF_eq] at hup
  have hic : tablesCall r.code r.tables = true := by
    unfold tablesCall
    exact List.all_eq_true.mpr fun f hf' => decide_eq_true (hN f (hf.inames f hf'))
  exact verifiedScrubbedAllUp r hpost (Nat.le_trans hf.depth_le hd)
    (hf.all (fun c h => (TFill.upCallee_parts h).2.1) hl1) (hf.up true hup) hic hl

/-- Proves `TFill m N a b` of a function's code with stubs (`a`) and with
implementations (`b`), from hypotheses of each list of implementations
(`∀ q ∈ ts, upCallee q.2 m = true ∧ q.1 ∈ N`) and of the code that calls
nothing indirectly (`UpperLock.inames c = []`): it walks the function's
code, unfolding its definitions. -/
macro "tfill_calls" : tactic => `(tactic| repeat' (first
  | exact TFill.block _
  | exact TFill.tab _ _ (by assumption)
  | exact TFill.same _ (by assumption)
  | refine TFill.seq ?_ ?_
  | refine TFill.ite _ ?_ ?_
  | refine TFill.loop _ ?_
  | refine TFill.call _ _ ?_
  | refine TFill.frame _ _ ?_
  | refine TFill.ifp ?_ ?_))

end VG.X86_64.Scrub
