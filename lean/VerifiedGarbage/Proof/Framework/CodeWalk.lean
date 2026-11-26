module

public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# What a cleanup needs of code, as the kernel walks it

The cleanup of a function needs of its code, callees included, that its
instructions pass a test, that it calls indirectly only functions of some
tables, and that it uses at most some stack. The kernel evaluates these for
every function with a cleanup. The functions here are those checks, written
for it, whatever the target:

* each walks the code with `Code.rec`, not a structural recursion, which
  compiles to `brecOn`;
* the stack is computed with `Nat.sub` and `Nat.add`, whose arguments the
  kernel evaluates once: `max` gives one of its arguments back as a term,
  which the kernel evaluates again at every level of the code;
* a block, and the body of a callee, are terms the kernel is asked for
  (`ask`): it remembers the value of those, not of the terms it passes
  through, and so finds again code that is there twice.
-/

@[expose] public section

namespace VG.CodeWalk

variable {I C : Type}

/-- `b`, which the kernel evaluates as a term of its own. -/
noncomputable def ask (b : Bool) : Bool := Bool.rec false true b

theorem ask_eq (b : Bool) : ask b = b := by cases b <;> rfl

theorem rec_and (a b : Bool) : (Bool.rec false b a : Bool) = (a && b) := by cases a <;> rfl

/-- The functions `c` may call indirectly. -/
def inames : Code I C → List String
  | .block _ => []
  | .seq a b => inames a ++ inames b
  | .ite _ t e => inames t ++ inames e
  | .loop b _ => inames b
  | .call _ b => inames b
  | .frame _ b _ => inames b
  | .icall _ n b nx => n :: inames b ++ inames nx

/-- `c.allInstrs p`, of code that calls indirectly only functions of `N`. -/
noncomputable def sideAll (p : I → Bool) (N : List String) (c : Code I C) : Bool :=
  Code.rec (motive := fun _ => Bool) (fun is => ask (Code.allInstrs p (.block is : Code I C)))
    (fun _ _ a b => Bool.rec false b a) (fun _ _ _ t e => Bool.rec false e t) (fun _ _ b => b) (fun _ _ b => ask b)
    (fun i _ j b => Bool.rec false (Bool.rec false b (p j)) (p i))
    (fun i n _ _ b nx => Bool.rec false (Bool.rec false (Bool.rec false nx b) (p i)) (decide (n ∈ N))) c

theorem sideAll_eq (p : I → Bool) (N : List String) (c : Code I C) :
    sideAll p N c = (c.allInstrs p && (inames c).all fun f => decide (f ∈ N)) := by
  induction c with
  | block is =>
    rw [inames, List.all_nil, Bool.and_true]
    exact ask_eq _
  | seq a b iha ihb =>
    rw [show sideAll p N (.seq a b) = (sideAll p N a && sideAll p N b) from rec_and _ _, iha, ihb, Code.allInstrs,
      inames, List.all_append]
    ac_rfl
  | ite _ a b iha ihb =>
    rw [show sideAll p N (.ite _ a b) = (sideAll p N a && sideAll p N b) from rec_and _ _, iha, ihb, Code.allInstrs,
      inames, List.all_append]
    ac_rfl
  | loop b _ ih => exact ih
  | call _ b ih => exact (ask_eq _).trans ih
  | frame i b j ih =>
    rw [show sideAll p N (.frame i b j) = (p i && (p j && sideAll p N b)) from
      (rec_and _ _).trans (congrArg _ (rec_and _ _)), ih, Code.allInstrs, inames]
    ac_rfl
  | icall i n b nx ihb ihn =>
    rw [show sideAll p N (.icall i n b nx) = (decide (n ∈ N) && (p i && (sideAll p N b && sideAll p N nx))) from
      (rec_and _ _).trans (congrArg _ ((rec_and _ _).trans (congrArg _ (rec_and _ _)))), ihb, ihn, Code.allInstrs,
      inames, List.cons_append, List.all_cons, List.all_append]
    ac_rfl

theorem sideAll_iff {p : I → Bool} {N : List String} {c : Code I C} :
    sideAll p N c = true ↔ c.allInstrs p = true ∧ ∀ f ∈ inames c, f ∈ N := by
  rw [sideAll_eq, Bool.and_eq_true, List.all_eq_true]
  simp only [decide_eq_true_eq]

/-- `c` calls indirectly only functions of `N`. -/
noncomputable def namesIn (N : List String) (c : Code I C) : Bool :=
  Code.rec (motive := fun _ => Bool) (fun _ => true)
    (fun _ _ a b => Bool.rec false b a) (fun _ _ _ t e => Bool.rec false e t) (fun _ _ b => b) (fun _ _ b => ask b)
    (fun _ _ _ b => b) (fun _ n _ _ b nx => Bool.rec false (Bool.rec false nx b) (decide (n ∈ N))) c

theorem namesIn_eq (N : List String) (c : Code I C) : namesIn N c = (inames c).all fun f => decide (f ∈ N) := by
  induction c with
  | block => rfl
  | seq a b iha ihb =>
    rw [show namesIn N (.seq a b) = (namesIn N a && namesIn N b) from rec_and _ _, iha, ihb, inames, List.all_append]
  | ite _ a b iha ihb =>
    rw [show namesIn N (.ite _ a b) = (namesIn N a && namesIn N b) from rec_and _ _, iha, ihb, inames, List.all_append]
  | loop b _ ih => exact ih
  | call _ b ih => exact (ask_eq _).trans ih
  | frame _ b _ ih => exact ih
  | icall i n b nx ihb ihn =>
    rw [show namesIn N (.icall i n b nx) = (decide (n ∈ N) && (namesIn N b && namesIn N nx)) from
      (rec_and _ _).trans (congrArg _ (rec_and _ _)), ihb, ihn, inames, List.cons_append, List.all_cons,
      List.all_append]

theorem namesIn_iff {N : List String} {c : Code I C} : namesIn N c = true ↔ ∀ f ∈ inames c, f ∈ N := by
  rw [namesIn_eq, List.all_eq_true]
  simp only [decide_eq_true_eq]

/-- The most stack `c` uses at once, where a call takes `k` bytes of it and a
frame whose push is `i` takes `f i`. -/
noncomputable def depth (f : I → Nat) (k : Nat) (c : Code I C) : Nat :=
  Code.rec (motive := fun _ => Nat) (fun _ => 0) (fun _ _ a b => Nat.add (Nat.sub a b) b)
    (fun _ _ _ t e => Nat.add (Nat.sub t e) e) (fun _ _ b => b) (fun _ _ b => Nat.add b k)
    (fun i _ _ b => Nat.add b (f i)) (fun _ _ _ _ b nx => Nat.add (Nat.sub (Nat.add b k) nx) nx) c

theorem depth_block (f : I → Nat) (k : Nat) (is : List I) : depth f k (.block is : Code I C) = 0 := rfl

theorem depth_seq (f : I → Nat) (k : Nat) (a b : Code I C) : depth f k (.seq a b) = max (depth f k a) (depth f k b) :=
  Nat.sub_add_eq_max _ _

theorem depth_ite (f : I → Nat) (k : Nat) (c : C) (a b : Code I C) :
    depth f k (.ite c a b) = max (depth f k a) (depth f k b) := Nat.sub_add_eq_max _ _

theorem depth_loop (f : I → Nat) (k : Nat) (b : Code I C) (c : C) : depth f k (.loop b c) = depth f k b := rfl

theorem depth_call (f : I → Nat) (k : Nat) (n : String) (b : Code I C) : depth f k (.call n b) = depth f k b + k := rfl

theorem depth_frame (f : I → Nat) (k : Nat) (i j : I) (b : Code I C) :
    depth f k (.frame i b j) = depth f k b + f i := rfl

theorem depth_icall (f : I → Nat) (k : Nat) (i : I) (n : String) (b nx : Code I C) :
    depth f k (.icall i n b nx) = max (depth f k b + k) (depth f k nx) := Nat.sub_add_eq_max _ _

end VG.CodeWalk
