module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Weave

/-!
# Interleaving independent code, for any ISA

Untrusted: everything here is checked by Lean. Two instructions *commute*
(`Commute`) when running them in either order faults alike or ends in the
same state. Any interleaving (`Merge`) of two blocks whose instructions
commute pairwise runs as the first block and then the second (`run_merge`,
`WP.merge`, `WP.weave`).

An ISA shows instructions commute through their *footprints*
(`Footprints`): what each instruction of a class may read and write, as
data with a union and a Boolean independence check. Two blocks whose
footprints' unions are independent commute pairwise (`indeps_of_check`), so
a proof checks independence by evaluating the blocks' footprints once
(`decide`), not instruction by instruction. The footprints of
`Framework/<ISA>/Interleave.lean` are bit masks of registers and bytes,
which the kernel evaluates as `Nat`s.
-/

@[expose] public section

namespace VG.Interleave

open VG

variable {M : ISA}

/-! ## Interleavings -/

/-- `c` interleaves `a` and `b`. -/
inductive Merge {α : Type} : List α → List α → List α → Prop
  | nil : Merge [] [] []
  | left {x : α} {c a b : List α} : Merge c a b → Merge (x :: c) (x :: a) b
  | right {y : α} {c a b : List α} : Merge c a b → Merge (y :: c) a (y :: b)

theorem Merge.nil_left {α : Type} : ∀ b : List α, Merge b [] b
  | [] => .nil
  | _ :: b => .right (Merge.nil_left b)

theorem Merge.nil_right {α : Type} : ∀ a : List α, Merge a a []
  | [] => .nil
  | _ :: a => .left (Merge.nil_right a)

theorem Merge.append {α : Type} (a b : List α) : Merge (a ++ b) a b := by
  induction a with
  | nil => exact Merge.nil_left b
  | cons x a ih => exact .left ih

open VG.Impl.Weave (weave weaveGo) in
theorem weaveGo_merge {α : Type} (n m : Nat) : ∀ f i j (a b : List α), Merge (weaveGo n m f i j a b) a b
  | 0, _, _, a, b => Merge.append a b
  | _ + 1, _, _, [], b => Merge.nil_left b
  | _ + 1, _, _, x :: a, [] => Merge.nil_right (x :: a)
  | f + 1, i, j, x :: a, y :: b => by
    rw [weaveGo]
    split
    · exact .left (weaveGo_merge n m f _ _ _ _)
    · exact .right (weaveGo_merge n m f _ _ _ _)

theorem weave_merge {α : Type} (a b : List α) : Merge (VG.Impl.Weave.weave a b) a b :=
  weaveGo_merge _ _ _ _ _ _ _

/-! ## Commuting instructions -/

/-- Running `x` then `y` faults alike, or ends in the same state, as `y` then `x`. -/
def Commute (M : ISA) (x y : M.Instr) : Prop :=
  ∀ s, (M.exec x s).bind (M.exec y) = (M.exec y s).bind (M.exec x)

theorem Commute.symm {x y : M.Instr} (h : Commute M x y) : Commute M y x := fun s => (h s).symm

/-- Every instruction of `a` commutes with every instruction of `b`. -/
def Indeps (M : ISA) (a b : List M.Instr) : Prop := ∀ x ∈ a, ∀ y ∈ b, Commute M x y

theorem comm_block {y : M.Instr} {a : List M.Instr} (ha : ∀ x ∈ a, Commute M x y) (s : M.State) :
    (M.exec y s).bind (runBlock M a) = (runBlock M a s).bind (M.exec y) := by
  induction a generalizing s with
  | nil =>
    show (M.exec y s).bind some = M.exec y s
    cases M.exec y s <;> rfl
  | cons x a ih =>
    show (M.exec y s).bind (fun u => (M.exec x u).bind (runBlock M a)) =
      ((M.exec x s).bind (runBlock M a)).bind (M.exec y)
    rw [← Option.bind_assoc, ((ha x List.mem_cons_self).symm s), Option.bind_assoc, Option.bind_assoc]
    congr 1
    funext u
    exact ih (fun x' hx' => ha x' (List.mem_cons_of_mem _ hx')) u

theorem runBlock_append (a b : List M.Instr) (s : M.State) :
    runBlock M (a ++ b) s = (runBlock M a s).bind (runBlock M b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    show (M.exec x s).bind (runBlock M (a ++ b)) = ((M.exec x s).bind (runBlock M a)).bind (runBlock M b)
    rw [Option.bind_assoc]
    congr 1
    funext u
    exact ih u

/-- An interleaving of blocks whose instructions commute runs as the first and then the second. -/
theorem run_merge {c a b : List M.Instr} (hm : Merge c a b) (hind : Indeps M a b) (s : M.State) :
    runBlock M c s = runBlock M (a ++ b) s := by
  induction hm generalizing s with
  | nil => rfl
  | @left x c a b _ ih =>
    show (M.exec x s).bind (runBlock M c) = (M.exec x s).bind (runBlock M (a ++ b))
    congr 1
    funext u
    exact ih (fun x' hx' y hy => hind x' (List.mem_cons_of_mem _ hx') y hy) u
  | @right y c a b _ ih =>
    show (M.exec y s).bind (runBlock M c) = runBlock M (a ++ y :: b) s
    have ih' : runBlock M c = runBlock M (a ++ b) :=
      funext (ih (fun x hx y' hy' => hind x hx y' (List.mem_cons_of_mem _ hy')))
    have ap : runBlock M (a ++ b) = fun u => (runBlock M a u).bind (runBlock M b) :=
      funext (runBlock_append a b)
    rw [ih', ap, runBlock_append, ← Option.bind_assoc,
      comm_block (fun x hx => hind x hx y List.mem_cons_self) s, Option.bind_assoc]
    rfl

theorem runBlock_of_WP {is : List M.Instr} {s : M.State} {Q : M.State → Prop} (h : WP M (.block is) s Q) :
    ∃ s', runBlock M is s = some s' ∧ Q s' := by
  induction is generalizing s with
  | nil => exact ⟨s, rfl, WP.block_nil_iff.mp h⟩
  | cons i is ih =>
    obtain ⟨s₁, h₁, h₂⟩ := WP.block_cons_iff.mp h
    obtain ⟨s', h', hq⟩ := ih h₂
    exact ⟨s', by show (M.exec i s).bind (runBlock M is) = _; rw [h₁]; exact h', hq⟩

/-- An interleaving of independent blocks runs as the first block and then the second. -/
theorem WP.merge {c a b : List M.Instr} (hm : Merge c a b) (hind : Indeps M a b) {s : M.State}
    {Q : M.State → Prop} (h : WP M (.block (a ++ b)) s Q) : WP M (.block c) s Q := by
  obtain ⟨s', h', hq⟩ := runBlock_of_WP h
  exact WP.of_runBlock ⟨s', by rw [run_merge hm hind]; exact h', hq⟩

/-- Independent blocks, woven (`Impl.Weave.weave`), run as the first and then the second. -/
theorem WP.weave {a b : List M.Instr} (hind : Indeps M a b) {s : M.State}
    {Q : M.State → Prop} (h : WP M (.block a) s fun t => WP M (.block b) t Q) :
    WP M (.block (VG.Impl.Weave.weave a b)) s Q :=
  WP.merge (weave_merge a b) hind (WP.block_append_iff.mpr h)

/-! ## Footprints -/

/-- What the instructions of a class may read and write (`fp`, `none` outside
the class), as data whose independence (`indep`) is checked by evaluation:
instructions with independent footprints commute (`comm`). `indep` of a
union implies it of each part, so it is checked once on the union of each
block's footprints. -/
structure Footprints (M : ISA) where
  Fp : Type
  fp : M.Instr → Option Fp
  empty : Fp
  union : Fp → Fp → Fp
  indep : Fp → Fp → Bool
  indep_union_left : ∀ {A B C : Fp}, indep (union A B) C = true → indep A C = true ∧ indep B C = true
  indep_union_right : ∀ {A B C : Fp}, indep A (union B C) = true → indep A B = true ∧ indep A C = true
  comm : ∀ {x y : M.Instr} {F G : Fp}, fp x = some F → fp y = some G → indep F G = true → Commute M x y

namespace Footprints

variable (P : Footprints M)

/-- The union of the footprints of a block, `none` if an instruction is outside the class. -/
def blockFp : List M.Instr → Option P.Fp
  | [] => some P.empty
  | i :: is => (P.fp i).bind fun a => (blockFp is).map fun b => P.union a b

variable {P}

theorem indeps_right {x : M.Instr} {F : P.Fp} (hx : P.fp x = some F) {b : List M.Instr} {B : P.Fp}
    (hb : P.blockFp b = some B) (hi : P.indep F B = true) : ∀ y ∈ b, Commute M x y := by
  induction b generalizing B with
  | nil => intro y hy; cases hy
  | cons z b ih =>
    simp only [blockFp, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hb
    obtain ⟨G, hz, B', hb', rfl⟩ := hb
    obtain ⟨hG, hB'⟩ := P.indep_union_right hi
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact P.comm hx hz hG
    · exact ih hb' hB' y hy

theorem indeps_of {a b : List M.Instr} {A B : P.Fp} (ha : P.blockFp a = some A) (hb : P.blockFp b = some B)
    (hi : P.indep A B = true) : Indeps M a b := by
  induction a generalizing A with
  | nil => intro x hx; cases hx
  | cons z a ih =>
    simp only [blockFp, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨F, hz, A', ha', rfl⟩ := ha
    obtain ⟨hF, hA'⟩ := P.indep_union_left hi
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact indeps_right hz hb hF
    · exact ih ha' hA' x hx

/-- Independence by evaluating both blocks' footprints. -/
theorem indeps_of_check {a b : List M.Instr}
    (h : ((P.blockFp a).bind fun A => (P.blockFp b).map fun B => P.indep A B) = some true) :
    Indeps M a b := by
  cases ha : P.blockFp a with
  | none => rw [ha] at h; cases h
  | some A =>
    cases hb : P.blockFp b with
    | none => rw [ha, hb] at h; cases h
    | some B =>
      rw [ha, hb] at h
      exact indeps_of ha hb (Option.some.inj h)

end Footprints

end VG.Interleave
