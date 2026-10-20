module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Weave

/-!
# Interleaving independent code, for any ISA

Untrusted: everything here is checked by Lean. Two instructions *commute*
from the states of `P` (`CommuteOn`) when running them in either order from
such a state faults alike or ends in the same state. Any interleaving
(`Merge`) of two blocks whose instructions keep `P` and commute pairwise
from its states runs, from a state of `P`, as the first block and then the
second (`run_merge`, `WP.merge`, `WP.weave`). `P` is what commuting needs of
the state beyond the instructions themselves: for code reading and writing
at several base registers, that their regions are disjoint; nothing
(`fun _ => True`) for code at one base.

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

/-- An interleaving of groups is one of their instructions. -/
theorem Merge.flatten {α : Type} {c a b : List (List α)} (h : Merge c a b) : Merge c.flatten a.flatten b.flatten := by
  induction h with
  | nil => exact .nil
  | @left x c a b _ ih =>
    simp only [List.flatten_cons]
    induction x with
    | nil => exact ih
    | cons y x ihx => exact .left ihx
  | @right y c a b _ ih =>
    simp only [List.flatten_cons]
    induction y with
    | nil => exact ih
    | cons z y ihy => exact .right ihy

theorem weaveG_merge {α : Type} (a b : List (List α)) : Merge (VG.Impl.Weave.weaveG a b) a.flatten b.flatten :=
  (weave_merge a b).flatten

/-! ## Commuting instructions -/

/-- Running `x` then `y` from a state of `P` faults alike, or ends in the
same state, as `y` then `x`. -/
def CommuteOn (M : ISA) (P : M.State → Prop) (x y : M.Instr) : Prop :=
  ∀ s, P s → (M.exec x s).bind (M.exec y) = (M.exec y s).bind (M.exec x)

theorem CommuteOn.symm {P : M.State → Prop} {x y : M.Instr} (h : CommuteOn M P x y) : CommuteOn M P y x :=
  fun s hs => (h s hs).symm

/-- `x` keeps `P`. -/
def Preserves (M : ISA) (P : M.State → Prop) (x : M.Instr) : Prop :=
  ∀ s s', P s → M.exec x s = some s' → P s'

/-- The instructions of `a` and `b` keep `P`, and from its states every
instruction of `a` commutes with every instruction of `b`. `P` is what
commuting needs of the state beyond the instructions (e.g. that regions
at different base registers are disjoint); `fun _ => True` when nothing. -/
structure Indeps (M : ISA) (P : M.State → Prop) (a b : List M.Instr) : Prop where
  left : ∀ x ∈ a, Preserves M P x
  right : ∀ y ∈ b, Preserves M P y
  comm : ∀ x ∈ a, ∀ y ∈ b, CommuteOn M P x y

theorem runBlock_preserves {P : M.State → Prop} {a : List M.Instr} (ha : ∀ x ∈ a, Preserves M P x) :
    ∀ {s s' : M.State}, P s → runBlock M a s = some s' → P s' := by
  induction a with
  | nil => intro s s' hs h; cases h; exact hs
  | cons x a ih =>
    intro s s' hs h
    simp only [runBlock, Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, h⟩ := h
    exact ih (fun x' hx' => ha x' (List.mem_cons_of_mem _ hx')) (ha x List.mem_cons_self s u hs hu) h

theorem comm_block {P : M.State → Prop} {y : M.Instr} {a : List M.Instr}
    (ha : ∀ x ∈ a, Preserves M P x ∧ CommuteOn M P x y) {s : M.State} (hs : P s) :
    (M.exec y s).bind (runBlock M a) = (runBlock M a s).bind (M.exec y) := by
  induction a generalizing s with
  | nil =>
    show (M.exec y s).bind some = M.exec y s
    cases M.exec y s <;> rfl
  | cons x a ih =>
    show (M.exec y s).bind (fun u => (M.exec x u).bind (runBlock M a)) =
      ((M.exec x s).bind (runBlock M a)).bind (M.exec y)
    rw [← Option.bind_assoc, ← (ha x List.mem_cons_self).2 s hs, Option.bind_assoc, Option.bind_assoc]
    cases hx : M.exec x s with
    | none => rfl
    | some u =>
      exact ih (fun x' hx' => ha x' (List.mem_cons_of_mem _ hx'))
        ((ha x List.mem_cons_self).1 s u hs hx)

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

/-- An interleaving of blocks whose instructions commute runs, from a state of
`P`, as the first and then the second. -/
theorem run_merge {P : M.State → Prop} {c a b : List M.Instr} (hm : Merge c a b) (hind : Indeps M P a b)
    {s : M.State} (hs : P s) : runBlock M c s = runBlock M (a ++ b) s := by
  induction hm generalizing s with
  | nil => rfl
  | @left x c a b _ ih =>
    show (M.exec x s).bind (runBlock M c) = (M.exec x s).bind (runBlock M (a ++ b))
    cases hx : M.exec x s with
    | none => rfl
    | some u =>
      exact ih ⟨fun x' hx' => hind.left x' (List.mem_cons_of_mem _ hx'), hind.right,
        fun x' hx' y hy => hind.comm x' (List.mem_cons_of_mem _ hx') y hy⟩
        (hind.left x List.mem_cons_self s u hs hx)
  | @right y c a b _ ih =>
    show (M.exec y s).bind (runBlock M c) = runBlock M (a ++ y :: b) s
    have hind' : Indeps M P a b := ⟨hind.left, fun y' hy' => hind.right y' (List.mem_cons_of_mem _ hy'),
      fun x hx y' hy' => hind.comm x hx y' (List.mem_cons_of_mem _ hy')⟩
    have e : (M.exec y s).bind (runBlock M c) = (M.exec y s).bind (runBlock M (a ++ b)) := by
      cases hy : M.exec y s with
      | none => rfl
      | some u => exact ih hind' (hind.right y List.mem_cons_self s u hs hy)
    have ap : runBlock M (a ++ b) = fun u => (runBlock M a u).bind (runBlock M b) :=
      funext (runBlock_append a b)
    rw [e, ap, runBlock_append, ← Option.bind_assoc,
      comm_block (fun x hx => ⟨hind.left x hx, hind.comm x hx y List.mem_cons_self⟩) hs, Option.bind_assoc]
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
theorem WP.merge {P : M.State → Prop} {c a b : List M.Instr} (hm : Merge c a b) (hind : Indeps M P a b)
    {s : M.State} (hs : P s) {Q : M.State → Prop} (h : WP M (.block (a ++ b)) s Q) : WP M (.block c) s Q := by
  obtain ⟨s', h', hq⟩ := runBlock_of_WP h
  exact WP.of_runBlock ⟨s', by rw [run_merge hm hind hs]; exact h', hq⟩

/-- Independent blocks, woven (`Impl.Weave.weave`), run as the first and then the second. -/
theorem WP.weave {P : M.State → Prop} {a b : List M.Instr} (hind : Indeps M P a b) {s : M.State} (hs : P s)
    {Q : M.State → Prop} (h : WP M (.block a) s fun t => WP M (.block b) t Q) :
    WP M (.block (VG.Impl.Weave.weave a b)) s Q :=
  WP.merge (weave_merge a b) hind hs (WP.block_append_iff.mpr h)

/-- Independent blocks, woven in groups (`Impl.Weave.weaveG`), run as the first and then the second. -/
theorem WP.weaveG {P : M.State → Prop} {a b : List (List M.Instr)} (hind : Indeps M P a.flatten b.flatten)
    {s : M.State} (hs : P s) {Q : M.State → Prop} (h : WP M (.block a.flatten) s fun t => WP M (.block b.flatten) t Q) :
    WP M (.block (VG.Impl.Weave.weaveG a b)) s Q :=
  WP.merge (weaveG_merge a b) hind hs (WP.block_append_iff.mpr h)

/-! ## Footprints -/

/-- What the instructions of a class may read and write (`fp`, `none` outside
the class), as data whose independence (`indep`) is checked by evaluation:
instructions with independent footprints commute (`comm`) from the states
of `Inv`, which the class's instructions keep (`preserves`). `indep` of a
union implies it of each part, so it is checked once on the union of each
block's footprints. -/
structure Footprints (M : ISA) where
  Fp : Type
  fp : M.Instr → Option Fp
  /-- What commuting needs of the state, e.g. that regions at different
  bases are disjoint; `fun _ => True` when nothing. -/
  Inv : M.State → Prop
  preserves : ∀ {x : M.Instr} {F : Fp}, fp x = some F → Preserves M Inv x
  empty : Fp
  union : Fp → Fp → Fp
  indep : Fp → Fp → Bool
  indep_union_left : ∀ {A B C : Fp}, indep (union A B) C = true → indep A C = true ∧ indep B C = true
  indep_union_right : ∀ {A B C : Fp}, indep A (union B C) = true → indep A B = true ∧ indep A C = true
  comm : ∀ {x y : M.Instr} {F G : Fp}, fp x = some F → fp y = some G → indep F G = true → CommuteOn M Inv x y

namespace Footprints

variable (P : Footprints M)

/-- The union of the footprints of a block, `none` if an instruction is outside the class. -/
def blockFp : List M.Instr → Option P.Fp
  | [] => some P.empty
  | i :: is => (P.fp i).bind fun a => (blockFp is).map fun b => P.union a b

variable {P}

theorem preserves_of {a : List M.Instr} {A : P.Fp} (ha : P.blockFp a = some A) :
    ∀ x ∈ a, Preserves M P.Inv x := by
  induction a generalizing A with
  | nil => intro x hx; cases hx
  | cons z a ih =>
    simp only [blockFp, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨F, hz, A', ha', rfl⟩ := ha
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact P.preserves hz
    · exact ih ha' x hx

theorem indeps_right {x : M.Instr} {F : P.Fp} (hx : P.fp x = some F) {b : List M.Instr} {B : P.Fp}
    (hb : P.blockFp b = some B) (hi : P.indep F B = true) : ∀ y ∈ b, CommuteOn M P.Inv x y := by
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
    (hi : P.indep A B = true) : Indeps M P.Inv a b := by
  refine ⟨preserves_of ha, preserves_of hb, ?_⟩
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
    Indeps M P.Inv a b := by
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
