module

public import VerifiedGarbage.Proof.Argon2.AArch64.Mix
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

@[expose] public section
namespace VG.Proof.Argon2.AArch64.Schedule
open VG VG.AArch64 VG.Impl.Argon2.AArch64

/-- A complete addition consumes the shared temporary before another chain
uses it; rotations never read that temporary. -/
inductive Op where
  | add (a b : Reg)
  | rotate (d a : Reg) (n : Nat)
  deriving DecidableEq

def lower : Op → List Instr
  | .add a b => addMul a b .x17
  | .rotate d a n => [.logic .eor .x d d a, .ror .x d d n]

def Good : Op → Prop
  | .add a b => a ≠ .x17 ∧ b ≠ .x17
  | .rotate d a n => d ≠ .x17 ∧ a ≠ .x17 ∧ 1 ≤ n ∧ n ≤ 63

def step (f : Reg → BitVec 64) : Op → Reg → BitVec 64
  | .add a b => fun r => if r = a then Spec.Argon2.addMul (f a) (f b) else f r
  | .rotate d a n => fun r => if r = d then (f d ^^^ f a).rotateRight n else f r

def run (ops : List Op) (f : Reg → BitVec 64) := ops.foldl step f

def Rel (f : Reg → BitVec 64) (s : State) := ∀ r, r ≠ .x17 → s.gpr r = f r

theorem one_ok (op : Op) (hg : Good op) (f : Reg → BitVec 64) (s : State)
    (hr : Rel f s) :
    WP isa (.block (lower op)) s fun t =>
      Rel (step f op) t ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.v = s.v := by
  cases op with
  | add a b =>
    refine (addMul_ok hg.1 hg.2 s).mono ?_
    rintro t ⟨ha, hk, hm, hrd, hwr, hv⟩
    refine ⟨?_, hm, hrd, hwr, hv⟩
    · intro r hrt
      by_cases h : r = a
      · subst r; simpa only [step, ite_true, hr _ hg.1, hr _ hg.2] using ha
      · simpa only [step, h, ite_false] using (hk r h hrt).trans (hr r hrt)
  | rotate d a n =>
    refine (xorRotate_ok n hg.2.2.1 hg.2.2.2 s).mono ?_
    rintro t ⟨hd, hk, hm, hrd, hwr, hv⟩
    refine ⟨?_, hm, hrd, hwr, hv⟩
    · intro r hrt
      by_cases h : r = d
      · subst r; simpa only [step, ite_true, hr _ hg.1, hr _ hg.2.1] using hd
      · simpa only [step, h, ite_false] using (hk r h).trans (hr r hrt)
theorem list_ok (ops : List Op) (hg : ∀ op ∈ ops, Good op)
    (f : Reg → BitVec 64) (s : State) (hr : Rel f s) :
    WP isa (.block (ops.flatMap lower)) s fun t =>
      Rel (run ops f) t ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.v = s.v := by
  induction ops generalizing f s with
  | nil => exact WP.block_nil ⟨hr, rfl, rfl, rfl, rfl⟩
  | cons op ops ih =>
    rw [List.flatMap_cons]
    apply WP.block_append
    refine (one_ok op (hg op (List.mem_cons_self ..)) f s hr).mono ?_
    rintro t ⟨ht, hm, hrd, hwr, hv⟩
    refine (ih (fun op ho => hg op (List.mem_cons_of_mem _ ho)) (step f op) t ht).mono ?_
    rintro u ⟨hu, hm', hrd', hwr', hv'⟩
    exact ⟨hu, hm'.trans hm, hrd'.trans hrd, hwr'.trans hwr, hv'.trans hv⟩

inductive Expr where
  | reg (r : Reg)
  | add (a b : Expr)
  | rotate (d a : Expr) (n : Nat)
  deriving DecidableEq

def Expr.eval (f : Reg → BitVec 64) : Expr → BitVec 64
  | .reg r => f r
  | .add a b => Spec.Argon2.addMul (a.eval f) (b.eval f)
  | .rotate d a n => (d.eval f ^^^ a.eval f).rotateRight n

def symStep (f : Reg → Expr) : Op → Reg → Expr
  | .add a b => fun r => if r = a then .add (f a) (f b) else f r
  | .rotate d a n => fun r => if r = d then .rotate (f d) (f a) n else f r

def symRun (ops : List Op) (f : Reg → Expr) := ops.foldl symStep f

theorem symbolic_correct (ops : List Op) (input f : Reg → BitVec 64)
    (sf : Reg → Expr) (h : ∀ r, f r = (sf r).eval input) :
    ∀ r, run ops f r = (symRun ops sf r).eval input := by
  induction ops generalizing f sf with
  | nil => exact h
  | cons op ops ih =>
    apply ih
    intro r
    cases op <;> simp only [step, symStep] <;> split <;> simp_all only [Expr.eval]

def halfOps (a b c d : Reg) (r1 r2 : Nat) : List Op :=
  [.add a b, .rotate d a r1, .add c d, .rotate b c r2]

def gbOps (q : Reg × Reg × Reg × Reg) : List Op :=
  let (a,b,c,d) := q
  halfOps a b c d 32 24 ++ halfOps a b c d 16 63

def halfGroup (qs : List (Reg × Reg × Reg × Reg)) (r1 r2 : Nat) : List Op :=
  qs.map (fun (a,b,_,_) => .add a b) ++
  qs.map (fun (a,_,_,d) => .rotate d a r1) ++
  qs.map (fun (_,_,c,d) => .add c d) ++
  qs.map (fun (_,b,c,_) => .rotate b c r2)

def groupOps (qs : List (Reg × Reg × Reg × Reg)) : List Op :=
  halfGroup qs 32 24 ++ halfGroup qs 16 63

def columns : List (Reg × Reg × Reg × Reg) :=
  [(lane 0,lane 4,lane 8,lane 12),(lane 1,lane 5,lane 9,lane 13),
   (lane 2,lane 6,lane 10,lane 14),(lane 3,lane 7,lane 11,lane 15)]

def diagonals : List (Reg × Reg × Reg × Reg) :=
  [(lane 0,lane 5,lane 10,lane 15),(lane 1,lane 6,lane 11,lane 12),
   (lane 2,lane 7,lane 8,lane 13),(lane 3,lane 4,lane 9,lane 14)]

def serialOps := (columns ++ diagonals).flatMap gbOps

def scheduledOps := groupOps columns ++ groupOps diagonals

instance (op : Op) : Decidable (Good op) := by
  cases op <;> dsimp only [Good] <;> infer_instance

theorem good_serial : ∀ op ∈ serialOps, Good op := by
  have h : serialOps.all (fun op => decide (Good op)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem good_scheduled : ∀ op ∈ scheduledOps, Good op := by
  have h : scheduledOps.all (fun op => decide (Good op)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

/-- Each half-round is checked separately, keeping the expression trees
small and the proof independent of the numeric values of the lanes. -/
theorem same_group_expressions (diagonal : Bool) : ∀ r : Reg,
    let qs := if diagonal then diagonals else columns
    symRun (groupOps qs) Expr.reg r = symRun (qs.flatMap gbOps) Expr.reg r := by
  cases diagonal <;> intro r <;> cases r <;> decide +kernel

theorem same_group_values (diagonal : Bool) (f : Reg → BitVec 64) (r : Reg) :
    let qs := if diagonal then diagonals else columns
    run (groupOps qs) f r = run (qs.flatMap gbOps) f r := by
  dsimp only
  rw [symbolic_correct _ f f Expr.reg (fun _ => rfl),
    symbolic_correct _ f f Expr.reg (fun _ => rfl), same_group_expressions]

theorem same_values (f : Reg → BitVec 64) (r : Reg) :
    run scheduledOps f r = run serialOps f r := by
  simp only [scheduledOps, serialOps, List.flatMap_append, run, List.foldl_append]
  change run (groupOps diagonals) (run (groupOps columns) f) r =
    run (diagonals.flatMap gbOps) (run (columns.flatMap gbOps) f) r
  have hc : run (groupOps columns) f = run (columns.flatMap gbOps) f :=
    funext (same_group_values false f)
  rw [hc]
  exact same_group_values true _ r

theorem lower_halfGroup (qs : List (Reg × Reg × Reg × Reg)) (r1 r2 : Nat) :
    (halfGroup qs r1 r2).flatMap lower = halfGBs qs r1 r2 := by
  simp [halfGroup, halfGBs, lower, List.flatMap_append, List.flatMap_map]

theorem lower_gbOps (q : Reg × Reg × Reg × Reg) :
    (gbOps q).flatMap lower = gb q.1 q.2.1 q.2.2.1 q.2.2.2 .x17 := by
  rcases q with ⟨a,b,c,d⟩
  simp [gbOps, halfOps, lower, gb, halfGB, List.append_assoc]

end VG.Proof.Argon2.AArch64.Schedule
