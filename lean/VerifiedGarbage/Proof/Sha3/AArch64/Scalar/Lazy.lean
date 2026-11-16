module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Reflect
import VerifiedGarbage.Proof.Framework.Bitslice.Anf
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.CoreExec
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Sha3.AArch64.Scalar.RotateExpr`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

/-- Push rotations to leaves. Deferred rotations can then be checked without
expanding an entire 24-round permutation into one expression tree. -/
def Expr.rotateNormal : Expr → Nat → Expr
  | .reg r, n => .ror (.reg r) (n % 64)
  | .slot k, n => .ror (.slot k) (n % 64)
  | .xor a b, n => .xor (a.rotateNormal n) (b.rotateNormal n)
  | .bic a b, n => .bic (a.rotateNormal n) (b.rotateNormal n)
  | .ror a k, n => a.rotateNormal ((k + n) % 64)

theorem rotateRight_not (x : Lane) (n : Nat) :
    (~~~x).rotateRight n = ~~~(x.rotateRight n) := by
  ext i hi
  simp only [BitVec.getElem_rotateRight, BitVec.getElem_not]
  split <;> rfl

theorem Expr.rotateNormal_eval (e : Expr) (f : File) (n : Nat) :
    (e.rotateNormal n).eval f = (e.eval f).rotateRight n := by
  induction e generalizing n with
  | reg r => exact BitVec.rotateRight_mod_eq_rotateRight
  | slot k => exact BitVec.rotateRight_mod_eq_rotateRight
  | xor a b ha hb =>
    simp only [rotateNormal, Expr.eval, ha, hb, VG.Bitslice.Anf.rotateRight_xor]
  | bic a b ha hb =>
    simp only [rotateNormal, Expr.eval, ha, hb, VG.Bitslice.Anf.rotateRight_and,
      rotateRight_not]
  | ror a k ha =>
    simp only [rotateNormal, Expr.eval, ha, VG.Bitslice.Anf.rotateRight_rotateRight]

end VG.Proof.Sha3.AArch64.Scalar

end

end


@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar.Lazy
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64.Scalar

deriving instance DecidableEq for ScalarOp

def registers : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x30]
def regIndex (r : Reg) : Nat := registers.idxOf r

def environment (logical physical : File) : File :=
  ⟨logical.regs, fun k => if k % 2 = 0 then physical.slots (k / 2)
    else physical.regs (registers.getD (k / 2) .x0)⟩

/-- Unassigned registers and preexisting slots are distinct symbolic inputs. -/
def physicalInitial : SymFile :=
  ⟨fun r => .slot (2 * regIndex r + 1), fun k => .slot (2 * k)⟩

/-- Model the physical input lanes by expressions in canonical logical lanes. -/
def symbolicLayout (layout : Layout) : SymFile :=
  layout.zipIdx.foldl (fun sf (entry, i) =>
    sf.write entry.1 (.ror (.reg (laneReg i)) entry.2)) physicalInitial

theorem environment_reg (logical physical : File) (r : Reg) :
    (Expr.slot (2 * regIndex r + 1)).eval (environment logical physical) = physical.regs r := by
  cases r <;> rfl

theorem physicalInitial_compatible (logical physical : File) :
    Compatible (environment logical physical) physicalInitial physical := by
  constructor
  · intro r; exact (environment_reg logical physical r).symm
  · intro k
    simp only [physicalInitial, Expr.eval, environment]
    rw [show 2 * k % 2 = 0 by omega_using [], ite_eq_left rfl,
      show 2 * k / 2 = k by omega_using []]

/-- Every listed lane has its declared physical orientation. -/
def LayoutHolds (layout : Layout) (logical physical : File) : Prop :=
  ∀ entry i, (entry, i) ∈ layout.zipIdx →
    physical.regs entry.1 = (logical.regs (laneReg i)).rotateRight entry.2

theorem symbolicLayout_compatible (layout : Layout) (logical physical : File)
    (h : LayoutHolds layout logical physical) :
    Compatible (environment logical physical) (symbolicLayout layout) physical := by
  apply List.foldlRecOn (motive := fun sf =>
    Compatible (environment logical physical) sf physical)
  · exact physicalInitial_compatible logical physical
  · intro sf hs entry he
    obtain ⟨⟨reg, offset⟩, i⟩ := entry
    constructor
    · intro q
      simp only [SymFile.write]
      split
      · rename_i hq; subst q
        exact h (reg, offset) i he
      · exact hs.1 q
    · exact hs.2

def outputExpr (p : Plan) (i : Nat) : Expr :=
  let (reg, offset) := p.output.getD i (.x0, 0)
  ((symRun p.core (symbolicLayout p.input)).regs reg).rotateNormal ((64-offset)%64)

def referenceExpr (i : Nat) : Expr :=
  ((symRun coreOps symInitial).regs (laneReg i)).rotateNormal 0

theorem plan_math (p : Plan)
    (cert : ∀ i < 25, outputExpr p i = referenceExpr i)
    (logical physical : File) (h : LayoutHolds p.input logical physical)
    (i : Nat) (hi : i < 25) :
    let (reg, offset) := p.output.getD i (.x0, 0)
    ((run p.core physical).regs reg).rotateRight ((64-offset)%64) =
      (run coreOps (environment logical physical)).regs (laneReg i) := by
  have hc := symRun_correct (environment logical physical) physical
    (symbolicLayout p.input) p.core (symbolicLayout_compatible p.input logical physical h)
  have he := congrArg (Expr.eval (environment logical physical)) (cert i hi)
  dsimp only [outputExpr, referenceExpr] at he
  rw [Expr.rotateNormal_eval, Expr.rotateNormal_eval,
    VG.Bitslice.Anf.rotateRight_zero, ← run_regs] at he
  rw [← hc.1] at he
  rcases hp : p.output.getD i (.x0, 0) with ⟨reg, offset⟩
  simpa only [hp] using he

theorem rotateRight_undo (x : Lane) (offset : Nat) (ho : offset < 64) :
    (x.rotateRight ((64-offset)%64)).rotateRight offset = x := by
  rw [VG.Bitslice.Anf.rotateRight_rotateRight]
  have hm : (((64-offset)%64)+offset)%64 = 0 := by omega_using [ho]
  rw [hm, VG.Bitslice.Anf.rotateRight_zero]

theorem plan_layout (p : Plan)
    (cert : ∀ i < 25, outputExpr p i = referenceExpr i)
    (hlen : p.output.length = 25)
    (bounds : ∀ entry ∈ p.output, entry.2 < 64)
    (logical physical : File) (h : LayoutHolds p.input logical physical) :
    LayoutHolds p.output (run coreOps (environment logical physical)) (run p.core physical) := by
  intro entry i he
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp he
  have hi : i < 25 := by
    have hlt := (List.getElem?_eq_some_iff.mp hget).1
    omega_using [hlen, hlt]
  have hd : p.output.getD i (.x0, 0) = entry := by
    simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some]
  have hm := plan_math p cert logical physical h i hi
  simp only [hd] at hm
  have hb : entry.2 < 64 := bounds entry (List.mem_of_getElem? hget)
  have ht := congrArg (fun x : Lane => x.rotateRight entry.2) hm
  rw [rotateRight_undo _ _ hb] at ht
  exact ht

/-! ## The certificate, for the kernel

`outputExpr` reads a `SymFile`, a chain of functions that the kernel follows again for every
read, and compares two trees of a hundred nodes for every lane of every round. The kernel checks
the same run with

* the registers in a structure (`KF`), read by a projection and written by rebuilding it;
* expressions read from a register evaluated before they are used (`force`), and rotations
  evaluated before they are passed down (`forceNat`), so that a subexpression several lanes
  share is the same term in each, and the kernel finds again what it did with it;
* the comparison in `Bool` (`same`): `DecidableEq`'s answer for two applications carries a
  cast along the equation of their arguments, which the kernel reduces by comparing them as the
  terms they are. -/

/-- `k e`, with `e` evaluated to its constructor. -/
private def force {α : Type} (e : Expr) (k : Expr → α) : α :=
  Expr.casesOn (motive := fun _ => α) e (fun r => k (.reg r)) (fun s => k (.slot s))
    (fun a b => k (.xor a b)) (fun a b => k (.bic a b)) (fun a n => k (.ror a n))

private theorem force_eq {α : Type} (e : Expr) (k : Expr → α) : force e k = k e := by cases e <;> rfl

/-- `k n`, with `n` evaluated to a numeral. -/
private def forceNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.casesOn (motive := fun _ => α) (Nat.succ n) (k n) (fun m => k m)

private theorem forceNat_eq {α : Type} (n : Nat) (k : Nat → α) : forceNat n k = k n := rfl

/-- The registers' expressions, a field each. -/
private structure KF where
  (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x30 : Expr)
  slots : Nat → Expr

private def KF.get (f : KF) (r : Reg) : Expr :=
  (match r with
    | .x0 => KF.x0 | .x1 => KF.x1 | .x2 => KF.x2 | .x3 => KF.x3 | .x4 => KF.x4 | .x5 => KF.x5
    | .x6 => KF.x6 | .x7 => KF.x7 | .x8 => KF.x8 | .x9 => KF.x9 | .x10 => KF.x10 | .x11 => KF.x11
    | .x12 => KF.x12 | .x13 => KF.x13 | .x14 => KF.x14 | .x15 => KF.x15 | .x16 => KF.x16
    | .x17 => KF.x17 | .x19 => KF.x19 | .x20 => KF.x20 | .x21 => KF.x21 | .x22 => KF.x22
    | .x23 => KF.x23 | .x24 => KF.x24 | .x25 => KF.x25 | .x26 => KF.x26 | .x27 => KF.x27
    | .x28 => KF.x28 | .x30 => KF.x30) f

private def KF.write (f : KF) (d : Reg) (v : Expr) : KF :=
  (match d with
    | .x0 => fun f v => { f with x0 := v } | .x1 => fun f v => { f with x1 := v }
    | .x2 => fun f v => { f with x2 := v } | .x3 => fun f v => { f with x3 := v }
    | .x4 => fun f v => { f with x4 := v } | .x5 => fun f v => { f with x5 := v }
    | .x6 => fun f v => { f with x6 := v } | .x7 => fun f v => { f with x7 := v }
    | .x8 => fun f v => { f with x8 := v } | .x9 => fun f v => { f with x9 := v }
    | .x10 => fun f v => { f with x10 := v } | .x11 => fun f v => { f with x11 := v }
    | .x12 => fun f v => { f with x12 := v } | .x13 => fun f v => { f with x13 := v }
    | .x14 => fun f v => { f with x14 := v } | .x15 => fun f v => { f with x15 := v }
    | .x16 => fun f v => { f with x16 := v } | .x17 => fun f v => { f with x17 := v }
    | .x19 => fun f v => { f with x19 := v } | .x20 => fun f v => { f with x20 := v }
    | .x21 => fun f v => { f with x21 := v } | .x22 => fun f v => { f with x22 := v }
    | .x23 => fun f v => { f with x23 := v } | .x24 => fun f v => { f with x24 := v }
    | .x25 => fun f v => { f with x25 := v } | .x26 => fun f v => { f with x26 := v }
    | .x27 => fun f v => { f with x27 := v } | .x28 => fun f v => { f with x28 := v }
    | .x30 => fun f v => { f with x30 := v } : KF → Expr → KF) f v

/-- The registers' expressions, in the order of `registers`. -/
private def KF.toList (f : KF) : List Expr :=
  [f.x0, f.x1, f.x2, f.x3, f.x4, f.x5, f.x6, f.x7, f.x8, f.x9, f.x10, f.x11, f.x12, f.x13,
    f.x14, f.x15, f.x16, f.x17, f.x19, f.x20, f.x21, f.x22, f.x23, f.x24, f.x25, f.x26, f.x27,
    f.x28, f.x30]

private theorem KF.get_toList (f : KF) (r : Reg) : f.get r = f.toList.getD r.ctorIdx (.slot 0) := by
  cases r <;> rfl

private theorem KF.toList_write (f : KF) (d : Reg) (v : Expr) :
    (f.write d v).toList = f.toList.set d.ctorIdx v := by
  cases d <;> rfl

private theorem ctorIdx_inj {q d : Reg} (h : q.ctorIdx = d.ctorIdx) : q = d := by
  have e : ∀ r : Reg, registers.getD r.ctorIdx .x0 = r := fun r => by cases r <;> rfl
  rw [← e q, ← e d, h]

/-- By the list of the fields: a case for each register, not for each pair. -/
private theorem KF.get_write (f : KF) (d q : Reg) (v : Expr) :
    (f.write d v).get q = if q = d then v else f.get q := by
  by_cases h : q = d
  · subst h; rw [ite_eq_left rfl]; cases q <;> rfl
  · rw [ite_eq_right h, KF.get_toList, KF.toList_write, KF.get_toList, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_set_ne fun e => h (ctorIdx_inj e.symm)]

private theorem KF.slots_write (f : KF) (d : Reg) (v : Expr) : (f.write d v).slots = f.slots := by
  cases d <;> rfl

private def KF.ofFn (g : Reg → Expr) (sl : Nat → Expr) : KF :=
  ⟨g .x0, g .x1, g .x2, g .x3, g .x4, g .x5, g .x6, g .x7, g .x8, g .x9, g .x10, g .x11, g .x12,
    g .x13, g .x14, g .x15, g .x16, g .x17, g .x19, g .x20, g .x21, g .x22, g .x23, g .x24,
    g .x25, g .x26, g .x27, g .x28, g .x30, sl⟩

/-- A `KF` holds what a `SymFile` does. -/
private def Agree (sf : SymFile) (f : KF) : Prop := (∀ r, sf.regs r = f.get r) ∧ sf.slots = f.slots

private theorem KF.ofFn_agree (g : Reg → Expr) (sl : Nat → Expr) : Agree ⟨g, sl⟩ (KF.ofFn g sl) :=
  ⟨fun r => by cases r <;> rfl, rfl⟩

private theorem Agree.write {sf : SymFile} {f : KF} (h : Agree sf f) (d : Reg) (v : Expr) :
    Agree (sf.write d v) (f.write d v) :=
  ⟨fun q => by rw [KF.get_write, ← h.1 q]; rfl, by rw [KF.slots_write]; exact h.2⟩

/-- `symStep`, on a `KF`, with the operands evaluated. -/
private def kStepF (f : KF) : ScalarOp → KF
  | .xor d a b => force (f.get a) fun x => force (f.get b) fun y => f.write d (.xor x y)
  | .xorRor d a b n => force (f.get a) fun x => force (f.get b) fun y => f.write d (.xor x (.ror y n))
  | .bic d a b => force (f.get a) fun x => force (f.get b) fun y => f.write d (.bic x y)
  | .bicRor d a b n => force (f.get a) fun x => force (f.get b) fun y => f.write d (.bic x (.ror y n))
  | .ror d a n => force (f.get a) fun x => f.write d (.ror x n)
  | .move d a => force (f.get a) fun x => f.write d x
  | .spill k a => force (f.get a) fun x => { f with slots := fun j => if j = k then x else f.slots j }
  | .reload d k => force (f.slots k) fun x => f.write d x

private def kRunF (ops : List ScalarOp) (f : KF) : KF := ops.foldl kStepF f

private theorem kStepF_agree {sf : SymFile} {f : KF} (h : Agree sf f) (op : ScalarOp) :
    Agree (symStep sf op) (kStepF f op) := by
  cases op <;> simp only [kStepF, symStep, force_eq, h.1, h.2]
  case spill k a => exact ⟨fun r => by cases r <;> exact h.1 _, rfl⟩
  all_goals exact h.write _ _

private theorem kRunF_agree {sf : SymFile} {f : KF} (h : Agree sf f) (ops : List ScalarOp) :
    Agree (symRun ops sf) (kRunF ops f) := by
  induction ops generalizing sf f with
  | nil => exact h
  | cons op ops ih => exact ih (kStepF_agree h op)

/-- `symbolicLayout`, as a `KF`. -/
private def kLayoutF (layout : Layout) : KF :=
  layout.zipIdx.foldl (fun kf (entry, i) =>
    kf.write entry.1 (.ror (.reg (laneReg i)) entry.2))
    (KF.ofFn (fun r => .slot (2 * regIndex r + 1)) fun k => .slot (2 * k))

private theorem kLayoutF_agree (layout : Layout) : Agree (symbolicLayout layout) (kLayoutF layout) := by
  unfold symbolicLayout kLayoutF
  have h : Agree physicalInitial
      (KF.ofFn (fun r => .slot (2 * regIndex r + 1)) fun k => .slot (2 * k)) := KF.ofFn_agree _ _
  generalize layout.zipIdx = l
  generalize physicalInitial = sf at h ⊢
  generalize KF.ofFn (fun r => .slot (2 * regIndex r + 1)) (fun k => .slot (2 * k)) = kf at h ⊢
  induction l generalizing sf kf with
  | nil => exact h
  | cons e l ih => exact ih _ _ (h.write e.1.1 _)

/-- `Expr.rotateNormal`, with the rotation it passes down evaluated. By the recursor, whose
cases are closed terms: the kernel instantiates nothing to unfold it. -/
private noncomputable def norm (e : Expr) : Nat → Expr :=
  Expr.rec (motive := fun _ => Nat → Expr)
    (fun r n => .ror (.reg r) (n % 64))
    (fun k n => .ror (.slot k) (n % 64))
    (fun _ _ na nb n => .xor (na n) (nb n))
    (fun _ _ na nb n => .bic (na n) (nb n))
    (fun _ k na n => forceNat ((k + n) % 64) fun m => na m) e

private theorem norm_eq (e : Expr) (n : Nat) : norm e n = e.rotateNormal n := by
  induction e generalizing n with
  | reg r => rfl
  | slot k => rfl
  | xor a b ha hb => rw [Expr.rotateNormal, ← ha, ← hb]; rfl
  | bic a b ha hb => rw [Expr.rotateNormal, ← ha, ← hb]; rfl
  | ror a k ha => exact ha ((k + n) % 64)

/-- Whether two expressions are the same. -/
private noncomputable def same (a : Expr) : Expr → Bool :=
  Expr.rec (motive := fun _ => Expr → Bool)
    (fun r b => match b with | .reg q => decide (r = q) | _ => false)
    (fun k b => match b with | .slot j => decide (k = j) | _ => false)
    (fun _ _ sa sb b => match b with | .xor c d => sa c && sb d | _ => false)
    (fun _ _ sa sb b => match b with | .bic c d => sa c && sb d | _ => false)
    (fun _ n sa b => match b with | .ror c m => decide (n = m) && sa c | _ => false) a

private theorem eq_of_same {a b : Expr} (h : same a b = true) : a = b := by
  induction a generalizing b with
  | reg r => cases b <;> first | exact absurd h Bool.false_ne_true | exact congrArg _ (of_decide_eq_true h)
  | slot k => cases b <;> first | exact absurd h Bool.false_ne_true | exact congrArg _ (of_decide_eq_true h)
  | xor a₁ a₂ h₁ h₂ =>
    cases b with
    | xor c d => have h' := Bool.and_eq_true_iff.mp h; rw [h₁ h'.1, h₂ h'.2]
    | _ => exact absurd h Bool.false_ne_true
  | bic a₁ a₂ h₁ h₂ =>
    cases b with
    | bic c d => have h' := Bool.and_eq_true_iff.mp h; rw [h₁ h'.1, h₂ h'.2]
    | _ => exact absurd h Bool.false_ne_true
  | ror a₁ n h₁ =>
    cases b with
    | ror c m => have h' := Bool.and_eq_true_iff.mp h; rw [h₁ h'.2, of_decide_eq_true h'.1]
    | _ => exact absurd h Bool.false_ne_true

/-- `outputExpr`, as the kernel evaluates it. -/
private noncomputable def outputExprF (p : Plan) (i : Nat) : Expr :=
  forceNat ((64 - (p.output.getD i (.x0, 0)).2) % 64) fun n =>
    norm ((kRunF p.core (kLayoutF p.input)).get (p.output.getD i (.x0, 0)).1) n

/-- `referenceExpr`, as the kernel evaluates it. -/
private noncomputable def referenceExprF (i : Nat) : Expr :=
  norm ((kRunF coreOps (KF.ofFn Expr.reg Expr.slot)).get (laneReg i)) 0

private theorem outputExpr_f (p : Plan) (i : Nat) : outputExpr p i = outputExprF p i := by
  rw [outputExprF, forceNat_eq, norm_eq, ← (kRunF_agree (kLayoutF_agree p.input) p.core).1]
  rfl

private theorem referenceExpr_f (i : Nat) : referenceExpr i = referenceExprF i := by
  have h : Agree symInitial (KF.ofFn Expr.reg Expr.slot) := KF.ofFn_agree _ _
  rw [referenceExpr, referenceExprF, norm_eq, ← (kRunF_agree h coreOps).1]

private theorem plans_symbolic_f : ∀ (r : Fin 24), ∀ i < 25,
    same (outputExprF (plans[r.val]' (by exact r.isLt)) i) (referenceExprF i) = true := by
  decide +kernel

theorem plans_symbolic : ∀ (r : Fin 24), ∀ i < 25, outputExpr (plans[r.val]' (by exact r.isLt)) i = referenceExpr i :=
  fun r i hi => by
    rw [outputExpr_f, referenceExpr_f]; exact eq_of_same (plans_symbolic_f r i hi)

theorem plans_shape : ∀ r : Fin 24,
    (plan r).input.length = 25 ∧ (plan r).output.length = 25 ∧
    (plan r).finish = (plan r).output ∧
    (∀ entry ∈ (plan r).output, entry.2 < 64) ∧
    (∀ op ∈ (plan r).core, Good op) ∧ Good (plan r).iota := by decide +kernel

theorem plans_iota : ∀ r : Fin 24,
    let lane := (plan r).output.getD 0 (.x0, 0)
    (plan r).iota = .xorRor lane.1 lane.1 (plan r).constantReg lane.2 ∧
    (∀ entry ∈ (plan r).output, entry.1 ≠ (plan r).constantReg) := by decide +kernel

theorem plans_lane_zero : ∀ r : Fin 24, ∀ i < 25,
    ((plan r).output.getD i (.x0, 0)).1 =
      ((plan r).output.getD 0 (.x0, 0)).1 ↔ i = 0 := by decide +kernel

theorem normalize_symbolic : ∀ i < 25,
    ((symRun normalize (symbolicLayout (plan ⟨23, by decide⟩).finish)).regs
      (laneReg i)).rotateNormal 0 = (Expr.reg (laneReg i)).rotateNormal 0 := by decide +kernel

def stageLayout (n : Nat) : Layout :=
  if h : n < 24 then (plan ⟨n, h⟩).input else (plan ⟨23, by decide⟩).finish

theorem plans_stage : ∀ r : Fin 24, (plan r).finish = stageLayout (r.val+1) := by
  decide +kernel

theorem normalize_good : ∀ op ∈ normalize, Good op := by decide +kernel

end VG.Proof.Sha3.AArch64.Scalar.Lazy
