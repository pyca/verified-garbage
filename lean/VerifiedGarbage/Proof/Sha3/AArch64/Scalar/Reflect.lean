module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

/-- Expressions preserve the meaning of the instruction schedule without
replaying its symbolic register writes once for every output lane. -/
inductive Expr where
  | reg (r : Reg)
  | slot (k : Nat)
  | xor (a b : Expr)
  | bic (a b : Expr)
  | ror (a : Expr) (n : Nat)
  deriving DecidableEq

def Expr.eval (f : File) : Expr → Lane
  | .reg r => f.regs r
  | .slot k => f.slots k
  | .xor a b => a.eval f ^^^ b.eval f
  | .bic a b => a.eval f &&& ~~~b.eval f
  | .ror a n => (a.eval f).rotateRight n

structure SymFile where
  regs : Reg → Expr
  slots : Nat → Expr

def SymFile.write (f : SymFile) (r : Reg) (v : Expr) : SymFile :=
  { f with regs := fun q => if q = r then v else f.regs q }

def symStep (f : SymFile) : ScalarOp → SymFile
  | .xor d a b => f.write d (.xor (f.regs a) (f.regs b))
  | .xorRor d a b n => f.write d (.xor (f.regs a) (.ror (f.regs b) n))
  | .bic d a b => f.write d (.bic (f.regs a) (f.regs b))
  | .bicRor d a b n => f.write d (.bic (f.regs a) (.ror (f.regs b) n))
  | .ror d a n => f.write d (.ror (f.regs a) n)
  | .move d a => f.write d (f.regs a)
  | .spill k a => { f with slots := fun j => if j = k then f.regs a else f.slots j }
  | .reload d k => f.write d (f.slots k)

def symRun (ops : List ScalarOp) (f : SymFile) : SymFile := ops.foldl symStep f

def symInitial : SymFile := ⟨Expr.reg, Expr.slot⟩

/-! ## The same run, for the kernel

A `SymFile`'s registers are a chain of functions, `fun q => if q = r then v else …`, one for
every write, and the kernel follows the chain again for every read: whether `q = r` is not a
term it caches. `KFile` keeps the registers' expressions in a list, a register's at its index,
which the kernel reads through a chain of `List.set` by evaluating each list once
(`symRun_regs`). -/

structure KFile where
  regs : List Expr
  slots : Nat → Expr

def KFile.get (f : KFile) (r : Reg) : Expr := f.regs.getD r.ctorIdx (.reg r)

def KFile.write (f : KFile) (r : Reg) (v : Expr) : KFile := { f with regs := f.regs.set r.ctorIdx v }

def kStep (f : KFile) : ScalarOp → KFile
  | .xor d a b => f.write d (.xor (f.get a) (f.get b))
  | .xorRor d a b n => f.write d (.xor (f.get a) (.ror (f.get b) n))
  | .bic d a b => f.write d (.bic (f.get a) (f.get b))
  | .bicRor d a b n => f.write d (.bic (f.get a) (.ror (f.get b) n))
  | .ror d a n => f.write d (.ror (f.get a) n)
  | .move d a => f.write d (f.get a)
  | .spill k a => { f with slots := fun j => if j = k then f.get a else f.slots j }
  | .reload d k => f.write d (f.slots k)

def kRun (ops : List ScalarOp) (f : KFile) : KFile := ops.foldl kStep f

def kInitial : KFile := ⟨(List.range 29).map fun i => .reg (Reg.ofNat i), Expr.slot⟩

/-- A `KFile` that holds what a `SymFile` does. -/
def Agree (sf : SymFile) (kf : KFile) : Prop :=
  kf.regs.length = 29 ∧ (∀ r, sf.regs r = kf.get r) ∧ ∀ k, sf.slots k = kf.slots k

theorem ctorIdx_lt (r : Reg) : r.ctorIdx < 29 := by cases r <;> decide

theorem KFile.get_write {f : KFile} (hl : f.regs.length = 29) (d q : Reg) (v : Expr) :
    (f.write d v).get q = if q = d then v else f.get q := by
  unfold KFile.get KFile.write
  rw [List.getD_eq_getElem?_getD]
  split
  · next h =>
    subst h
    rw [List.getElem?_set_self (by rw [hl]; exact ctorIdx_lt q)]
    rfl
  · next h =>
    have hi : d.ctorIdx ≠ q.ctorIdx := fun e => h (by rw [← Reg.ofNat_ctorIdx q, ← e, Reg.ofNat_ctorIdx])
    rw [List.getElem?_set_ne hi, ← List.getD_eq_getElem?_getD]

theorem Agree.write {sf : SymFile} {kf : KFile} (h : Agree sf kf) (d : Reg) {v w : Expr} (e : v = w) :
    Agree (sf.write d v) (kf.write d w) :=
  ⟨by simp only [KFile.write, List.length_set, h.1],
    fun q => by rw [KFile.get_write h.1, ← h.2.1 q, e]; rfl, h.2.2⟩

theorem kStep_agree {sf : SymFile} {kf : KFile} (h : Agree sf kf) (op : ScalarOp) :
    Agree (symStep sf op) (kStep kf op) := by
  cases op with
  | spill k a => exact ⟨h.1, h.2.1, fun j => by simp only [symStep, kStep, h.2.1 a, h.2.2 j]⟩
  | reload d k => exact h.write d (h.2.2 k)
  | _ => exact h.write _ (by simp only [h.2.1])

theorem kRun_agree {sf : SymFile} {kf : KFile} (h : Agree sf kf) (ops : List ScalarOp) :
    Agree (symRun ops sf) (kRun ops kf) := by
  induction ops generalizing sf kf with
  | nil => exact h
  | cons op ops ih => exact ih (kStep_agree h op)

theorem agree_initial : Agree symInitial kInitial :=
  ⟨by simp only [kInitial, List.length_map, List.length_range], fun r => by cases r <;> rfl, fun _ => rfl⟩

/-- A register after a symbolic run, as the kernel evaluates it. -/
theorem symRun_regs (ops : List ScalarOp) (r : Reg) :
    (symRun ops symInitial).regs r = (kRun ops kInitial).get r :=
  (kRun_agree agree_initial ops).2.1 r

def Compatible (input : File) (sf : SymFile) (f : File) : Prop :=
  (∀ r, f.regs r = (sf.regs r).eval input) ∧
  (∀ k, f.slots k = (sf.slots k).eval input)

theorem symStep_correct (input f : File) (sf : SymFile) (op : ScalarOp)
    (h : Compatible input sf f) : Compatible input (symStep sf op) (step f op) := by
  obtain ⟨hr, hs⟩ := h
  cases op <;> constructor <;> intro q <;>
    simp only [step, symStep, File.write, SymFile.write]
  all_goals first | (split <;> simp_all only [Expr.eval]) | simp_all only

theorem symRun_correct (input f : File) (sf : SymFile) (ops : List ScalarOp)
    (h : Compatible input sf f) : Compatible input (symRun ops sf) (run ops f) := by
  induction ops generalizing f sf with
  | nil => exact h
  | cons op ops ih =>
    exact ih (step f op) (symStep sf op) (symStep_correct input f sf op h)

theorem run_regs (ops : List ScalarOp) (f : File) (r : Reg) :
    (run ops f).regs r = ((symRun ops symInitial).regs r).eval f :=
  (symRun_correct f f symInitial ops ⟨fun _ => rfl, fun _ => rfl⟩).1 r

end VG.Proof.Sha3.AArch64.Scalar
