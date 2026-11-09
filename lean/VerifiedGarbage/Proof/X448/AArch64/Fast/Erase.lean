module

public import VerifiedGarbage.Proof.Framework.AArch64.TaintSplit
public import VerifiedGarbage.Impl.X448.AArch64.Fast
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# Curve448's register-resident field arithmetic on AArch64, erased

Untrusted: everything here is checked by Lean. Without what the analysis does
not read (`Instr.eraseT`, `Proof/Framework/AArch64/TaintSplit.lean`), each
field operation on the working space's slots is the same code whatever its
slots: the constants `mulE`, `sqrE`, … (`Op.code_eraseT`, by the kernel's
evaluation for any slots), whose analysis the kernel then caches.
-/

@[expose] public section

namespace VG.AArch64

open VG.Impl.X448.AArch64.Fast

/-! ## The operations -/

def mulE : List Instr := (Impl.Curve448.AArch64.Fast.mul 0 0 0).map Instr.eraseT
def sqrE : List Instr := (Impl.Curve448.AArch64.Fast.sqr 0 0).map Instr.eraseT
def subE : List Instr := (Impl.Curve448.AArch64.Fast.sub 0 0 0).map Instr.eraseT
def addSubE : List Instr := (Impl.Curve448.AArch64.Fast.addSub 0 0 0 0).map Instr.eraseT
def smallE : List Instr := (Impl.Curve448.AArch64.Fast.small 0 0 0).map Instr.eraseT
def copyE : List Instr := (Impl.Curve448.AArch64.copy 0 0).map Instr.eraseT
/-- An operation's code, erased. -/
def opErased : Op → List Instr
  | .mul _ a b => if a = b then sqrE else mulE
  | .sub .. => subE
  | .addSub .. => addSubE
  | .small .. => smallE
  | .copy .. => copyE

theorem Op.code_eraseT : ∀ op : Op, op.code.map Instr.eraseT = opErased op
  | .mul o a b => by
    simp only [Op.code, opErased, fmul]
    split
    · exact (by kernel_rfl : (Impl.Curve448.AArch64.Fast.sqr o a).map Instr.eraseT = sqrE)
    · exact (by kernel_rfl : (Impl.Curve448.AArch64.Fast.mul o a b).map Instr.eraseT = mulE)
  | .sub o a b => (by kernel_rfl : (Impl.Curve448.AArch64.Fast.sub o a b).map Instr.eraseT = subE)
  | .addSub o₁ o₂ a b =>
    (by kernel_rfl : (Impl.Curve448.AArch64.Fast.addSub o₁ o₂ a b).map Instr.eraseT = addSubE)
  | .small o a e => (by kernel_rfl : (Impl.Curve448.AArch64.Fast.small o a e).map Instr.eraseT = smallE)
  | .copy o a => (by kernel_rfl : (Impl.Curve448.AArch64.copy o a).map Instr.eraseT = copyE)

theorem ops_eraseT : ∀ l : List Op, Code.eraseT (ops l) = piecesProg (l.map opErased)
  | [] => rfl
  | o :: os => by
    simp only [ops, Code.eraseT, Op.code_eraseT, ops_eraseT os, List.map_cons, piecesProg]

theorem sqn_eraseT (o n : Nat) : Code.eraseT (sqn o n) =
    .seq (.block ([Instr.movz .x .x19 0 0] : List Instr))
      (.loop (.block (sqrE ++ ([.subImm .x .x19 .x19 0] : List Instr))) (.nonzero .x .x19)) := by
  have e := Op.code_eraseT (.mul o o o)
  simp only [Op.code, fmul, ite_true, opErased] at e
  simp only [sqn, Code.eraseT, List.map_append, e, List.map_cons, List.map_nil,
    Instr.eraseT]

end VG.AArch64
