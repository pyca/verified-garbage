import VerifiedGarbage.Proof.Framework.AArch64.TaintSplit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Impl.X448.AArch64.Base

/-!
# Curve448's register-resident field arithmetic on AArch64, erased

Untrusted: everything here is checked by Lean. Without what the analysis does
not read (`Instr.eraseT`, `Proof/Framework/AArch64/TaintSplit.lean`), each
field operation on the working space's slots is the same code whatever its
slots: the constants `mulE`, `sqrE`, … (`Op.code_eraseT`, by the kernel's
evaluation for any slots), whose analysis the kernel then caches.
-/

namespace VG.AArch64

open VG.Impl.X448.AArch64.Fast

/-! ## The operations -/

def mulE : List Instr := (Impl.Curve448.AArch64.Fast.mul 0 0 0).map Instr.eraseT
def sqrE : List Instr := (Impl.Curve448.AArch64.Fast.sqr 0 0).map Instr.eraseT
def subE : List Instr := (Impl.Curve448.AArch64.Fast.sub 0 0 0).map Instr.eraseT
def addSubE : List Instr := (Impl.Curve448.AArch64.Fast.addSub 0 0 0 0).map Instr.eraseT
def smallE : List Instr := (Impl.Curve448.AArch64.Fast.small 0 0 0).map Instr.eraseT
def copyE : List Instr := (Impl.Curve448.AArch64.copy 0 0).map Instr.eraseT
def mul2E : List Instr := (Impl.Curve448.AArch64.Neon.mul2 0 0 0 0 0 0).map Instr.eraseT

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

theorem mul2_eraseT (o₁ a₁ b₁ o₂ a₂ b₂ : Nat) :
    (Impl.Curve448.AArch64.Neon.mul2 o₁ a₁ b₁ o₂ a₂ b₂).map Instr.eraseT = mul2E := by
  kernel_rfl

theorem codeOf_eraseT (l : List Op) : (codeOf l).map Instr.eraseT = (l.map opErased).flatten := by
  rw [codeOf, List.map_flatMap, List.flatMap_def]
  exact congrArg List.flatten (List.map_congr_left fun op _ => Op.code_eraseT op)

theorem ops_eraseT : ∀ l : List Op, Code.eraseT (ops l) = piecesProg (l.map opErased)
  | [] => rfl
  | o :: os => by
    simp only [ops, Code.eraseT, Op.code_eraseT, ops_eraseT os, List.map_cons, piecesProg]

theorem weaveGo_map (g : Instr → Instr) (n m : Nat) :
    ∀ f i j (a b : List Instr), (weaveGo n m f i j a b).map g = weaveGo n m f i j (a.map g) (b.map g)
  | 0, _, _, a, b => by simp only [weaveGo, List.map_append]
  | _ + 1, _, _, [], b => by simp only [weaveGo, List.map_nil]
  | _ + 1, _, _, x :: a, [] => by simp only [weaveGo, List.map_cons, List.map_nil]
  | f + 1, i, j, x :: a, y :: b => by
    simp only [weaveGo, List.map_cons]
    split
    · rw [List.map_cons, weaveGo_map g n m f _ _ a (y :: b), List.map_cons]
    · rw [List.map_cons, weaveGo_map g n m f _ _ (x :: a) b, List.map_cons]

theorem weave_map (g : Instr → Instr) (a b : List Instr) : (weave a b).map g = weave (a.map g) (b.map g) := by
  simp only [weave, weaveGo_map, List.length_map]

theorem sqn_eraseT (o n : Nat) : Code.eraseT (sqn o n) =
    .seq (.block ([Instr.movz .x .x19 0 0] : List Instr))
      (.loop (.block (sqrE ++ ([.subImm .x .x19 .x19 0] : List Instr))) (.nonzero .x .x19)) := by
  have e := Op.code_eraseT (.mul o o o)
  simp only [Op.code, fmul, ite_true, opErased] at e
  simp only [sqn, Code.eraseT, List.map_append, e, List.map_cons, List.map_nil,
    Instr.eraseT]

end VG.AArch64
