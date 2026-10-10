import VerifiedGarbage.Proof.X448.AArch64.Footprint
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Impl.X448.AArch64.Fast

/-!
# X448 on AArch64: the footprints of the field operations, for any slots

Untrusted: everything here is checked by Lean. Each field operation's code
(and the AdvSIMD pair of products, `Neon.mul2`) is, for any slots, its code at
the probe slots `P 0`, `P 1`, … with its offsets moved (`*_reloc`, checked by
the kernel once for any slots), and its code at the probe slots is within a
bound (`*_bnd`, checked once by evaluation): so its code at any slots is
within the bound moved to them (`*_in`, `op_in`, `codeOf_in`), and the
independence of two interleaved streams needs only their bounds'
(`indeps_of_bnd`), whatever the code.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64 VG.AArch64.Interleave
open VG.Impl.Curve448.AArch64
open VG.Impl.X448.AArch64.Fast (Op codeOf fmul)

/-- The probe slots, a window `W` apart, above every offset the code uses. -/
def P (k : Nat) : Nat := 8192 + 4096 * k

/-! ## Bounds at the probe slots -/

def sqrB : Bnd := ⟨267644925, 267644917, 0, 0, true, true, [(3648, 72), (P 0, 64), (P 1, 64)],
  [(3648, 72), (P 0, 64)]⟩
def mulB : Bnd := ⟨267644925, 267644917, 0, 0, true, true,
  [(3584, 64), (P 0, 64), (P 1, 64), (P 2, 64)], [(3584, 64), (P 0, 64)]⟩
def subB : Bnd := ⟨61, 53, 0, 0, false, false, [(P 1, 64), (P 2, 64)], [(P 0, 64)]⟩
def addSubB : Bnd := ⟨253, 245, 0, 0, false, false, [(P 2, 64), (P 3, 64)], [(P 0, 64), (P 1, 64)]⟩
def smallB : Bnd := ⟨15986685, 15986677, 0, 0, false, false, [(P 1, 64), (P 2, 64)], [(P 0, 64)]⟩
def copyB : Bnd := ⟨24, 16, 0, 0, false, false, [(P 1, 64)], [(P 0, 64)]⟩
def mul2B : Bnd := ⟨4104, 0, 4294967295, 4294967295, false, false,
  [(4096, 624), (P 1, 64), (P 2, 64), (P 4, 64), (P 5, 64)], [(4096, 624), (P 0, 64), (P 3, 64)]⟩

theorem sqr_bnd : (Fast.sqr (P 0) (P 1)).all (fpIn sqrB) = true := by decide +kernel
theorem mul_bnd : (Fast.mul (P 0) (P 1) (P 2)).all (fpIn mulB) = true := by decide +kernel
theorem sub_bnd : (Fast.sub (P 0) (P 1) (P 2)).all (fpIn subB) = true := by decide +kernel
theorem addSub_bnd : (Fast.addSub (P 0) (P 1) (P 2) (P 3)).all (fpIn addSubB) = true := by decide +kernel
theorem small_bnd : (Fast.small (P 0) (P 1) (P 2)).all (fpIn smallB) = true := by decide +kernel
theorem copy_bnd : (VG.Impl.Curve448.AArch64.copy (P 0) (P 1)).all (fpIn copyB) = true := by decide +kernel
theorem mul2_bnd : (Neon.mul2 (P 0) (P 1) (P 2) (P 3) (P 4) (P 5)).all (fpIn mul2B) = true := by
  decide +kernel

theorem sep2 : sepB [P 0, P 1] = true := by decide
theorem sep3 : sepB [P 0, P 1, P 2] = true := by decide
theorem sep4 : sepB [P 0, P 1, P 2, P 3] = true := by decide
theorem sep6 : sepB [P 0, P 1, P 2, P 3, P 4, P 5] = true := by decide
theorem sqr_al : (sqrB.rd ++ sqrB.wr).all (alignedB [P 0, P 1]) = true := by decide
theorem mul_al : (mulB.rd ++ mulB.wr).all (alignedB [P 0, P 1, P 2]) = true := by decide
theorem sub_al : (subB.rd ++ subB.wr).all (alignedB [P 0, P 1, P 2]) = true := by decide
theorem addSub_al : (addSubB.rd ++ addSubB.wr).all (alignedB [P 0, P 1, P 2, P 3]) = true := by decide
theorem small_al : (smallB.rd ++ smallB.wr).all (alignedB [P 0, P 1, P 2]) = true := by decide
theorem copy_al : (copyB.rd ++ copyB.wr).all (alignedB [P 0, P 1]) = true := by decide
theorem mul2_al : (mul2B.rd ++ mul2B.wr).all (alignedB [P 0, P 1, P 2, P 3, P 4, P 5]) = true := by decide

/-! ## Any slots -/

theorem sqr_reloc (o a : Nat) : Fast.sqr o a = (Fast.sqr (P 0) (P 1)).map (relocI [(P 0, o), (P 1, a)]) := by
  kernel_rfl
theorem mul_reloc (o a b : Nat) :
    Fast.mul o a b = (Fast.mul (P 0) (P 1) (P 2)).map (relocI [(P 0, o), (P 1, a), (P 2, b)]) := by
  kernel_rfl
theorem sub_reloc (o a b : Nat) :
    Fast.sub o a b = (Fast.sub (P 0) (P 1) (P 2)).map (relocI [(P 0, o), (P 1, a), (P 2, b)]) := by
  kernel_rfl
theorem addSub_reloc (o₁ o₂ a b : Nat) : Fast.addSub o₁ o₂ a b =
    (Fast.addSub (P 0) (P 1) (P 2) (P 3)).map (relocI [(P 0, o₁), (P 1, o₂), (P 2, a), (P 3, b)]) := by
  kernel_rfl
theorem small_reloc (o a e : Nat) :
    Fast.small o a e = (Fast.small (P 0) (P 1) (P 2)).map (relocI [(P 0, o), (P 1, a), (P 2, e)]) := by
  kernel_rfl
theorem copy_reloc (o a : Nat) : VG.Impl.Curve448.AArch64.copy o a =
    (VG.Impl.Curve448.AArch64.copy (P 0) (P 1)).map (relocI [(P 0, o), (P 1, a)]) := by
  kernel_rfl
theorem mul2_reloc (o₁ a₁ b₁ o₂ a₂ b₂ : Nat) : Neon.mul2 o₁ a₁ b₁ o₂ a₂ b₂ =
    (Neon.mul2 (P 0) (P 1) (P 2) (P 3) (P 4) (P 5)).map
      (relocI [(P 0, o₁), (P 1, a₁), (P 2, b₁), (P 3, o₂), (P 4, a₂), (P 5, b₂)]) := by
  kernel_rfl

/-- The bound of a field operation at its slots. -/
def opBnd : Op → Bnd
  | .mul o a b => if a = b then sqrB.reloc [(P 0, o), (P 1, a)] else mulB.reloc [(P 0, o), (P 1, a), (P 2, b)]
  | .sub o a b => subB.reloc [(P 0, o), (P 1, a), (P 2, b)]
  | .addSub o₁ o₂ a b => addSubB.reloc [(P 0, o₁), (P 1, o₂), (P 2, a), (P 3, b)]
  | .small o a e => smallB.reloc [(P 0, o), (P 1, a), (P 2, e)]
  | .copy o a => copyB.reloc [(P 0, o), (P 1, a)]

theorem op_in : ∀ (op : Op), ∀ x ∈ op.code, fpIn (opBnd op) x = true
  | .mul o a b => by
    simp only [Impl.X448.AArch64.Fast.Op.code, fmul, opBnd]
    split
    · rename_i h
      subst h
      exact fpIn_relocs (sqr_reloc o a) sqr_bnd rfl sep2 sqr_al
    · exact fpIn_relocs (mul_reloc o a b) mul_bnd rfl sep3 mul_al
  | .sub o a b => fpIn_relocs (sub_reloc o a b) sub_bnd rfl sep3 sub_al
  | .addSub o₁ o₂ a b => fpIn_relocs (addSub_reloc o₁ o₂ a b) addSub_bnd rfl sep4 addSub_al
  | .small o a e => fpIn_relocs (small_reloc o a e) small_bnd rfl sep3 small_al
  | .copy o a => fpIn_relocs (copy_reloc o a) copy_bnd rfl sep2 copy_al

/-- The bound of the code of field operations. -/
def opsBnd : List Op → Bnd
  | [] => ⟨0, 0, 0, 0, false, false, [], []⟩
  | op :: l => (opBnd op).union (opsBnd l)

theorem codeOf_in : ∀ (l : List Op), ∀ x ∈ codeOf l, fpIn (opsBnd l) x = true
  | [] => fun _ h => by cases h
  | op :: l => fun x hx => by
    simp only [codeOf, List.flatMap_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · exact fpIn_union_left (op_in op x hx)
    · exact fpIn_union_right (codeOf_in l x hx)

/-- The bound of a pair of products in AdvSIMD at its slots. -/
def mul2Bnd (o₁ a₁ b₁ o₂ a₂ b₂ : Nat) : Bnd :=
  mul2B.reloc [(P 0, o₁), (P 1, a₁), (P 2, b₁), (P 3, o₂), (P 4, a₂), (P 5, b₂)]

theorem mul2_in (o₁ a₁ b₁ o₂ a₂ b₂ : Nat) :
    ∀ x ∈ Neon.mul2 o₁ a₁ b₁ o₂ a₂ b₂, fpIn (mul2Bnd o₁ a₁ b₁ o₂ a₂ b₂) x = true :=
  fpIn_relocs (mul2_reloc o₁ a₁ b₁ o₂ a₂ b₂) mul2_bnd rfl sep6 mul2_al

/-- Field operations interleaved with a pair of products in AdvSIMD are independent if their
bounds are. -/
theorem indeps_ops_mul2 (l : List Op) (o₁ a₁ b₁ o₂ a₂ b₂ : Nat)
    (h : (opsBnd l).toFp.indep (mul2Bnd o₁ a₁ b₁ o₂ a₂ b₂).toFp = true) :
    Indeps (codeOf l) (Neon.mul2 o₁ a₁ b₁ o₂ a₂ b₂) :=
  indeps_of_bnd (codeOf_in l) (mul2_in o₁ a₁ b₁ o₂ a₂ b₂) h

end VG.Proof.X448.AArch64.Fast
