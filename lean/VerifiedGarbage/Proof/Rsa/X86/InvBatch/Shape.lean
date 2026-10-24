module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape

/-! # Stack-pointer safety of the batched GCD and inversion kernels

For every width, from the generators: no instruction they emit writes `esp`,
whatever its displacements. -/

@[expose] public section
namespace VG.Proof.Rsa.X86.BatchShape
open VG VG.X86 VG.Proof.Mont.X86.StaticSquare
open VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass.X86.Inv

theorem copy_noSp : ∀ k o a, (VG.Impl.Weierstrass.X86.copy k o a).all noSp = true
  | 0, _, _ => rfl
  | k+1, o, a => by rw [VG.Impl.Weierstrass.X86.copy, List.all_append, copy_noSp k]; rfl

theorem sel_noSp : ∀ k o a b, (VG.Impl.Weierstrass.X86.sel k o a b).all noSp = true
  | 0, _, _, _ => rfl
  | k+1, o, a, b => by rw [VG.Impl.Weierstrass.X86.sel, List.all_append, sel_noSp k]; rfl

theorem maskCopy_noSp : ∀ k o a, (maskCopy k o a).all noSp = true
  | 0, _, _ => rfl
  | k+1, o, a => by rw [maskCopy, List.all_append, maskCopy_noSp k]; rfl

theorem all_const_true {α : Type} (l : List α) : l.all (fun _ => true) = true :=
  List.all_eq_true.mpr fun _ _ => rfl

theorem all_range_true {n : Nat} {f : Nat → Bool} (h : ∀ j, f j = true) : (List.range n).all f = true :=
  List.all_eq_true.mpr fun j _ => h j

theorem noSp_store (a : MemOp) (r : Reg) : noSp (.store a r) = true := rfl
theorem mulStep_noSp (acc b j : Nat) : (mulStep acc b j).all noSp = true := rfl
theorem shrStep_noSp (d s j : Nat) : (shrStep d s j).all noSp = true := rfl

theorem zeros_noSp (acc k : Nat) : (zeros acc k).all noSp = true := by
  simp only [zeros, List.all_cons, List.all_map, Function.comp_def, noSp_store, all_const_true]; rfl

theorem subInPlace_noSp (d s n : Nat) : (subInPlace d s n).all noSp = true := by
  rw [subInPlace, List.all_flatMap, List.all_eq_true]; intro _ _; rfl

theorem addInPlace_noSp (d s n : Nat) : (addInPlace d s n).all noSp = true := by
  rw [addInPlace, List.all_flatMap, List.all_eq_true]; intro _ _; rfl

theorem mulRow_noSp (acc b N : Nat) : (mulRow acc b N).all noSp = true := by
  simp only [mulRow, List.cons_append, List.all_cons, List.all_append, List.all_flatMap, mulStep_noSp,
    all_const_true]; rfl

theorem rowAdd_noSp (c acc s n : Nat) : (rowAdd c acc s n).all noSp = true := by
  rw [rowAdd, List.all_append, mulRow_noSp]; rfl

theorem correction_noSp (c acc s t n : Nat) : (correction c acc s t n).all noSp = true := by
  rw [correction, List.all_append, List.all_append, maskCopy_noSp, subInPlace_noSp]; rfl

theorem linear_noSp (u v acc a b t n k : Nat) : (linear u v acc a b t n k).all noSp = true := by
  simp only [linear, linearUnsigned, List.all_append, zeros_noSp, rowAdd_noSp, correction_noSp, Bool.and_self]

theorem shr30_noSp (d s n : Nat) : (shr30 d s n).all noSp = true := by
  simp only [shr30, List.all_append, List.all_flatMap, shrStep_noSp, all_const_true]; rfl

theorem setConst_noSp (n o x : Nat) : (setConst n o x).all noSp = true := by
  rw [setConst, List.all_flatMap, List.all_eq_true]; intro _ _; rfl

theorem wordSteps_noSp (t n : Nat) : (wordSteps t n).allInstrs noSp = true := rfl

theorem gcd_body_noSp (n : Nat) : (Impl.Rsa.X86.GcdBatch.body n).allInstrs noSp = true := by
  rw [Code.allInstrs_eq]
  simp only [Impl.Rsa.X86.GcdBatch.body, Impl.Rsa.X86.GcdBatch.seqs, Impl.Rsa.X86.Keys.seqs, instrs,
    Impl.Rsa.X86.GcdBatch.batch, Impl.Rsa.X86.GcdBatch.init, Impl.Rsa.X86.GcdBatch.start,
    Impl.Rsa.X86.GcdBatch.update, Impl.Rsa.X86.GcdBatch.row, Impl.Rsa.X86.GcdBatch.finish,
    Impl.Rsa.X86.GcdBatch.copyExtend, List.all_append, ← Code.allInstrs_eq,
    copy_noSp, zeros_noSp, maskCopy_noSp, addInPlace_noSp, subInPlace_noSp, linear_noSp, shr30_noSp,
    setConst_noSp, sel_noSp, Bool.and_true, Bool.true_and]
  rfl

theorem csub_noSp (M : VG.Impl.Mont.Mod) (src o : Nat) : (csub M src o).all noSp = true := by
  have d : (diffs M src).all noSp = true := by
    rw [diffs, List.all_flatMap]; exact all_range_true fun _ => rfl
  have e : (selects M src o).all noSp = true := by
    rw [selects, List.all_flatMap]; exact all_range_true fun _ => rfl
  rw [csub, List.all_append, List.all_append, d, e]; rfl

theorem virtualize_noSp (n M : Nat) : (Impl.Rsa.X86.InvBatch.virtualize n M).all noSp = true := by
  have h : (List.range (n-1)).all (noSp ∘ fun j => Instr.alu .or .eax (.mem (sc (M+4*(j+1))))) = true :=
    all_range_true fun _ => rfl
  rw [Impl.Rsa.X86.InvBatch.virtualize, List.all_append, List.all_append, List.all_map, h]; rfl

theorem reduce_noSp (w n out : Nat) : (Impl.Rsa.X86.InvBatch.reduce w n out).all noSp = true := by
  simp only [Impl.Rsa.X86.InvBatch.reduce, Impl.Rsa.X86.InvBatch.reduceLoaded, Impl.Rsa.X86.InvBatch.redSum,
    Impl.Rsa.X86.InvBatch.quo, addIfNeg, List.all_append, zeros_noSp, rowAdd_noSp, maskCopy_noSp,
    addInPlace_noSp, csub_noSp, Bool.and_true]
  rfl

theorem inv_body_noSp (w n : Nat) : (Impl.Rsa.X86.InvBatch.body w n).allInstrs noSp = true := by
  rw [Code.allInstrs_eq]
  simp only [Impl.Rsa.X86.InvBatch.body, Impl.Rsa.X86.InvBatch.seqs, Impl.Rsa.X86.Keys.seqs, instrs,
    Impl.Rsa.X86.InvBatch.init, Impl.Rsa.X86.InvBatch.operands, Impl.Rsa.X86.InvBatch.coefficients,
    Impl.Rsa.X86.InvBatch.inverseSetup, Impl.Rsa.X86.InvBatch.start, Impl.Rsa.X86.InvBatch.update,
    Impl.Rsa.X86.InvBatch.normalize, Impl.Rsa.X86.InvBatch.twice, Impl.Rsa.X86.InvBatch.finish,
    Impl.Rsa.X86.InvBatch.absolute, Impl.Rsa.X86.GcdBatch.copyExtend, List.all_append, ← Code.allInstrs_eq,
    copy_noSp, zeros_noSp, maskCopy_noSp, addInPlace_noSp, subInPlace_noSp, linear_noSp, shr30_noSp,
    setConst_noSp, sel_noSp, csub_noSp, virtualize_noSp, reduce_noSp, Bool.and_true, Bool.true_and]
  rfl

end VG.Proof.Rsa.X86.BatchShape

namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Proof.Mont.X86.StaticSquare

theorem body64_noSp : (Impl.Rsa.X86.InvBatch.body 64 32).allInstrs noSp=true := BatchShape.inv_body_noSp 64 32
theorem body96_noSp : (Impl.Rsa.X86.InvBatch.body 96 48).allInstrs noSp=true := BatchShape.inv_body_noSp 96 48
theorem body128_noSp : (Impl.Rsa.X86.InvBatch.body 128 64).allInstrs noSp=true := BatchShape.inv_body_noSp 128 64

end VG.Proof.Rsa.X86.InvBatch
