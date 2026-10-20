module

public import VerifiedGarbage.Impl.Rsa.X86.KeyCheck
public import VerifiedGarbage.Proof.Bignum.X86.CrtStackSafety
import VerifiedGarbage.Proof.Framework.GetElem

/-! # Stack-pointer safety of both key-validation programs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.KeyCheck
open VG.Impl.Bignum.X86 VG.Impl.Mont.X86
open VG.Proof.Bignum.X86.Crt (stackSafe shiftExponent_sp)

theorem loadInputs_sp (n : Nat) (xs : List (Nat × Nat)) :
    (loadInputs n xs).all stackSafe = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [loadInputs, VG.Impl.Rsa.X86.CrtValues.load, loadBE, reverseBytes,
      Code.all]
    rw [ih]
    rfl

theorem sized_sp (full : Bool) (n : Nat) : (sized full n).all stackSafe = true := by
  cases full <;>
    simp only [sized, loads, Bool.false_eq_true, ite_false, ite_true, keyBody, crtBody,
      start, crtChecks, dChecks1, dChecks2, dChecks3, ltA, eqA, divSet, mulA, division,
      VG.Impl.Rsa.X86.Div.code, VG.Impl.Rsa.X86.Div.step,
      VG.Impl.Rsa.X86.Div.shiftArrays, VG.Impl.Rsa.X86.Div.shift, VG.Impl.Rsa.X86.Div.copyWords,
      VG.Impl.Rsa.X86.Div.reduce, mulMod, mulModStep, mulHead, mulTail, addMod,
      List.cons_append, List.nil_append, seqs, copy, eqS, sub3, sel, half,
      Dynamic.zerosW, Dynamic.chainW, Dynamic.selectsW, Dynamic.wordLoop,
      Code.all, List.all_append] <;>
    rw [loadInputs_sp] <;>
    simp only [List.all_cons, shiftExponent_sp] <;> rfl

theorem dispatch_sp (full : Bool) (widths : List Nat) :
    (dispatch full widths).all stackSafe = true := by
  induction widths with
  | nil => rfl
  | cons w rest ih =>
    change true && ((sized full w).all stackSafe && (dispatch full rest).all stackSafe) = true
    rw [sized_sp, ih]
    rfl

theorem code_sp (full : Bool) : (code full).all (fun i => !isa.writesSp i) = true := by
  change (code full).all stackSafe = true
  unfold code body checkExponent valid
  simp only [Code.all]
  rw [dispatch_sp]
  rfl

end VG.Proof.Rsa.X86.KeyCheck
