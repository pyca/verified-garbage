module

public import VerifiedGarbage.Impl.Rsa.X86.Recover
public import VerifiedGarbage.Proof.Rsa.X86.CvStackSafety

/-! # Stack-pointer safety throughout prime recovery -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.Recover
open VG.Impl.Bignum.X86 VG.Impl.Mont.X86
open VG.Proof.Bignum.X86.Crt (stackSafe shiftExponent_sp shiftUp_sp sub_sp)

theorem sized_sp (n : Nat) : (sized n).all stackSafe = true := by
  simp only [sized, numbers, loads, load, prod, rest, halving, halfInit, halfBody,
    mont, setupR2, mmul, clrTop, candLoop, candBody, candExp, candSet, alignStart, alignCount,
    alignBody, table, powers, windowCount, windowBody, square, windowTop, scan, windowIs,
    candSquare, sqBody, fin, finY, factors, gcdSet, divSet, order, stores,
    VG.Impl.Rsa.X86.CrtValues.store,
    VG.Impl.Rsa.X86.Div.code, VG.Impl.Rsa.X86.Div.step,
    VG.Impl.Rsa.X86.Div.shiftArrays, VG.Impl.Rsa.X86.Div.shift, VG.Impl.Rsa.X86.Div.copyWords,
    VG.Impl.Rsa.X86.Div.reduce, mulMod, mulModStep, mulHead, mulTail, addMod,
    seqs, copy, eqAt, eqS, sub3, sel, half, inverse,
    loadBE, storeBE, reverseBytes,
    Dynamic.powerTwo, Dynamic.doubleLoop, Dynamic.doubleStep, Dynamic.one,
    Dynamic.mul, Dynamic.row, Dynamic.mulRowW, Dynamic.zerosW, Dynamic.selectsW,
    Dynamic.chainW, Dynamic.csubW, Dynamic.addW, Dynamic.wordLoop,
    Code.all, List.all_append, shiftExponent_sp, shiftUp_sp]
  rw [VG.Proof.Rsa.X86.CrtValues.invStep_sp, VG.Proof.Rsa.X86.CrtValues.invStep_sp]
  rfl

theorem dispatch_sp (widths : List Nat) : (dispatch widths).all stackSafe = true := by
  induction widths with
  | nil => rfl
  | cons w rest ih =>
    change true && ((sized w).all stackSafe && (dispatch rest).all stackSafe) = true
    rw [sized_sp, ih]
    rfl

theorem code_sp : code.all (fun i => !isa.writesSp i) = true := by
  change code.all stackSafe = true
  unfold code body valid
  simp only [Code.all]
  rw [dispatch_sp]
  rfl

end VG.Proof.Rsa.X86.Recover
