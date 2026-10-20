module

public import VerifiedGarbage.Impl.Bignum.X86.CrtFn
import VerifiedGarbage.Proof.Framework.GetElem

/-! # Compositional stack-pointer safety avoids rechecking every dispatched width -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Bignum.X86

def stackSafe (i : Instr) : Bool := !isa.writesSp i

theorem chain_sp (M : Mod) (op op' : AluOp) (out a b : Nat) :
    (chain M op op' out a b).all stackSafe = true := by
  unfold chain
  rw [List.all_flatMap]
  apply List.all_eq_true.mpr
  intro j _
  rfl

theorem masked_sp (M : Mod) : (masked M).all stackSafe = true := by
  unfold masked
  rw [List.all_flatMap]
  apply List.all_eq_true.mpr
  intro j _
  rfl

theorem sub_sp (M : Mod) (acc out a b : Nat) : (sub M acc out a b).all stackSafe = true := by
  simp only [sub, List.all_append, chain_sp, masked_sp]
  rfl

theorem shiftExponent_sp (n out : Nat) : (Dynamic.shiftExponent n out).all stackSafe = true := by
  induction n generalizing out with
  | zero => rfl
  | succ n ih =>
    rw [Dynamic.shiftExponent, List.all_append, ih]
    rfl

theorem sized_sp (n : Nat) : (VG.Impl.Bignum.X86.Crt.sized n).all stackSafe = true := by
  simp only [VG.Impl.Bignum.X86.Crt.sized, VG.Impl.Bignum.X86.Crt.importComponents,
    VG.Impl.Bignum.X86.Crt.importComponent, VG.Impl.Bignum.X86.Crt.validate,
    VG.Impl.Bignum.X86.Crt.compute, VG.Impl.Bignum.X86.Crt.powers,
    VG.Impl.Bignum.X86.Crt.factorPower, VG.Impl.Bignum.X86.Crt.loadPower,
    VG.Impl.Bignum.X86.Crt.coefficient, VG.Impl.Bignum.X86.Crt.loadCoefficient,
    VG.Impl.Bignum.X86.Crt.exportResult, VG.Impl.Bignum.X86.Crt.maskResult,
    VG.Impl.Bignum.X86.Crt.maskOutput, VG.Impl.Bignum.X86.Crt.writeResult,
    loadBE, storeBE, reverseBytes, checkFactorProduct, wideProduct, wideProductRow,
    copyArray, copyPadded, checkedPrimePower, checkedPreparePrime, primePower, preparePrime,
    sanitizeModulus, smallConstant, primeMask, crtCoefficient, reduceOperand, crtRecombine,
    Dynamic.contextSetup, Dynamic.exponentiate, Dynamic.exponentStep, Dynamic.exponentBody,
    Dynamic.exponentProduct, Dynamic.selectProduct, Dynamic.powerTwo, Dynamic.doubleLoop,
    Dynamic.doubleStep, Dynamic.one, Dynamic.mul, Dynamic.row, Dynamic.mulRowW,
    Dynamic.zerosW, Dynamic.selectsW, Dynamic.chainW, Dynamic.csubW, Dynamic.addW, Dynamic.wordLoop,
    VG.Impl.Dsa.X86.lessThan, VG.Impl.Dsa.X86.equal, Code.all, sub_sp, shiftExponent_sp,
    List.all_append]
  rfl

theorem dispatch_sp (widths : List Nat) : (VG.Impl.Bignum.X86.Crt.dispatch widths).all stackSafe = true := by
  induction widths with
  | nil => rfl
  | cons w rest ih =>
    change true && ((VG.Impl.Bignum.X86.Crt.sized w).all stackSafe &&
      (VG.Impl.Bignum.X86.Crt.dispatch rest).all stackSafe) = true
    rw [sized_sp, ih]
    rfl

theorem wrapper_sp (c : Prog isa) (hc : c.all stackSafe = true) :
    (Code.seq (.block VG.Impl.Bignum.X86.Crt.entry)
      (.seq (.seq (.block PublicFn.modulusArgs) (.seq (.block modulusCheck)
        (.ite .e (.seq (.block PublicFn.widthArgs) c) PublicFn.failure)))
        (.block VG.Impl.Bignum.X86.Crt.restore))).all stackSafe = true := by
  simp only [Code.all, hc]
  rfl

theorem code_sp : VG.Impl.Bignum.X86.Crt.code.all (fun i => !isa.writesSp i) = true :=
  wrapper_sp _ (dispatch_sp _)

end VG.Proof.Bignum.X86.Crt
