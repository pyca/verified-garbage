module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpPhases
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # Native key imports, exports and public dispatch preserve ESP -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyNoSp
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.RsaKeyGen.X86.Key

theorem writePort_noSp (n i : Nat) : NoSp (writePort n i) := NoSp.of_all (by rfl)

theorem writePorts_noSp (n i count : Nat) : NoSp (writePorts n i count) := by
  induction count generalizing i with
  | zero => exact NoSp.of_all (by rfl)
  | succ count ih => exact sequence (writePort_noSp n i) (ih (i + 1))

theorem sized_noSp (n : Nat) : NoSp (sized n) := by
  apply NoSp.of_all
  simp only [sized, clearArrays, loadPrime, loadExponent, writeOutputs, seqs, Code.allInstrs,
    checked (widenCopy _ _ _ _), checked (derive_noSp n), checked (writePorts_noSp _ _ _)]
  rfl

theorem dispatch_noSp (choices : List Nat) : NoSp (dispatch choices) := by
  induction choices with
  | nil => exact NoSp.of_all (by rfl)
  | cons w rest ih =>
    apply NoSp.of_all
    simp only [dispatch, Code.allInstrs, checked (sized_noSp _), checked ih]
    rfl

theorem body_noSp : NoSp body := by
  apply NoSp.of_all
  simp only [body, Code.allInstrs, checked (dispatch_noSp widths)]
  rfl

theorem code_noSp : NoSp code := by
  apply NoSp.of_all
  simp only [code, Code.allInstrs, checked body_noSp]
  rfl

end VG.Proof.RsaKeyGen.X86.KeyNoSp
