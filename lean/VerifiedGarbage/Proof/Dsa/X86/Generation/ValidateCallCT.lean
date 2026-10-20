module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateLayout
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidatePre

/-! # The domain checker is called with equal public arguments and packed domain bytes -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

structure ValidateCallAt (G : GenerationGeometry) (bytes : List Byte) (s : State) : Prop where
  sp : s.gpr .esp = G.frame - 24#32
  slots : ValidateSlots G s
  read : Covers (validateRd G ++ validateWr G) (s.rd ++ s.wr)
  write : Covers (validateWr G) s.wr
  bytes : Spec.Rsa.bytesAt s.mem (off G.base packed) (2 * G.pLen + G.qLen) = bytes

theorem validateCall_public {G : GenerationGeometry} {bytes : List Byte} {s t : State}
    (R : ValidateCallAt G bytes s) (S : ValidateCallAt G bytes t) :
    (Spec.Dsa.checkParametersContract abi 32).pub
      (s.callEntry.withRegions (validateRd G) (validateWr G))
      (t.callEntry.withRegions (validateRd G) (validateWr G)) := by
  sig_pub [Spec.Dsa.checkParametersContract, Spec.Dsa.checkParametersSig, abi, argSlots, argVal, argBytes]
  simp only [validate_arg R.sp R.slots (validateRd G) (validateWr G) (show 0 < 6 by decide),
    validate_arg R.sp R.slots (validateRd G) (validateWr G) (show 1 < 6 by decide),
    validate_arg R.sp R.slots (validateRd G) (validateWr G) (show 2 < 6 by decide),
    validate_arg R.sp R.slots (validateRd G) (validateWr G) (show 3 < 6 by decide),
    validate_arg R.sp R.slots (validateRd G) (validateWr G) (show 4 < 6 by decide),
    validate_arg R.sp R.slots (validateRd G) (validateWr G) (show 5 < 6 by decide),
    validate_arg S.sp S.slots (validateRd G) (validateWr G) (show 0 < 6 by decide),
    validate_arg S.sp S.slots (validateRd G) (validateWr G) (show 1 < 6 by decide),
    validate_arg S.sp S.slots (validateRd G) (validateWr G) (show 2 < 6 by decide),
    validate_arg S.sp S.slots (validateRd G) (validateWr G) (show 3 < 6 by decide),
    validate_arg S.sp S.slots (validateRd G) (validateWr G) (show 4 < 6 by decide),
    validate_arg S.sp S.slots (validateRd G) (validateWr G) (show 5 < 6 by decide), validateValue]
  have pw := G.width
  have qw := G.qWidth
  have size : (BitVec.ofNat 32 (2 * G.pLen + G.qLen)).toNat = 2 * G.pLen + G.qLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have first := validateEntry_bytes R.sp
  have second := validateEntry_bytes S.sp
  rw [State.callEntry_mem] at first second
  refine ⟨?_, ?_, by trivial⟩
  · rw [R.sp, S.sp]
  · rw [size, G.pointer_addr (by unfold packed usedBytes domainCheck; omega), first, second, R.bytes, S.bytes]

theorem validateCall_ct (F : KeyRandom.CheckCall.CheckFn) (G : GenerationGeometry) (bytes : List Byte) :
    RelCT isa (Two fun (_ : Unit) => ValidateCallAt G bytes) (.call F.name F.code) (fun _ _ => True) := by
  refine RelCT.call F.verified.1 F.verified.2.1 (validateRd G) (validateWr G) ?_
  rintro s t ⟨_, R, S⟩
  exact ⟨validate_pre R.sp R.slots, validate_pre S.sp S.slots, validateCall_public R S,
    R.read, R.write, S.read, S.write, R.sp.trans S.sp.symm⟩
end VG.Proof.Dsa.X86.Generation
