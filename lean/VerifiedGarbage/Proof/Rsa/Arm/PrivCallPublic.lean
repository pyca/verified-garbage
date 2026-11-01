module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtPre
public import VerifiedGarbage.Proof.Rsa.Arm.PrivPcPre
public import VerifiedGarbage.Proof.Rsa.Arm.PrivPdPre
public import VerifiedGarbage.Proof.Rsa.Contract


/-! # Public call arguments agree when the key and buffer geometry agree -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

theorem crtCall_pub {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} {s t : State}
    (hs : PrivContext g bs1 s) (ht : PrivContext g bs2 t) (as : CrtArgs g s) (argT : CrtArgs g t)
    (nb : bs1 0 = bs2 0) :
    (Proof.Rsa.privateCrtContract abi 56).pub
      (s.callEntry.withRegions (crtRd g) (crtWr g)) (t.callEntry.withRegions (crtRd g) (crtWr g)) := by
  sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  have sa := fun {j} (hj : j < 14) => crtArgs_stack hs as hj
  have ta := fun {j} (hj : j < 14) => crtArgs_stack ht argT hj
  simp only [hs.sp, ht.sp, as.output, argT.output, as.outputLength, argT.outputLength, as.modulus, argT.modulus, as.length, argT.length,
    sa (by decide : 0 < 14), ta (by decide : 0 < 14), sa (by decide : 2 < 14), ta (by decide : 2 < 14),
    sa (by decide : 3 < 14), ta (by decide : 3 < 14), sa (by decide : 4 < 14), ta (by decide : 4 < 14),
    sa (by decide : 5 < 14), ta (by decide : 5 < 14), sa (by decide : 6 < 14), ta (by decide : 6 < 14),
    sa (by decide : 8 < 14), ta (by decide : 8 < 14), sa (by decide : 10 < 14), ta (by decide : 10 < 14),
    sa (by decide : 12 < 14), ta (by decide : 12 < 14), sa (by decide : 13 < 14), ta (by decide : 13 < 14),
    sa (by decide : 1 < 14), ta (by decide : 1 < 14), sa (by decide : 7 < 14), ta (by decide : 7 < 14),
    sa (by decide : 9 < 14), ta (by decide : 9 < 14), sa (by decide : 11 < 14), ta (by decide : 11 < 14),
    true_and, and_true]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hs.valid.maxLength; omega : g.length < 2 ^ 32)]
  have bytes : Spec.Rsa.bytesAt s.mem ((g.sources 0).setWidth 64) g.length =
      Spec.Rsa.bytesAt t.mem ((g.sources 0).setWidth 64) g.length :=
    (hs.sources 0).bytes.trans (nb.trans (ht.sources 0).bytes.symm)
  rw [bytes]
theorem pcCall_pub {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} {s t : State}
    (hs : PrivContext g bs1 s) (ht : PrivContext g bs2 t) (argsS : PcArgs g s) (argsT : PcArgs g t)
    (nb : bs1 0 = bs2 0) :
    (Spec.Rsa.publicPrecomputeContract abi 56).pub
      (s.callEntry.withRegions (pcRd g) (pcWr g)) (t.callEntry.withRegions (pcRd g) (pcWr g)) := by
  sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  have sa := pcArgs_stack hs argsS
  have ta := pcArgs_stack ht argsT
  simp only [hs.sp, ht.sp, argsS.output, argsT.output, argsS.outputLength, argsT.outputLength,
    argsS.modulus, argsT.modulus, argsS.length, argsT.length, sa.1, ta.1, sa.2, ta.2, true_and, and_true]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hs.valid.maxLength; omega : g.length < 2 ^ 32)]
  have bytes : Spec.Rsa.bytesAt s.mem ((g.sources 0).setWidth 64) g.length =
      Spec.Rsa.bytesAt t.mem ((g.sources 0).setWidth 64) g.length :=
    (hs.sources 0).bytes.trans (nb.trans (ht.sources 0).bytes.symm)
  rw [bytes]

theorem pdCall_pub {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} {s t : State}
    (hs : PrivContext g bs1 s) (ht : PrivContext g bs2 t) (argsS : PdArgs g s) (argsT : PdArgs g t)
    (eb : bs1 1 = bs2 1)
    (pre : Spec.Rsa.wordsAt s.mem (State.addr g.precomputation) (2 * Spec.Rsa.modulusWords g.length) =
      Spec.Rsa.wordsAt t.mem (State.addr g.precomputation) (2 * Spec.Rsa.modulusWords g.length)) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pub
      (s.callEntry.withRegions (pdRd g) (pdWr g)) (t.callEntry.withRegions (pdRd g) (pdWr g)) := by
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  have sa := fun {j} (hj : j < 6) => pdArgs_stack hs argsS hj
  have ta := fun {j} (hj : j < 6) => pdArgs_stack ht argsT hj
  simp only [hs.sp, ht.sp, argsS.output, argsT.output, argsS.outputLength, argsT.outputLength,
    argsS.precomputation, argsT.precomputation, argsS.precomputationLength, argsT.precomputationLength,
    sa (by decide : 0 < 6), ta (by decide : 0 < 6), sa (by decide : 1 < 6), ta (by decide : 1 < 6),
    sa (by decide : 2 < 6), ta (by decide : 2 < 6), sa (by decide : 3 < 6), ta (by decide : 3 < 6),
    sa (by decide : 4 < 6), ta (by decide : 4 < 6), sa (by decide : 5 < 6), ta (by decide : 5 < 6),
    pdArgument, true_and, and_true]
  have ef : g.exponentLength < 2 ^ 32 := by have := hs.valid.exponentFits; have := hs.valid.maxLength; omega
  have pf : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := hs.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ef, Nat.mod_eq_of_lt pf]
  have bytes : Spec.Rsa.bytesAt s.mem ((g.sources 1).setWidth 64) g.exponentLength =
      Spec.Rsa.bytesAt t.mem ((g.sources 1).setWidth 64) g.exponentLength :=
    (hs.sources 1).bytes.trans (eb.trans (ht.sources 1).bytes.symm)
  change Spec.Rsa.wordsAt s.mem (g.precomputation.setWidth 64) (2 * Spec.Rsa.modulusWords g.length) =
    Spec.Rsa.wordsAt t.mem (g.precomputation.setWidth 64) (2 * Spec.Rsa.modulusWords g.length) at pre
  rw [bytes, pre]
end VG.Proof.Rsa.Arm
