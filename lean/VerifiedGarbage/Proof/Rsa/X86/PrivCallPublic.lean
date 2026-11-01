module
public import VerifiedGarbage.Proof.Rsa.X86.PrivCrtPre
public import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputePre
public import VerifiedGarbage.Proof.Rsa.X86.PrivPublicPre

import VerifiedGarbage.Proof.Rsa.X86.PrivCallInput
import VerifiedGarbage.Proof.Rsa.X86.PrivCrtCall
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # Public nested-call observations agree for the same public RSA key -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

theorem crtCall_pub {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} {s t : State}
    (hs : PrivContext g bs1 s) (ht : PrivContext g bs2 t) (argsS : CrtArgs g s) (argsT : CrtArgs g t)
    (nb : bs1 0 = bs2 0) :
    (Proof.Rsa.privateCrtContract abi 96).pub
      (s.callEntry.withRegions (crtRd g) (crtWr g)) (t.callEntry.withRegions (crtRd g) (crtWr g)) := by
  sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes]
  have sa := fun {j} (hj : j < 18) => crtArgs_values hs argsS hj
  have ta := fun {j} (hj : j < 18) => crtArgs_values ht argsT hj
  simp only [hs.sp, ht.sp, sa (by decide : 0 < 18), ta (by decide : 0 < 18),
    sa (by decide : 1 < 18), ta (by decide : 1 < 18),
    sa (by decide : 2 < 18), ta (by decide : 2 < 18),
    sa (by decide : 3 < 18), ta (by decide : 3 < 18),
    sa (by decide : 4 < 18), ta (by decide : 4 < 18),
    sa (by decide : 5 < 18), ta (by decide : 5 < 18),
    sa (by decide : 6 < 18), ta (by decide : 6 < 18),
    sa (by decide : 7 < 18), ta (by decide : 7 < 18),
    sa (by decide : 8 < 18), ta (by decide : 8 < 18),
    sa (by decide : 9 < 18), ta (by decide : 9 < 18),
    sa (by decide : 10 < 18), ta (by decide : 10 < 18),
    sa (by decide : 11 < 18), ta (by decide : 11 < 18),
    sa (by decide : 12 < 18), ta (by decide : 12 < 18),
    sa (by decide : 13 < 18), ta (by decide : 13 < 18),
    sa (by decide : 14 < 18), ta (by decide : 14 < 18),
    sa (by decide : 15 < 18), ta (by decide : 15 < 18),
    sa (by decide : 16 < 18), ta (by decide : 16 < 18),
    sa (by decide : 17 < 18), ta (by decide : 17 < 18),
    crtArgument, PrivGeometry.argument, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_true, ite_false, true_and, and_true]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hs.valid.maxLength; omega : g.length < 2 ^ 32)]
  have bytes : Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 0).setWidth 64) g.length =
      Spec.Rsa.bytesAt t.callEntry.mem ((g.sources 0).setWidth 64) g.length :=
    (hs.callBytes 0).trans (nb.trans (ht.callBytes 0).symm)
  simp only [State.callEntry_mem, hs.sp, ht.sp] at bytes
  rw [bytes]

theorem pcCall_pub {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} {s t : State}
    (hs : PrivContext g bs1 s) (ht : PrivContext g bs2 t) (argsS : Arguments g (pcArgument g) 6 s) (argsT : Arguments g (pcArgument g) 6 t)
    (nb : bs1 0 = bs2 0) :
    (Spec.Rsa.publicPrecomputeContract abi 96).pub
      (s.callEntry.withRegions (pcRd g) (pcWr g)) (t.callEntry.withRegions (pcRd g) (pcWr g)) := by
  sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes]
  have sa := fun {j} (hj : j < 6) => pcArgs_values hs argsS hj
  have ta := fun {j} (hj : j < 6) => pcArgs_values ht argsT hj
  simp only [hs.sp, ht.sp, sa (by decide : 0 < 6), ta (by decide : 0 < 6),
    sa (by decide : 1 < 6), ta (by decide : 1 < 6),
    sa (by decide : 2 < 6), ta (by decide : 2 < 6),
    sa (by decide : 3 < 6), ta (by decide : 3 < 6),
    sa (by decide : 4 < 6), ta (by decide : 4 < 6),
    sa (by decide : 5 < 6), ta (by decide : 5 < 6),
    pcArgument, true_and, and_true]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hs.valid.maxLength; omega : g.length < 2 ^ 32)]
  have bytes : Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 0).setWidth 64) g.length =
      Spec.Rsa.bytesAt t.callEntry.mem ((g.sources 0).setWidth 64) g.length :=
    (hs.callBytes 0).trans (nb.trans (ht.callBytes 0).symm)
  simp only [State.callEntry_mem, hs.sp, ht.sp] at bytes
  rw [bytes]

theorem pdCall_pub {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} {s t : State}
    (hs : PrivContext g bs1 s) (ht : PrivContext g bs2 t) (argsS : Arguments g (pdArgument g) 10 s) (argsT : Arguments g (pdArgument g) 10 t)
    (eb : bs1 1 = bs2 1)
    (pre : Spec.Rsa.wordsAt s.mem (byteAddr g.precomputation) (2 * Spec.Rsa.modulusWords g.length) =
      Spec.Rsa.wordsAt t.mem (byteAddr g.precomputation) (2 * Spec.Rsa.modulusWords g.length)) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 96).pub
      (s.callEntry.withRegions (pdRd g) (pdWr g)) (t.callEntry.withRegions (pdRd g) (pdWr g)) := by
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes]
  have sa := fun {j} (hj : j < 10) => pdArgs_values hs argsS hj
  have ta := fun {j} (hj : j < 10) => pdArgs_values ht argsT hj
  simp only [hs.sp, ht.sp, sa (by decide : 0 < 10), ta (by decide : 0 < 10),
    sa (by decide : 1 < 10), ta (by decide : 1 < 10),
    sa (by decide : 2 < 10), ta (by decide : 2 < 10),
    sa (by decide : 3 < 10), ta (by decide : 3 < 10),
    sa (by decide : 4 < 10), ta (by decide : 4 < 10),
    sa (by decide : 5 < 10), ta (by decide : 5 < 10),
    sa (by decide : 6 < 10), ta (by decide : 6 < 10),
    sa (by decide : 7 < 10), ta (by decide : 7 < 10),
    sa (by decide : 8 < 10), ta (by decide : 8 < 10),
    sa (by decide : 9 < 10), ta (by decide : 9 < 10),
    pdArgument, true_and, and_true]
  have ef : g.exponentLength < 2 ^ 32 := by have := hs.valid.exponentFits; have := hs.valid.maxLength; omega
  have pf : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := hs.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ef, Nat.mod_eq_of_lt pf]
  have bytes : Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 1).setWidth 64) g.exponentLength =
      Spec.Rsa.bytesAt t.callEntry.mem ((g.sources 1).setWidth 64) g.exponentLength :=
    (hs.callBytes 1).trans (eb.trans (ht.callBytes 1).symm)
  have words := hs.callPrecomputation.trans (pre.trans ht.callPrecomputation.symm)
  change Spec.Rsa.wordsAt s.callEntry.mem (g.precomputation.setWidth 64) (2 * Spec.Rsa.modulusWords g.length) =
    Spec.Rsa.wordsAt t.callEntry.mem (g.precomputation.setWidth 64) (2 * Spec.Rsa.modulusWords g.length) at words
  simp only [State.callEntry_mem, hs.sp, ht.sp] at bytes words
  rw [bytes, words]

end VG.Proof.Rsa.X86.PrivChecked
