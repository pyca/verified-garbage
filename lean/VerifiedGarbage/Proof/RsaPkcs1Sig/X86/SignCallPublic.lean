module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivatePre

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateCall

/-! # Public nested-call observations agree for the same public RSA key -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86

theorem privateCall_pub {g : Geometry} {bs1 bs2 : Fin 8 → List Byte} {s t : State}
    (hs : Context g bs1 s) (ht : Context g bs2 t) (argsS : PrivateArgs g s) (argsT : PrivateArgs g t)
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    (Spec.Rsa.privateCheckedContract abi VG.Proof.Rsa.X86.PrivChecked.stackBytes).pub
      (s.callEntry.withRegions (privateRd g) (privateWr g)) (t.callEntry.withRegions (privateRd g) (privateWr g)) := by
  sig_pub [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes]
  have sa := fun {j} (hj : j < 20) => privateArgs_values hs argsS hj
  have ta := fun {j} (hj : j < 20) => privateArgs_values ht argsT hj
  simp only [hs.sp, ht.sp, sa (by decide : 0 < 20), ta (by decide : 0 < 20),
    sa (by decide : 1 < 20), ta (by decide : 1 < 20),
    sa (by decide : 2 < 20), ta (by decide : 2 < 20),
    sa (by decide : 3 < 20), ta (by decide : 3 < 20),
    sa (by decide : 4 < 20), ta (by decide : 4 < 20),
    sa (by decide : 5 < 20), ta (by decide : 5 < 20),
    sa (by decide : 6 < 20), ta (by decide : 6 < 20),
    sa (by decide : 7 < 20), ta (by decide : 7 < 20),
    sa (by decide : 8 < 20), ta (by decide : 8 < 20),
    sa (by decide : 9 < 20), ta (by decide : 9 < 20),
    sa (by decide : 10 < 20), ta (by decide : 10 < 20),
    sa (by decide : 11 < 20), ta (by decide : 11 < 20),
    sa (by decide : 12 < 20), ta (by decide : 12 < 20),
    sa (by decide : 13 < 20), ta (by decide : 13 < 20),
    sa (by decide : 14 < 20), ta (by decide : 14 < 20),
    sa (by decide : 15 < 20), ta (by decide : 15 < 20),
    sa (by decide : 16 < 20), ta (by decide : 16 < 20),
    sa (by decide : 17 < 20), ta (by decide : 17 < 20), sa (by decide : 18 < 20), ta (by decide : 18 < 20),
    sa (by decide : 19 < 20), ta (by decide : 19 < 20),
    privateArgument, Geometry.argument, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_true, ite_false, true_and, and_true]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hs.valid.maxLength; omega : g.length < 2 ^ 32)]
  have ef : g.exponentLength < 2 ^ 32 := by have := hs.valid.exponentFits; have := hs.valid.maxLength; omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ef]
  have bytesN := (hs.callBytes 0).trans (nb.trans (ht.callBytes 0).symm)
  have bytesE := (hs.callBytes 1).trans (eb.trans (ht.callBytes 1).symm)
  change Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 0).setWidth 64) g.length = _ at bytesN
  change Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 1).setWidth 64) g.exponentLength = _ at bytesE
  simp only [State.callEntry_mem, hs.sp, ht.sp] at bytesN bytesE
  rw [bytesN, bytesE]
  rfl

end VG.Proof.RsaPkcs1Sig.X86.Sgn
