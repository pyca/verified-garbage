module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicPre

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # The nested public operation observes only the shared exponent and key words -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86

theorem Context.words_equal {g : Geometry} {bs : Fin 5 → List Byte} {s t : State}
    (hs : Context g bs s) (ht : Context g bs t) :
    Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 4)) g.preLength =
      Spec.Rsa.wordsAt t.mem (byteAddr (g.sources 4)) g.preLength := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left ?_
  intro i hi
  have hi := List.mem_range.mp hi
  apply Mem.readW_congr
  intro j hj
  rw [Offset.add_add]
  have bound : 8 * i + j < (bs 4).length := by
    rw [(hs.sources 4).length]
    change 8 * i + j < 8 * g.preLength
    omega
  rw [(hs.sources 4).byte _ bound, (ht.sources 4).byte _ bound]

theorem publicCall_pub {g : Geometry} {bs : Fin 5 → List Byte} {s t : State}
    (hs : Context g bs s) (ht : Context g bs t)
    (argsS : Arguments g (publicArgument g) 10 s) (argsT : Arguments g (publicArgument g) 10 t) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 96).pub
      (s.callEntry.withRegions (publicRd g) (publicWr g)) (t.callEntry.withRegions (publicRd g) (publicWr g)) := by
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes]
  have sa := fun {j} (hj : j < 10) => publicArgs_values hs argsS hj
  have ta := fun {j} (hj : j < 10) => publicArgs_values ht argsT hj
  simp only [hs.sp, ht.sp, sa (by decide : 0 < 10), ta (by decide : 0 < 10),
    sa (by decide : 1 < 10), ta (by decide : 1 < 10), sa (by decide : 2 < 10), ta (by decide : 2 < 10),
    sa (by decide : 3 < 10), ta (by decide : 3 < 10), sa (by decide : 4 < 10), ta (by decide : 4 < 10),
    sa (by decide : 5 < 10), ta (by decide : 5 < 10), sa (by decide : 6 < 10), ta (by decide : 6 < 10),
    sa (by decide : 7 < 10), ta (by decide : 7 < 10), sa (by decide : 8 < 10), ta (by decide : 8 < 10),
    sa (by decide : 9 < 10), ta (by decide : 9 < 10), publicArgument, true_and, and_true]
  have ef : g.exponentLength < 2 ^ 32 := by have := hs.valid.exponentFits; have := hs.valid.maxLength; omega
  have pf : g.preLength < 2 ^ 32 := by
    have fit := hs.valid.sourceFits 4
    change (g.sources 4).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
    omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ef, Nat.mod_eq_of_lt pf]
  have bytes := (hs.callBytes 1).trans (ht.callBytes 1).symm
  have words := hs.callWords.trans ((hs.words_equal ht).trans ht.callWords.symm)
  change Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 1).setWidth 64) g.exponentLength = _ at bytes
  simp only [State.callEntry_mem, hs.sp, ht.sp] at bytes words
  simp only [byteAddr] at words
  rw [bytes, words]
  rfl

end VG.Proof.RsaPkcs1Sig.X86.Ver
