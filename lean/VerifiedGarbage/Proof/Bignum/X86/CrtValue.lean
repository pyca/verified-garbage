module

public import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
public import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The values of private CRT RSA's arguments, and its specification's result

`componentValue`: the number an argument's bytes encode; `accepted` and
`outputValue`: whether the key and input are accepted, and the CRT result;
`specResult`: the specification's result, by them (`specResult_eq`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86

def componentValue (m : Mem) (args : Nat → BitVec 32) (i : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args i)) (args (i + 1)).toNat)

theorem Inputs.modulus_length {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State}
    (h : Inputs base bytes len args s) : (args 3).toNat = len := by
  rw [h.nLen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.upper; omega)]

theorem Inputs.modulus_bound {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State}
    (h : Inputs base bytes len args s) : componentValue s.mem args 2 < 2 ^ (8 * len) := by
  have B := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) (args 3).toNat)
  simpa only [componentValue, Nat.reduceAdd, VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.pow256_eq,
    h.modulus_length] using B

theorem Inputs.factor_bounds {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State}
    (h : Inputs base bytes len args s)
    (valid : Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true) :
    componentValue s.mem args 2 % 2 = 1 ∧
      componentValue s.mem args 6 < componentValue s.mem args 2 ∧
      componentValue s.mem args 8 < componentValue s.mem args 2 := by
  have H := VG.Proof.Bignum.crt_bounds_of valid h.lower
    (VG.Proof.Bignum.bytesAt_length s.mem (byteAddr (args 6)) (args 7).toNat) h.pShort
    (VG.Proof.Bignum.bytesAt_length s.mem (byteAddr (args 8)) (args 9).toNat) h.qShort
  exact ⟨H.1, H.2.2⟩

def accepted (m : Mem) (args : Nat → BitVec 32) : Prop :=
  componentValue m args 6 * componentValue m args 8 = componentValue m args 2 ∧
    componentValue m args 4 < componentValue m args 2 ∧ componentValue m args 14 < componentValue m args 6

instance (m : Mem) (args : Nat → BitVec 32) : Decidable (accepted m args) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def outputValue (m : Mem) (args : Nat → BitVec 32) : Nat :=
  VG.Proof.Bignum.crtResult (componentValue m args 6) (componentValue m args 8)
    (componentValue m args 10) (componentValue m args 12) (componentValue m args 14) (componentValue m args 4)

def specResult (m : Mem) (args : Nat → BitVec 32) : Option (List Byte) :=
  Spec.Rsa.privateCrt (Spec.Rsa.bytesAt m (byteAddr (args 2)) (args 3).toNat)
    (Spec.Rsa.bytesAt m (byteAddr (args 4)) (args 5).toNat)
    (Spec.Rsa.bytesAt m (byteAddr (args 6)) (args 7).toNat)
    (Spec.Rsa.bytesAt m (byteAddr (args 8)) (args 9).toNat)
    (Spec.Rsa.bytesAt m (byteAddr (args 10)) (args 11).toNat)
    (Spec.Rsa.bytesAt m (byteAddr (args 12)) (args 13).toNat)
    (Spec.Rsa.bytesAt m (byteAddr (args 14)) (args 15).toNat)

theorem specResult_eq (m : Mem) (args : Nat → BitVec 32) :
    specResult m args = if Spec.Rsa.modulusValid (componentValue m args 2) (args 3).toNat then
      if accepted m args then some (Spec.Rsa.i2osp (outputValue m args) (args 3).toNat) else none
    else none := by
  unfold specResult Spec.Rsa.privateCrt
  dsimp only
  rw [VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.decryptCrt_eq]
  change (if Spec.Rsa.modulusValid (componentValue m args 2) (args 3).toNat then
    (if componentValue m args 4 < componentValue m args 2 ∧
      componentValue m args 6 * componentValue m args 8 = componentValue m args 2 ∧
      componentValue m args 14 < componentValue m args 6 then some (outputValue m args) else none).map
        (fun v => Spec.Rsa.i2osp v (args 3).toNat) else none) = _
  have order : (componentValue m args 4 < componentValue m args 2 ∧
      componentValue m args 6 * componentValue m args 8 = componentValue m args 2 ∧
      componentValue m args 14 < componentValue m args 6) ↔ accepted m args :=
    ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩
  cases Spec.Rsa.modulusValid (componentValue m args 2) (args 3).toNat <;>
    by_cases a : accepted m args <;>
    simp only [order, a, Bool.false_eq_true, ite_false, ite_true, Option.map_some, Option.map_none]

end VG.Proof.Bignum.X86.Crt
