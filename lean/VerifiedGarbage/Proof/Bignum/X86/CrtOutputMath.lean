module

public import VerifiedGarbage.Proof.Bignum.X86.CrtImportFrame
public import VerifiedGarbage.Proof.Bignum.X86.CrtNarrowResult

/-! # Caller byte lengths bound the imported modulus and factors -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86

theorem Inputs.modulus_length {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State}
    (h : Inputs base bytes len args s) : (args 3).toNat = len := by
  rw [h.nLen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.upper; omega)]

theorem Inputs.modulus_bound {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State}
    (h : Inputs base bytes len args s) : componentValue s.mem args 2 < 2 ^ (8 * len) := by
  have B := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) (args 3).toNat)
  simpa only [componentValue, Nat.reduceAdd, VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.pow256_eq, h.modulus_length] using B

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

end VG.Proof.Bignum.X86.Crt
