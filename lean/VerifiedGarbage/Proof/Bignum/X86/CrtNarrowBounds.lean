module

public import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
public import VerifiedGarbage.Proof.Bignum.X86.CrtImportFrame
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86.CrtBothPowers

/-! # The imported factors and exponents fit the words their lengths give -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Impl.Mont.X86.Dynamic VG.Impl.Bignum.X86.Crt

/-- An imported component is below `2 ^ (8 len)` for its length `len`. -/
theorem component_lt {args : Nat → BitVec 32} {m : Mem}
    (i : Nat) : componentValue m args i < 2 ^ (8 * (args (i + 1)).toNat) := by
  have B := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt m (byteAddr (args i)) (args (i + 1)).toNat)
  simpa only [componentValue, VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.pow256_eq] using B

theorem fits_words {x len h : Nat} (hx : x < 2 ^ (8 * len)) (hl : len ≤ 8 * h) : x < 2 ^ (64 * h) :=
  Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))

/-- A factor and its exponent fit `h` words when the factor's length does. -/
theorem Inputs.p_fits {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State}
    (hi : Inputs base bytes len args s) {h : Nat} (hl : (args 7).toNat ≤ 8 * h) :
    componentValue s.mem args 6 < 2 ^ (64 * h) ∧ componentValue s.mem args 10 < 2 ^ (64 * h) :=
  ⟨fits_words (component_lt 6) hl,
    fits_words (component_lt 10) (by rw [hi.dpLen]; exact hl)⟩

theorem Inputs.q_fits {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State}
    (hi : Inputs base bytes len args s) {h : Nat} (hl : (args 9).toNat ≤ 8 * h) :
    componentValue s.mem args 8 < 2 ^ (64 * h) ∧ componentValue s.mem args 12 < 2 ^ (64 * h) :=
  ⟨fits_words (component_lt 8) hl,
    fits_words (component_lt 12) (by rw [hi.dqLen]; exact hl)⟩

/-- The arguments the exponentiations need, once the components are imported. -/
theorem import_powerArgs {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s u : State}
    (h : Inputs base bytes len args s) (hu : Inputs base bytes len args u)
    (P : wordsVal u.mem base (VG.Impl.Mont.X86.Dynamic.slot (Spec.Rsa.modulusWords len) pSlot) (Spec.Rsa.modulusWords len) =
      componentValue s.mem args 6)
    (Q : wordsVal u.mem base (VG.Impl.Mont.X86.Dynamic.slot (Spec.Rsa.modulusWords len) qSlot) (Spec.Rsa.modulusWords len) =
      componentValue s.mem args 8)
    (DP : wordsVal u.mem base (VG.Impl.Mont.X86.Dynamic.slot (Spec.Rsa.modulusWords len) dpSlot) (Spec.Rsa.modulusWords len) =
      componentValue s.mem args 10)
    (DQ : wordsVal u.mem base (VG.Impl.Mont.X86.Dynamic.slot (Spec.Rsa.modulusWords len) dqSlot) (Spec.Rsa.modulusWords len) =
      componentValue s.mem args 12) :
    PowerArgs base bytes (Spec.Rsa.modulusWords len) u :=
  ⟨⟨args 7, hu.stack 7 (by decide), fun hl => by rw [P, DP]; exact h.p_fits hl⟩,
    ⟨args 9, hu.stack 9 (by decide), fun hl => by rw [Q, DQ]; exact h.q_fits hl⟩⟩

end VG.Proof.Bignum.X86.Crt
