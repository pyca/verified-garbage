module

public import VerifiedGarbage.Proof.Rsa.X86.KcABI
public import VerifiedGarbage.Proof.Rsa.X86.KcLoads
public import VerifiedGarbage.Proof.Rsa.X86.KcResult

import VerifiedGarbage.Proof.Rsa.X86.KcBuffers
import VerifiedGarbage.Proof.Rsa.X86.KcResources
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
/-! # The signature's byte-length bounds imply the arithmetic factor bounds -/

-- Formerly `VerifiedGarbage/Proof/Rsa/KeyByteBounds.lean`, which only this module imported.
section

/-! # A factor shorter than the modulus leaves room for modular addition -/

section
namespace VG.Proof.Rsa
open VG

theorem short_factor_bounds {bs : List Byte} {k w : Nat} (short : bs.length < k) (fits : k ≤ 4 * w) :
    Spec.Rsa.os2ip bs < 256 ^ (k - 1) ∧
    2 * Spec.Rsa.os2ip bs ≤ 2 ^ (32 * w) ∧ Spec.Rsa.os2ip bs < 2 ^ (32 * w) := by
  have value := lt_of_os2ip bs
  have small : 256 ^ bs.length ≤ 256 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have room : 2 * 256 ^ bs.length ≤ 2 ^ (32 * w) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, ← Nat.pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨Nat.lt_of_lt_of_le value small, by omega, by omega⟩
end VG.Proof.Rsa
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.KeyCheck

theorem ABI.numberBounds {full : Bool} {s : State} (a : ABI full s) (m : Mem) :
    Bounds (geometry (caller full s)) (arg s 1).toNat (numbers (caller full s) m) := by
  have width : (arg s 1).toNat ≤ 4 * (2 * (caller full s).n) := by have := a.width.2.2; omega
  have pLen : (inputBytes (caller full s) m (if full then 3 else 2)).length < (arg s 1).toNat := by
    rw [inputBytes, VG.Proof.Bignum.bytesAt_length]
    cases full <;> exact a.pSmall
  have qLen : (inputBytes (caller full s) m (if full then 4 else 3)).length < (arg s 1).toNat := by
    rw [inputBytes, VG.Proof.Bignum.bytesAt_length]
    cases full <;> exact a.qSmall
  have p := VG.Proof.Rsa.short_factor_bounds pLen width
  have q := VG.Proof.Rsa.short_factor_bounds qLen width
  exact ⟨p.1, q.1, p.2.1, q.2.1⟩

theorem numbers_entry {full : Bool} {s : State} {m : Mem} (a : ABI full s)
    (o : Outside (caller full s).base 0 (caller full s).size s.mem m) :
    numbers (caller full s) m = numbers (caller full s) s.mem := by
  have same (i : Nat) (hi : 2 * i < scratchArg full) :
      inputBytes (caller full s) m i = inputBytes (caller full s) s.mem i :=
    VG.Proof.Bignum.scratch_bytes o
      (by have := (a.inputLength hi).2; have := a.width.2.1; omega)
      (a.inApart _ (a.inputMember hi))
  cases full
  · simp only [numbers, show (caller false s).full = false from rfl, Bool.false_eq_true, ite_false]
    rw [same 0 (by decide), same 1 (by decide), same 2 (by decide), same 3 (by decide),
      same 4 (by decide), same 5 (by decide), same 6 (by decide)]
  · simp only [numbers, show (caller true s).full = true from rfl, ite_true]
    rw [same 0 (by decide), same 1 (by decide), same 2 (by decide), same 3 (by decide),
      same 4 (by decide), same 5 (by decide), same 6 (by decide), same 7 (by decide)]
end VG.Proof.Rsa.X86.KeyCheck
