module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyProduct
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # The prime product fits exactly in the modulus-width key array -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem primeProduct_ok {s : State} {B : Addr} {Z n out a b k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (ho : out < 32) (ha : a < 32) (hb : b < 32) (oa : out ≠ a) (ob : out ≠ b)
    (boundA : num s.mem B n a < 2 ^ (32 * k)) (boundB : num s.mem B n b < 2 ^ (32 * k)) :
    WP isa (primeProduct n out a b) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [out] [kProduct] s.mem t.mem ∧
      num t.mem B n out = num s.mem B n a * num s.mem B n b ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have A := VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : k ≤ n) boundA
  have Bv := VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : k ≤ n) boundB
  have bound : val32 s.mem B (arr n a) k * val32 s.mem B (arr n b) k < 2 ^ (32 * n) := by
    have lt := Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_left (val32 s.mem B (arr n a) k) (Nat.le_of_lt (val32_lt s.mem B (arr n b) k)))
      (Nat.mul_lt_mul_of_pos_right (val32_lt s.mem B (arr n a) k) (Nat.two_pow_pos (32 * k)))
    rw [show 32 * n = 32 * k + 32 * k by omega, Nat.pow_add]
    exact lt
  refine WP.mono (product_ok h width positive even ho ha hb oa ob) fun t ⟨ht, frame, value, K⟩ => ?_
  have low := VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : n ≤ n + 2)
    (by rw [value]; exact bound)
  refine ⟨ht, frame, ?_, K⟩
  change val32 t.mem B (arr n out) n = _
  rw [low, value, A, Bv]

end VG.Proof.RsaKeyGen.X86.Key
