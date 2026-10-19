module

public import VerifiedGarbage.Proof.Bignum.X86.PublicContext
public import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math

/-! # Arithmetic facts for the compact public RSA context -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.Impl.Bignum.X86.PublicContext VG.Proof.Mont

theorem Context.odd {n bytes m : Nat} {base : Addr} {s : X86.State}
    (h : Context n m base bytes s) : m % 2 = 1 := by
  have hi := h.inverse
  have hmod : (m * w32 s.mem base inverseOffset + 1) % 2 = 0 := by omega
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hm with hm | hm
  · rw [Nat.add_mod, Nat.mul_mod, hm] at hmod
    simp at hmod
  · exact hm

theorem Context.coprime {n bytes m : Nat} {base : Addr} {s : X86.State}
    (h : Context n m base bytes s) : Nat.Coprime (2 ^ (64 * n)) m :=
  VG.Proof.Bignum.coprime_pow2 h.odd _

end VG.Proof.Bignum.X86.PublicContext
