module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomeryFrame
import VerifiedGarbage.Proof.Bignum.Math

/-! Encode ordinary one using the R-squared already computed. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem montgomery_one {s : State} {base : Addr} {n m : Nat}
    (C : Context n m base montgomeryBytes s)
    (room : CallRoom (s.gpr .esp) base montgomeryBytes)
    (hn : 0 < n) (hn' : n ≤ 48) (odd : m % 2 = 1)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (rr : wordsVal s.mem base (slot n 4) n = 2 ^ (64 * n) * 2 ^ (64 * n) % m) :
    WP isa (montgomery n 6 4 3) s fun t =>
      Context n m base montgomeryBytes t ∧
      wordsVal t.mem base (slot n 6) n = 2 ^ (64 * n) % m ∧
      wordsVal t.mem base (slot n 4) n = 2 ^ (64 * n) * 2 ^ (64 * n) % m ∧
      MontgomeryFrame base (s.gpr .esp) n 6 s t ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have modulus : val32 s.mem base (slot n 0) (2 * n) = m := by
    rw [← wordsVal_eq_val32]; exact C.modulus.val
  have ordinary : val32 s.mem base (slot n 3) (2 * n) = 1 := by
    rw [← wordsVal_eq_val32]; exact one
  have square : val32 s.mem base (slot n 4) (2 * n) = 2 ^ (64 * n) * 2 ^ (64 * n) % m := by
    rw [← wordsVal_eq_val32]; exact rr
  refine WP.mono (montgomery_ok C.scr room hn hn' (show 6 < 9 by decide) (show 4 < 9 by decide)
    (show 3 < 9 by decide) (by decide) (by rw [modulus]; exact C.inverse)
    (by rw [ordinary, modulus]; exact C.gt_one)) fun t ⟨cs, rd, wr, F, bound, value⟩ => ?_
  rw [modulus] at bound value
  rw [ordinary, square, Nat.mul_one, Nat.mod_mod] at value
  have encoded := VG.Proof.Bignum.mont_cancel (VG.Proof.Bignum.coprime_pow2 odd _) value
  rw [Nat.mod_eq_of_lt bound] at encoded
  refine ⟨montgomery_context_keep C room hn hn' (by decide) (by decide) cs rd wr F,
    ?_, ?_, F, cs, rd, wr⟩
  · rw [wordsVal_eq_val32]; exact encoded
  · rw [wordsVal_eq_val32, montgomery_slot_keep C.scr room F hn hn' (by decide) (by decide)
      (show 4 < 9 by decide) (by decide), ← wordsVal_eq_val32]
    exact rr

end VG.Proof.Dsa.X86.Generation
