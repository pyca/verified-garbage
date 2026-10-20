module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrepareExponent
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # Factoring the predecessor preserves the prepared Montgomery constants -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem prepareWrites_word {n d : Nat} {base : Addr} {s t : Mem}
    (O : Outs base (prepareWrites n) s t)
    (disjoint : d + 4 ≤ primeTwos ∨ primeTwos + 4 ≤ d)
    (above : slot n 8 + 8 * n ≤ d) (below : d + 4 ≤ primeExponent) :
    t.readW (off base d) 32 = s.readW (off base d) 32 := by
  apply BitVec.eq_of_toNat_eq
  have v := O.val32 (d := d) (k := 1) (by
    intro r hr
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> omega) (by unfold primeExponent at below; omega)
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using v

theorem prepareWrites_low {n d k : Nat} {base : Addr} {s t : Mem}
    (O : Outs base (prepareWrites n) s t) (width : n ≤ 48)
    (low : d + 4 * k ≤ slot n 8) : val32 t base d k = val32 s base d k := by
  apply O.val32
  · intro r hr
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [slot, stride, primeTwos, primeExponent] at * <;> omega
  · simp only [slot, stride] at low; omega

theorem primePrepare_ok {s : State} {base : Addr} {size n m : Nat}
    (C : Context n m base size s) (width : n ≤ 48) (room : primeExponent + 8 * n ≤ size)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m) (odd : m % 2 = 1) :
    WP isa (prepareExponent n) s fun t => Context n m base size t ∧
      wordsVal t.mem base (slot n 3) n = 1 ∧ wordsVal t.mem base (slot n 4) n = 2 ^ (128 * n) % m ∧
      t.mem.readW (off base primeTwos) 32 = BitVec.ofNat 32 (Spec.Rsa.splitTwos (m - 1)).1 ∧
      val32 t.mem base primeExponent (2 * n) = (Spec.Rsa.splitTwos (m - 1)).2 ∧
      Outs base (prepareWrites n) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (prepareExponent_ok C width room one odd) fun t ⟨twos, exponent, O, K⟩ => ?_
  have keep (j : Nat) (hj : j < 8) : wordsVal t.mem base (slot n j) n = wordsVal s.mem base (slot n j) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    apply prepareWrites_low O width
    have h := slot_le (n := n) hj
    unfold stride at h
    omega
  refine ⟨⟨C.scr.of_keeps K (by decide), C.size_le,
    ⟨C.modulus.n0, C.modulus.mo, C.modulus.tmp, C.modulus.sep, (keep 0 (by decide)).trans C.modulus.val⟩,
    C.gt_one, ?_⟩, (keep 3 (by decide)).trans one, (keep 4 (by decide)).trans r2, twos, exponent, O, K⟩
  have low := prepareWrites_low O width (d := 0) (k := 1) (by simp only [slot, stride]; omega)
  have word : w32 t.mem base 0 = w32 s.mem base 0 := by simpa only [val32, Nat.mul_zero, Nat.add_zero] using low
  rw [word]
  exact C.inverse
end VG.Proof.Dsa.X86.Generation
