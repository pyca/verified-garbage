module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedSetup
public import VerifiedGarbage.Proof.Bignum.X86.PublicSetup

/-! # Set the inverse and one without recomputing the stored Montgomery power -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

theorem precomputedSetup_ok {n bytes m : Nat} {base : Addr} {s : State}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (precomputedSetup n) s fun t =>
      Context n m base bytes t ∧ wordsVal t.mem base (slot n 4) n = 1 ∧
      Outs base [(56, 4), (slot n 4, 8 * n)] s.mem t.mem ∧ Keeps powerClob s t := by
  have nw := hs.nowrap
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b3 := slot_bound (n := n) (i := 4) (by decide)
  have hd0 := slot_header n 0
  have hd1 := slot_header n 1
  have hd3 := slot_header n 4
  have s01 := slot_le (n := n) (i := 0) (j := 1) (by decide)
  have s03 := slot_le (n := n) (i := 0) (j := 4) (by decide)
  have low := modulus_low hn hv
  have lowodd : w32 s.mem base (slot n 0) % 2 = 1 := by omega
  unfold precomputedSetup
  refine WP.seq (WP.mono (setupInverse_ok hs
    (by unfold stride at b0; omega) (by change 56 + 4 ≤ bytes; unfold stride at b0; omega) lowodd) fun u ⟨inv, O, K⟩ => ?_)
  have cu : Context n m base bytes u := by
    refine ⟨hs.of_keeps K (by decide), hz, ⟨hn, ?_, ?_, ?_, ?_⟩, hm1, ?_⟩
    · change slot n 0 + 8 * n ≤ bytes; unfold stride at b0; omega
    · change slot n 1 + 8 * n ≤ bytes; unfold stride at b1; omega
    · change slot n 0 + 8 * n ≤ slot n 1 ∨ slot n 1 + 8 * n ≤ slot n 0
      unfold stride at s01; omega
    · change wordsVal u.mem base (slot n 0) n = m
      rw [wordsVal_eq_val32, O.val32 (by change slot n 0 + 4 * (2 * n) ≤ 56 ∨ 56 + 4 ≤ slot n 0; omega) (by unfold stride at b0; omega), ← wordsVal_eq_val32, hv]
    · rw [Nat.add_mod, Nat.mul_mod, low] at ⊢
      rw [Nat.add_mod, Nat.mul_mod] at inv
      simpa only [Nat.mod_eq_of_lt (s.mem.readW (off base (slot n 0)) 32).isLt] using inv
  refine WP.mono (one_ok cu.scr hn (by unfold stride at b3; omega)) fun v ⟨Ov, Vv, Kv⟩ => ?_
  have cv := cu.outside_keep Kv (by decide) (by decide) Ov
    (.inl (by unfold stride at s03; omega)) (by change 56 + 4 ≤ slot n 4; omega)
  refine ⟨cv, Vv, ?_, (K.mono (by decide)).trans (Kv.mono (by decide))⟩
  exact (Outs.of_outside O (by simp [inverseOffset, VG.Impl.Bignum.sMinv])).trans
    (Outs.of_outside Ov (by simp))

end VG.Proof.Bignum.X86.PublicContext
