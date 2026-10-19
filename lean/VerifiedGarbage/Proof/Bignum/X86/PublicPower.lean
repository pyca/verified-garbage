module

public import VerifiedGarbage.Impl.Bignum.X86.PublicPower
public import VerifiedGarbage.Proof.Bignum.X86.PublicSetup
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedExponent

/-! # Complete Montgomery setup and RSA public-power correctness -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic

theorem setup_input {n : Nat} {base : Addr} {m m' : Mem}
    (h : Outs base (setupRanges n) m m') (bound : size n ≤ 2 ^ 64) :
    wordsVal m' base (slot n 6) n = wordsVal m base (slot n 6) n := by
  have b := slot_bound (n := n) (i := 6) (by decide)
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply h.val32
  · intro r hr
    simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [slot, stride, VG.Impl.Bignum.hdrBytes] <;> omega
  · simp only [stride] at b
    omega

theorem setup_exponent {n : Nat} {base : Addr} {m m' : Mem}
    (h : Outs base (setupRanges n) m m') :
    val32 m' base 128 2 = val32 m base 128 2 := by
  apply h.val32
  · intro r hr
    simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [slot, stride, VG.Impl.Bignum.hdrBytes] <;> omega
  · decide

theorem publicPower_ok {n bytes m : Nat} {base : Addr} {s : State}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32)
    (hz : size n ≤ bytes) (hv : wordsVal s.mem base (slot n 0) n = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (publicPower n) s fun t =>
      Context n m base bytes t ∧
      wordsVal t.mem base (slot n 7) n =
        wordsVal s.mem base (slot n 6) n ^ val32 s.mem base 128 2 % m ∧
      Outs base (setupRanges n ++ exponentRanges n) s.mem t.mem ∧
      Keeps powerClob s t := by
  unfold publicPower
  refine WP.seq (WP.mono (setup_ok hs hn hn32 hz hv hm1 hodd) fun u ⟨C, One, R2, O, K⟩ => ?_)
  refine WP.mono (precomputedExponent_ok C One
    (by rw [R2]; exact Nat.mod_lt _ (by omega))) fun t ⟨Ct, _, Vt, Ot, Kt⟩ => ?_
  refine ⟨Ct, ?_, ?_, K.trans Kt⟩
  · rw [Vt R2, setup_input O (by have := hs.nowrap; omega), setup_exponent O]
  · exact (O.mono (by intros; exact List.mem_append_left _ ‹_›)).trans
      (Ot.mono (by intros; exact List.mem_append_right _ ‹_›))

end VG.Proof.Bignum.X86.PublicContext
