module

public import VerifiedGarbage.Proof.Bignum.X86.InputCompare
public import VerifiedGarbage.Proof.Bignum.X86.PublicPowerFrame
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPower

/-! # Compare, save acceptance, and exponentiate every RSA representative -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

/-- The input's comparison with the modulus, its mask saved: everything the
exponentiation reads is kept. -/
theorem acceptSave_ok {n bytes : Nat} {base : Addr} {s : State}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes) :
    WP isa (inputCompare n) s fun u =>
      WP isa (.block [.store (VG.Impl.Mont.X86.sc PublicFn.acceptanceOffset) .ecx]) u fun v =>
        Scr v base bytes ∧
        wordsVal v.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n =
          wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n ∧
        wordsVal v.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n =
          wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n ∧
        wordsVal v.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 6) n =
          wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 6) n ∧
        val32 v.mem base 128 2 = val32 s.mem base 128 2 ∧
        v.mem.readW (off base 144) 32 =
          (if wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 6) n <
            wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n
          then BitVec.allOnes 32 else 0) ∧
        Outside base 16 (bytes - 16) s.mem v.mem ∧ Keeps powerClob s v := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  have s15 := slot_le (n := n) (i := 1) (j := 5) (by decide)
  have d5 := slot_header n 5
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  have s01 := slot_le (n := n) (i := 0) (j := 1) (by decide)
  have s16 := slot_le (n := n) (i := 1) (j := 6) (by decide)
  have d0 := slot_header n 0
  have d1 := slot_header n 1
  have d6 := slot_header n 6
  have nw := hs.nowrap
  simp only [stride] at b0 b1 b5 b6 s01 s15 s16
  refine WP.mono (inputCompare_ok hs hn hz) fun u ⟨Mask, O, K⟩ => ?_
  have hu := hs.of_keeps K (by decide)
  refine wp_storeS (hu.ea (by change 144 < bytes; omega))
    (hu.write (by change 144 + 4 ≤ bytes; omega)) fun v S => WP.block_nil ?_
  have Os : Outside base 144 4 u.mem v.mem := by
    rw [S.mem]
    exact writeW32_outside _ _ _ (by decide)
  refine ⟨hu.of_keeps (S.keeps []) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [wordsVal_eq_val32, Os.val32 (.inr (by omega)) (by omega),
      O.val32 (.inl (by omega)) (by omega), ← wordsVal_eq_val32]
  · rw [wordsVal_eq_val32, Os.val32 (.inr (by omega)) (by omega),
      O.val32 (.inr (by omega)) (by omega), ← wordsVal_eq_val32]
  · rw [wordsVal_eq_val32, Os.val32 (.inr (by omega)) (by omega),
      O.val32 (.inr (by omega)) (by omega), ← wordsVal_eq_val32]
  · rw [Os.val32 (.inl (by decide)) (by decide), O.val32 (.inl (by omega)) (by decide)]
  · rw [S.mem, PublicFn.acceptanceOffset, Mem.readW_writeW_self32, Mask]
  · exact (O.mono (by omega) (by omega)).trans (Os.mono (by omega) (by omega))
  · exact (K.mono (by decide)).trans ((S.keeps []).mono (by decide))

theorem precomputedAcceptAndPower_ok {n bytes m x e r : Nat} {base : Addr} {s : State}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes) (hv : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n = m)
    (hx : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 6) n = x) (he : val32 s.mem base 128 2 = e)
    (hm1 : 1 < m) (hodd : m % 2 = 1)
    (hr : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n = r) (hrm : r < m) :
    WP isa (PrecomputedFn.acceptAndPower n) s fun t =>
      Context n m base bytes t ∧ wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 7) n < m ∧
      (r = 2 ^ (128 * n) % m → wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 7) n = x ^ e % m) ∧
      t.mem.readW (off base 144) 32 = (if x < m then BitVec.allOnes 32 else 0) ∧
      Outside base 16 (bytes - 16) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold PrecomputedFn.acceptAndPower
  refine WP.seq (WP.mono (acceptSave_ok hs hn hz) fun u Save => WP.seq (WP.mono Save
    fun v ⟨hv', modV, rV, inputV, expV, savedMask, Ov, Kv⟩ => ?_))
  rw [hv] at modV
  rw [hx, hv] at savedMask
  refine WP.mono (precomputedPower_ok hv' hn hz modV hm1 hodd (by rw [rV, hr]; exact hrm))
    fun t ⟨C, B, V, Ot, Kt⟩ => ?_
  refine ⟨C, B, ?_, ?_, ?_, Kv.trans Kt⟩
  · intro good
    rw [V (by rw [rV, hr]; exact good), inputV, expV, hx, he]
  · rw [power_header Ot (.inr ⟨by decide, by decide⟩), savedMask]
  · exact Ov.trans (power_saved Ot hz)

end VG.Proof.Bignum.X86.PublicContext
