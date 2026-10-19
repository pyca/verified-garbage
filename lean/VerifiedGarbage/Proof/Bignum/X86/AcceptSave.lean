module

public import VerifiedGarbage.Proof.Bignum.X86.InputCompare
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

/-! # Compare the input with the modulus and save the acceptance mask -/

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

end VG.Proof.Bignum.X86.PublicContext
