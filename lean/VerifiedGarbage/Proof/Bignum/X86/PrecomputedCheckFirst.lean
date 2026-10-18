module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedChecks
public import VerifiedGarbage.Proof.Bignum.X86.ArrayCompare
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedCheckFrame

/-! # Reject packed moduli below two before Montgomery arithmetic -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

theorem precomputedCheckFirst_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (space : size n ≤ bytes) :
    WP isa (precomputedCheckFirst n) s fun t =>
      t.mem.readW (off base 148) 32 =
        (if 1 < wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n then BitVec.allOnes 32 else 0) ∧
      Outs base (precomputedCheckRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b4 := slot_bound (n := n) (i := 4) (by decide)
  have sep := slot_le (n := n) (i := 0) (j := 4) (by decide)
  have hd := slot_header n 0
  have nw := hs.nowrap
  simp only [stride] at b0 b4 sep
  unfold precomputedCheckFirst
  refine WP.seq (WP.mono (one_ok hs hn (by omega)) fun u ⟨O, One, K⟩ => ?_)
  refine WP.seq (WP.mono (arrayCompare_ok (hs.of_keeps K (by decide)) hn space
    (by decide) (by decide) (by decide) (by decide)) fun v ⟨Mask, Ov, Kv⟩ => ?_)
  have hv := (hs.of_keeps K (by decide)).of_keeps Kv (by decide)
  refine wp_storeS (hv.ea (by change 148 < bytes; omega))
    (hv.write (by change 148 + 4 ≤ bytes; omega)) fun t S => WP.block_nil ?_
  have Ot : Outside base 148 4 v.mem t.mem := by rw [S.mem]; exact writeW32_outside _ _ _ (by decide)
  refine ⟨?_, ?_, ((K.mono (by decide)).trans (Kv.mono (by decide))).trans ((S.keeps []).mono (by decide))⟩
  · rw [S.mem, precomputedCheckOffset, Mem.readW_writeW_self32, Mask, One]
    have M : wordsVal u.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n = wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n := by
      rw [wordsVal_eq_val32, O.val32 (.inl (by omega)) (by omega), ← wordsVal_eq_val32]
    rw [M]
  · exact ((Outs.of_outside O (by simp [precomputedCheckRanges])).trans
      (Outs.of_outside Ov (by simp [precomputedCheckRanges]))).trans
      (Outs.of_outside Ot (by simp [precomputedCheckRanges]))

end VG.Proof.Bignum.X86.PublicContext
