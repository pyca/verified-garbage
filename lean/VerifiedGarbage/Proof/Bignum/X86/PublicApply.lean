module

public import VerifiedGarbage.Proof.Bignum.X86.InputCompare
public import VerifiedGarbage.Proof.Bignum.X86.PublicPowerFrame
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn

/-! # Compare, save acceptance, and exponentiate every RSA representative -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem acceptAndPower_ok {n bytes m x e : Nat} {base : Addr} {s : State}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32)
    (hz : size n ≤ bytes) (hv : wordsVal s.mem base (slot n 0) n = m)
    (hx : wordsVal s.mem base (slot n 6) n = x) (he : val32 s.mem base 128 2 = e)
    (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (PublicFn.acceptAndPower n) s fun t =>
      Context n m base bytes t ∧ wordsVal t.mem base (slot n 7) n = x ^ e % m ∧
      t.mem.readW (off base 144) 32 = (if x < m then BitVec.allOnes 32 else 0) ∧
      Outside base 16 (bytes - 16) s.mem t.mem ∧ Keeps powerClob s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  have s01 := slot_le (n := n) (i := 0) (j := 1) (by decide)
  have s16 := slot_le (n := n) (i := 1) (j := 6) (by decide)
  have d0 := slot_header n 0
  have d1 := slot_header n 1
  have d6 := slot_header n 6
  have nw := hs.nowrap
  simp only [stride] at b0 b1 b6 s01 s16
  unfold PublicFn.acceptAndPower
  refine WP.seq (WP.mono (inputCompare_ok hs hn hz) fun u ⟨Mask, O, K⟩ => ?_)
  have hu := hs.of_keeps K (by decide)
  refine WP.seq (wp_storeS (hu.ea (by change 144 < bytes; omega))
    (hu.write (by change 144 + 4 ≤ bytes; omega)) fun v S => WP.block_nil ?_)
  have hv' := hu.of_keeps (S.keeps []) (by decide)
  have Os : Outside base 144 4 u.mem v.mem := by
    rw [S.mem]
    exact writeW32_outside _ _ _ (by decide)
  have modV : wordsVal v.mem base (slot n 0) n = m := by
    rw [wordsVal_eq_val32, Os.val32 (.inr (by omega)) (by omega),
      O.val32 (.inl (by omega)) (by omega), ← wordsVal_eq_val32, hv]
  have inputV : wordsVal v.mem base (slot n 6) n = x := by
    rw [wordsVal_eq_val32, Os.val32 (.inr (by omega)) (by omega),
      O.val32 (.inr (by omega)) (by omega), ← wordsVal_eq_val32, hx]
  have expV : val32 v.mem base 128 2 = e := by
    rw [Os.val32 (.inl (by decide)) (by decide), O.val32 (.inl (by omega)) (by decide), he]
  have savedMask : v.mem.readW (off base 144) 32 = (if x < m then BitVec.allOnes 32 else 0) := by
    rw [S.mem, PublicFn.acceptanceOffset, Mem.readW_writeW_self32, Mask, hx, hv]
  refine WP.mono (publicPower_ok hv' hn hn32 hz modV hm1 hodd) fun t ⟨C, V, Ot, Kt⟩ => ?_
  refine ⟨C, by rw [V, inputV, expV], ?_, ?_, ?_⟩
  · rw [power_header Ot (.inr ⟨by decide, by decide⟩), savedMask]
  · exact ((O.mono (by omega) (by omega)).trans (Os.mono (by omega) (by omega))).trans
      (power_saved Ot hz)
  · exact ((K.mono (by decide)).trans ((S.keeps []).mono (by decide))).trans Kt

end VG.Proof.Bignum.X86.PublicContext
