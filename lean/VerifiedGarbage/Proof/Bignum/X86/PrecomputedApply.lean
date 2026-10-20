module

public import VerifiedGarbage.Proof.Bignum.X86.PublicPowerFrame
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Bignum.X86.PublicContext
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPower
public import VerifiedGarbage.Proof.Bignum.X86.AcceptSave

import VerifiedGarbage.Proof.Bignum.X86.InputCompare
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # Compare, save acceptance, and exponentiate every RSA representative -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

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
