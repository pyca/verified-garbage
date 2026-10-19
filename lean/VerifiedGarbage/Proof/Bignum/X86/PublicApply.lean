module

public import VerifiedGarbage.Proof.Bignum.X86.AcceptSave
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
  unfold PublicFn.acceptAndPower
  refine WP.seq (WP.mono (acceptSave_ok hs hn hz) fun u Save => WP.seq (WP.mono Save
    fun v ⟨hv', modV, _, inputV, expV, savedMask, Ov, Kv⟩ => ?_))
  rw [hv] at modV
  rw [hx, hv] at savedMask
  refine WP.mono (publicPower_ok hv' hn hn32 hz modV hm1 hodd) fun t ⟨C, V, Ot, Kt⟩ => ?_
  refine ⟨C, by rw [V, inputV, expV, hx, he], ?_, ?_, Kv.trans Kt⟩
  · rw [power_header Ot (.inr ⟨by decide, by decide⟩), savedMask]
  · exact Ov.trans (power_saved Ot hz)

end VG.Proof.Bignum.X86.PublicContext
