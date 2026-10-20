module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Framework.Offset

/-! # Import the public modulus while preserving the saved call frame -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86

theorem precomputedInput_ok {s : State} {base : Addr} {bytes n len : Nat} {xp : BitVec 32}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes) (hl : 0 < len) (hlen : len ≤ 8 * n)
    (XP : CallArgument s base bytes 6 xp) (XL : CallArgument s base bytes 7 (BitVec.ofNat 32 len))
    (xf : xp.toNat + len ≤ 2 ^ 32) (xr : InRegions (s.rd ++ s.wr) (byteAddr xp) len)
    (xs : Region.Disjoint ⟨byteAddr xp, len⟩ ⟨base, bytes⟩) :
    WP isa (PrecomputedFn.importInput n) s fun t =>
      wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 6) n = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr xp) len) ∧
      Outside base (VG.Impl.Bignum.X86.PublicContext.slot n 6) (8 * n) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have b0 := slot_bound (n := n) (i := 6) (by decide)
  have nw := hs.nowrap
  simp only [stride] at b0
  unfold PrecomputedFn.importInput
  refine WP.seq (WP.mono (argumentPair_ok (by decide) (by decide) XP.readSrc XL.readSrc)
    fun u ⟨XPtr, NCount, Mu, Ku⟩ => ?_)
  refine WP.mono (loadBE_ok (hs.of_keeps Ku (by decide)) hn (by omega) hl hlen
    (by rw [XPtr]; exact xf) NCount (by rw [XPtr, Ku.2.1, Ku.2.2]; exact xr)
    (by rw [XPtr]; exact xs.sub_right (Offset.sub_base base (by omega))))
    fun t ⟨N, O, K⟩ => ?_
  refine ⟨?_, ?_, (Ku.mono (by decide)).trans K⟩
  · rw [N, XPtr, Mu]
  · rw [← Mu]; exact O

end VG.Proof.Bignum.X86.PublicContext
