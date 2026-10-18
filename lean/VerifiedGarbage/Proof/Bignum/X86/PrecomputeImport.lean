module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.Proof.Bignum.X86.PublicImport

/-! # Import the public modulus while preserving the saved call frame -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86

theorem precomputeImport_ok {s : State} {base : Addr} {bytes n len : Nat} {np : BitVec 32}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes) (hl : 0 < len) (hlen : len ≤ 8 * n)
    (NP : CallArgument s base bytes 2 np) (NL : CallArgument s base bytes 3 (BitVec.ofNat 32 len))
    (nf : np.toNat + len ≤ 2 ^ 32) (nr : InRegions (s.rd ++ s.wr) (byteAddr np) len)
    (ns : Region.Disjoint ⟨byteAddr np, len⟩ ⟨base, bytes⟩) :
    WP isa (PrecomputeFn.importModulus n) s fun t =>
      wordsVal t.mem base (slot n 0) n = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr np) len) ∧
      Outside base 256 (bytes - 256) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have d0 := slot_header n 0
  have nw := hs.nowrap
  simp only [stride] at b0
  unfold PrecomputeFn.importModulus
  refine WP.seq (WP.mono (argumentPair_ok (by decide) (by decide) NP.readSrc NL.readSrc)
    fun u ⟨NPtr, NCount, Mu, Ku⟩ => ?_)
  refine WP.mono (loadBE_ok (hs.of_keeps Ku (by decide)) hn (by omega) hl hlen
    (by rw [NPtr]; exact nf) NCount (by rw [NPtr, Ku.2.1, Ku.2.2]; exact nr)
    (by rw [NPtr]; exact ns.sub_right (Offset.sub_base base (by omega))))
    fun t ⟨N, O, K⟩ => ?_
  refine ⟨?_, ?_, (Ku.mono (by decide)).trans K⟩
  · rw [N, NPtr, Mu]
  · rw [← Mu]; exact O.mono (by omega) (by omega)

end VG.Proof.Bignum.X86.PublicContext
