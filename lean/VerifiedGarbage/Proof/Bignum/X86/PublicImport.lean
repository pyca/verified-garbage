module

public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.LoadBE
public import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
public import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # Import the modulus and representative without changing the call header -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86

theorem importNumbers_ok {s : State} {base : Addr} {bytes n len : Nat} {np xp : BitVec 32}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes) (hl : 0 < len) (hlen : len ≤ 8 * n)
    (NP : CallArgument s base bytes 2 np) (NL : CallArgument s base bytes 3 (BitVec.ofNat 32 len))
    (XP : CallArgument s base bytes 6 xp) (XL : CallArgument s base bytes 7 (BitVec.ofNat 32 len))
    (nf : np.toNat + len ≤ 2 ^ 32) (xf : xp.toNat + len ≤ 2 ^ 32)
    (nr : InRegions (s.rd ++ s.wr) (byteAddr np) len)
    (xr : InRegions (s.rd ++ s.wr) (byteAddr xp) len)
    (ns : Region.Disjoint ⟨byteAddr np, len⟩ ⟨base, bytes⟩)
    (xs : Region.Disjoint ⟨byteAddr xp, len⟩ ⟨base, bytes⟩) :
    WP isa (PublicFn.importNumbers n) s fun t =>
      wordsVal t.mem base (slot n 0) n = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr np) len) ∧
      wordsVal t.mem base (slot n 6) n = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr xp) len) ∧
      Outside base 256 (bytes - 256) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  have s06 := slot_le (n := n) (i := 0) (j := 6) (by decide)
  have d0 := slot_header n 0
  have d6 := slot_header n 6
  have nw := hs.nowrap
  simp only [stride] at b0 b6 s06
  unfold PublicFn.importNumbers
  refine WP.seq (WP.mono (argumentPair_ok (by decide) (by decide) NP.readSrc NL.readSrc)
    fun u ⟨NPtr, NCount, Mu, Ku⟩ => ?_)
  refine WP.seq (WP.mono (loadBE_ok (hs.of_keeps Ku (by decide)) hn (by omega) hl hlen
    (by rw [NPtr]; exact nf) NCount (by rw [NPtr, Ku.2.1, Ku.2.2]; exact nr)
    (by rw [NPtr]; exact ns.sub_right (Offset.sub_base base (by omega))))
    fun v ⟨NValue, Nv, Kv⟩ => ?_)
  have Ksv := (Ku.mono (by decide)).trans Kv
  have Osv : Outside base 0 bytes s.mem v.mem := by
    rw [← Mu]
    exact Nv.mono (by omega) (by omega)
  have hv := hs.of_keeps Ksv (by decide)
  refine WP.seq (WP.mono (argumentPair_ok (by decide) (by decide)
    ((XP.keep Ksv (by decide) Osv).readSrc) ((XL.keep Ksv (by decide) Osv).readSrc))
    fun w ⟨XPtr, XCount, Mw, Kw⟩ => ?_)
  have Ksw : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s w := Ksv.trans (Kw.mono (by decide))
  refine WP.mono (loadBE_ok (hs.of_keeps Ksw (by decide)) hn (by omega) hl hlen
    (by rw [XPtr]; exact xf) XCount (by rw [XPtr, Ksw.2.1, Ksw.2.2]; exact xr)
    (by rw [XPtr]; exact xs.sub_right (Offset.sub_base base (by omega))))
    fun t ⟨XValue, Xt, Kt⟩ => ?_
  refine ⟨?_, ?_, ?_, Ksw.trans Kt⟩
  · rw [wordsVal_eq_val32, Xt.val32 (.inl (by omega)) (by omega),
      ← wordsVal_eq_val32, Mw, NValue, NPtr, Mu]
  · rw [XValue, XPtr, Mw, scratch_bytes Osv (by omega) xs]
  · have N : Outside base 256 (bytes - 256) s.mem w.mem := by
      rw [Mw, ← Mu]
      exact Nv.mono (by omega) (by omega)
    exact N.trans (Xt.mono (by omega) (by omega))

end VG.Proof.Bignum.X86.PublicContext
