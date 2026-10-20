module

public import VerifiedGarbage.Impl.Bignum.X86.CrtCore
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Framework.Offset

/-! # Import a cdecl byte-slice argument into private scratch -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86.Crt VG.Proof.Mont VG.Proof.Mont.X86

theorem importComponent_ok {s : State} {base : Addr} {bytes n len i dst : Nat} {ptr : BitVec 32}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : dst + 8 * n ≤ bytes)
    (hl : 0 < len) (hlen : len ≤ 8 * n)
    (P : CallArgument s base bytes i ptr) (L : CallArgument s base bytes (i + 1) (BitVec.ofNat 32 len))
    (bound : ptr.toNat + len ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (byteAddr ptr) len)
    (disjoint : Region.Disjoint ⟨byteAddr ptr, len⟩ ⟨base, bytes⟩) :
    WP isa (importComponent n i dst) s fun t =>
      wordsVal t.mem base dst n = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr ptr) len) ∧
      Outside base dst (8 * n) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold importComponent
  refine WP.seq (WP.mono (argumentPair_ok (by decide) (by decide) P.readSrc L.readSrc)
    fun u ⟨Ptr, Count, Mem, Keep⟩ => ?_)
  refine WP.mono (loadBE_ok (hs.of_keeps Keep (by decide)) hn hz hl hlen
    (by rw [Ptr]; exact bound) Count (by rw [Ptr, Keep.2.1, Keep.2.2]; exact readable)
    (by rw [Ptr]; exact disjoint.sub_right (Offset.sub_base base hz))) fun t ⟨V, O, K⟩ => ?_
  refine ⟨?_, ?_, (Keep.mono (by decide)).trans K⟩
  · rw [V, Ptr, Mem]
  · rw [← Mem]; exact O

end VG.Proof.Bignum.X86.Crt
