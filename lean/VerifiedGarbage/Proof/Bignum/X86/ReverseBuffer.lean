module
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.X86.StoreBE
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Serialize a nonempty native integer buffer as exact big-endian octets -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86
open VG.Proof.Mont.X86

theorem reverseBuffer_ok (s : State) {src dst : BitVec 32} {n : Nat}
    (hn : 0 < n) (srcFit : src.toNat + n ≤ 2 ^ 32) (dstFit : dst.toNat + n ≤ 2 ^ 32)
    (countFits : n < 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr src) n)
    (write : InRegions s.wr (byteAddr dst) n)
    (sep : Region.Disjoint ⟨byteAddr src, n⟩ ⟨byteAddr dst, n⟩)
    (p0 : s.gpr .ebx = dst) (p1 : s.gpr .esi = src + BitVec.ofNat 32 (n - 1))
    (count : s.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa reverseBytes s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr dst) n = Spec.Rsa.i2osp (s.mem.read (byteAddr src) n).toNat n ∧
      Frame [⟨byteAddr dst, n⟩] s.mem t.mem ∧
      t.gpr .ebx = dst + BitVec.ofNat 32 n ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  refine WP.mono (reverseBytes_ok s (reverseCtx_of_regions s src dst countFits srcFit dstFit read write sep)
    hn p1 p0 count) ?_
  intro t inv
  exact ⟨inv.i2osp srcFit dstFit, inv.frame dstFit, inv.dest, inv.rest⟩

end VG.Proof.Bignum.X86
