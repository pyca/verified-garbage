module

public import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
public import VerifiedGarbage.Proof.Bignum.ByteWords

/-! # Forward copies preserve packed little-endian integer reads -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86

theorem CopyInv.read {s t : State} {src dst : BitVec 32} {n d width : Nat}
    (I : CopyInv s src dst n n t) (srcFit : src.toNat + n ≤ 2 ^ 32)
    (dstFit : dst.toNat + n ≤ 2 ^ 32) (bound : d + width ≤ n) :
    t.mem.read (byteAddr dst + BitVec.ofNat 64 d) width =
      s.mem.read (byteAddr src + BitVec.ofNat 64 d) width := by
  apply Mem.read_eq_of_bytes
  intro i hi
  rw [Mem.extractLsb'_read _ _ hi, Offset.add_add, Offset.add_add]
  have Eq := I.copied (d + i) (by omega)
  rw [byteAddr_add (by omega : dst.toNat + (d + i) < 2 ^ 32),
    byteAddr_add (by omega : src.toNat + (d + i) < 2 ^ 32)] at Eq
  exact Eq

theorem copyBuffers_ok {s : State} {src dst : BitVec 32} {n : Nat}
    (positive : 0 < n) (countFit : n < 2 ^ 32)
    (srcFit : src.toNat + n ≤ 2 ^ 32) (dstFit : dst.toNat + n ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr src) n)
    (write : InRegions s.wr (byteAddr dst) n)
    (apart : Region.Disjoint ⟨byteAddr src, n⟩ ⟨byteAddr dst, n⟩)
    (P : s.gpr .esi = src) (Q : s.gpr .ebx = dst) (C : s.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa VG.Impl.Bignum.X86.copyBytes s fun t =>
      t.mem.read (byteAddr dst) n = s.mem.read (byteAddr src) n ∧
      t.gpr .ebx = dst + BitVec.ofNat 32 n ∧ t.gpr .esi = src + BitVec.ofNat 32 n ∧
      Frame [⟨byteAddr dst, n⟩] s.mem t.mem ∧
      VG.Proof.Mont.X86.Keeps [.eax, .ebx, .esi, .ecx] s t := by
  refine WP.mono (copyBytes_ok s (copyCtx_of_regions s src dst countFit srcFit dstFit read write apart)
    positive P Q C) fun t I => ?_
  refine ⟨?_, I.dest, I.source, I.frame dstFit, I.rest⟩
  simpa only [BitVec.add_zero] using I.read srcFit dstFit (d := 0) (width := n) (by omega)

end VG.Proof.Bignum.X86
