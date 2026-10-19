module
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Impl.Bignum.X86.ExportArray

import VerifiedGarbage.Proof.Bignum.X86.ExportArrayArgs
import VerifiedGarbage.Proof.Bignum.X86.CopyRead
import VerifiedGarbage.Proof.Bignum.PackedRead
import VerifiedGarbage.Proof.Framework.Offset

/-! # Packed workspace export preserves its integer value and advances the destination -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86

theorem exportArray_ok {s : State} {base : Addr} {bytes n src : Nat} {dst : BitVec 32}
    (hs : Scr s base bytes) (positive : 0 < n) (countFit : 8 * n < 2 ^ 32) (bound : src + 8 * n ≤ bytes)
    (fit : dst.toNat + 8 * n ≤ 2 ^ 32) (write : InRegions s.wr (byteAddr dst) (8 * n))
    (apart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr dst, 8 * n⟩)
    (P : s.gpr .ebx = dst) :
    WP isa (exportArray n src) s fun t =>
      (t.mem.read (byteAddr dst) (8 * n)).toNat = wordsVal s.mem base src n ∧
      t.gpr .ebx = dst + BitVec.ofNat 32 (8 * n) ∧
      Frame [⟨byteAddr dst, 8 * n⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  let source := s.gpr .edi + BitVec.ofNat 32 src
  have nw := hs.nowrap
  have address : byteAddr source = off base src := hs.ea (by omega)
  have sourceNat : source.toNat = base.toNat + src := by
    simp only [source, BitVec.toNat_add, hs.edi_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : src < 2 ^ 32), Nat.mod_eq_of_lt (by omega : base.toNat + src < 2 ^ 32)]
  have sourceFit : source.toNat + 8 * n ≤ 2 ^ 32 := by rw [sourceNat]; omega
  unfold exportArray
  refine WP.seq (WP.mono (exportArrayArgs_ok n src s) fun u ⟨S, C, M, K⟩ => ?_)
  refine WP.mono (copyBuffers_ok (by omega) countFit sourceFit fit
    (by rw [K.2.1, K.2.2, address]; exact hs.read bound)
    (by rw [K.2.2]; exact write)
    (by rw [address]; exact apart.sub_left (Offset.sub_base base bound))
    S ((K.1 _ (by decide)).trans P) C) fun t ⟨Read, D, _, F, T⟩ => ?_
  refine ⟨?_, D, ?_, (K.mono (by decide)).trans T⟩
  · rw [Read, M, address, wordsVal_read]
  · rw [← M]; exact F

end VG.Proof.Bignum.X86
