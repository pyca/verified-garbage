module
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Impl.Bignum.X86.ImportArray

import VerifiedGarbage.Proof.Bignum.X86.ImportArrayArgs
import VerifiedGarbage.Proof.Bignum.X86.CopyRead
import VerifiedGarbage.Proof.Bignum.PackedRead
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem

/-! # Packed imports preserve their integer value and advance the input -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86

theorem importArray_ok {s : State} {base : Addr} {bytes n dst : Nat} {src : BitVec 32}
    (hs : Scr s base bytes) (positive : 0 < n) (countFit : 8 * n < 2 ^ 32) (bound : dst + 8 * n ≤ bytes)
    (fit : src.toNat + 8 * n ≤ 2 ^ 32) (read : InRegions (s.rd ++ s.wr) (byteAddr src) (8 * n))
    (apart : Region.Disjoint ⟨byteAddr src, 8 * n⟩ ⟨base, bytes⟩)
    (P : s.gpr .esi = src) :
    WP isa (importArray n dst) s fun t =>
      wordsVal t.mem base dst n = (s.mem.read (byteAddr src) (8 * n)).toNat ∧
      t.gpr .esi = src + BitVec.ofNat 32 (8 * n) ∧
      Frame [⟨off base dst, 8 * n⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  let target := s.gpr .edi + BitVec.ofNat 32 dst
  have nw := hs.nowrap
  have address : byteAddr target = off base dst := hs.ea (by omega)
  have targetNat : target.toNat = base.toNat + dst := by
    simp only [target, BitVec.toNat_add, hs.edi_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : dst < 2 ^ 32), Nat.mod_eq_of_lt (by omega : base.toNat + dst < 2 ^ 32)]
  have targetFit : target.toNat + 8 * n ≤ 2 ^ 32 := by rw [targetNat]; omega
  unfold importArray
  refine WP.seq (WP.mono (importArrayArgs_ok n dst s) fun u ⟨D, C, M, K⟩ => ?_)
  refine WP.mono (copyBuffers_ok (by omega) countFit fit targetFit
    (by rw [K.2.1, K.2.2]; exact read)
    (by rw [K.2.2, address]; exact hs.write bound)
    (by rw [address]; exact apart.sub_right (Offset.sub_base base bound))
    ((K.1 _ (by decide)).trans P) D C) fun t ⟨Read, _, S, F, T⟩ => ?_
  refine ⟨?_, S, ?_, (K.mono (by decide)).trans T⟩
  · rw [wordsVal_read, ← address, Read, M]
  · rw [address, M] at F; exact F

end VG.Proof.Bignum.X86
