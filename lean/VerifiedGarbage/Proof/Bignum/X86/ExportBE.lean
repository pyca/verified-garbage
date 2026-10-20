module
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.X86.StoreBE

import VerifiedGarbage.Proof.Bignum.X86.StoreBEArgs
import VerifiedGarbage.Proof.Bignum.X86.ReverseBuffer
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Exact big-endian export of the low bytes of an RSA workspace integer -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem storeBE_read_ok {s : State} {base : Addr} {bytes src len : Nat}
    (hs : Scr s base bytes) (hl : 0 < len) (ho : src + len ≤ bytes)
    (hc : s.gpr .ecx = BitVec.ofNat 32 len)
    (dstFit : (s.gpr .ebx).toNat + len ≤ 2 ^ 32)
    (write : InRegions s.wr (byteAddr (s.gpr .ebx)) len)
    (sep : Region.Disjoint ⟨off base src, len⟩ ⟨byteAddr (s.gpr .ebx), len⟩) :
    WP isa (storeBE src) s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (s.gpr .ebx)) len =
        Spec.Rsa.i2osp (s.mem.read (off base src) len).toNat len ∧
      Frame [⟨byteAddr (s.gpr .ebx), len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have nw := hs.nowrap
  let source := s.gpr .edi + BitVec.ofNat 32 src
  have sourceAddr : byteAddr source = off base src := hs.ea (by omega)
  have sourceNat : source.toNat = base.toNat + src := by
    dsimp only [source]
    rw [BitVec.toNat_add, hs.edi_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show src < 2 ^ 32 by omega), Nat.mod_eq_of_lt (by omega)]
  unfold storeBE
  refine WP.seq (WP.mono (storeBEArgs_ok s src hl hc) fun u ⟨P, M, K⟩ => ?_)
  refine WP.mono (reverseBuffer_ok u (src := source) (dst := s.gpr .ebx) hl
    (by omega) dstFit (by have := hs.size_lt; omega)
    (by rw [K.2.1, K.2.2, sourceAddr]; exact hs.read ho)
    (by rw [K.2.2]; exact write) (by rw [sourceAddr]; exact sep)
    (K.1 .ebx (by decide)) P (by rw [K.1 .ecx (by decide), hc]))
    fun t ⟨V, F, _, T⟩ => ?_
  rw [sourceAddr, M] at V
  rw [M] at F
  exact ⟨V, F, (K.mono (by decide)).trans T⟩

theorem storeBE_ok {s : State} {base : Addr} {bytes src n len : Nat}
    (hs : Scr s base bytes) (hl : 0 < len) (hlen : len ≤ 8 * n)
    (ho : src + 8 * n ≤ bytes) (hc : s.gpr .ecx = BitVec.ofNat 32 len)
    (valueFit : wordsVal s.mem base src n < 2 ^ (8 * len))
    (dstFit : (s.gpr .ebx).toNat + len ≤ 2 ^ 32)
    (write : InRegions s.wr (byteAddr (s.gpr .ebx)) len)
    (sep : Region.Disjoint ⟨off base src, len⟩ ⟨byteAddr (s.gpr .ebx), len⟩) :
    WP isa (storeBE src) s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (s.gpr .ebx)) len =
        Spec.Rsa.i2osp (wordsVal s.mem base src n) len ∧
      Frame [⟨byteAddr (s.gpr .ebx), len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .esi, .ecx] s t := by
  refine WP.mono (storeBE_read_ok hs hl (by omega) hc dstFit write sep) fun t ⟨V, F, K⟩ => ?_
  have eq : (s.mem.read (off base src) (8 * n)).toNat = wordsVal s.mem base src n := by
    rw [wordsVal_eq_val32, ← read_eq_val32]
    congr 2 <;> omega
  rw [read_prefix_value s.mem _ hlen (by rw [eq]; exact valueFit), eq] at V
  exact ⟨V, F, K⟩

end VG.Proof.Bignum.X86
