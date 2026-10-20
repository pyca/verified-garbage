module

public import VerifiedGarbage.Proof.Bignum.X86.ExponentScan
import VerifiedGarbage.Proof.Bignum.X86.ExponentTest
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The i686 validator implements the shared public-exponent predicate -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem exponentCheck_ok (s : State) {ep : BitVec 32} {eb : List Byte}
    (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr ep) eb.length)
    (bytes : ∀ i (hi : i < eb.length), s.mem (byteAddr ep + BitVec.ofNat 64 i) = eb[i])
    (ptr : s.gpr .esi = ep) (count : s.gpr .ecx = BitVec.ofNat 32 eb.length) :
    WP isa exponentCheck s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)).toNat ∧
      t.mem = s.mem ∧ Keeps exponentClobbers s t := by
  rw [exponentCheck, WP.seq_iff]
  refine WP.mono (exponentScan_ok s positive countFit sourceFit read bytes ptr count) ?_
  rintro u ⟨lo, hi, memU, restU⟩
  refine WP.mono (exponentTest_ok u) ?_
  rintro t ⟨value, memT, restT⟩
  rw [lo, hi, exponentTest_value] at value
  exact ⟨value, memT.trans memU, restU.trans (restT.mono (by decide))⟩

theorem exponentCheck_words_ok (s : State) {ep : BitVec 32} {eb : List Byte}
    (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr ep) eb.length)
    (bytes : ∀ i (hi : i < eb.length), s.mem (byteAddr ep + BitVec.ofNat 64 i) = eb[i])
    (ptr : s.gpr .esi = ep) (count : s.gpr .ecx = BitVec.ofNat 32 eb.length) :
    WP isa exponentCheck s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)).toNat ∧
      t.gpr .ebx = BitVec.ofNat 32 (Spec.Rsa.os2ip eb % 2 ^ 32) ∧
      t.gpr .edx = BitVec.ofNat 32 (exponentHigh (Spec.Rsa.os2ip eb)) ∧
      t.mem = s.mem ∧ Keeps exponentClobbers s t := by
  rw [exponentCheck, WP.seq_iff]
  refine WP.mono (exponentScan_ok s positive countFit sourceFit read bytes ptr count) ?_
  rintro u ⟨lo, hi, memU, restU⟩
  refine WP.mono (exponentTest_ok u) ?_
  rintro t ⟨value, memT, restT⟩
  rw [lo, hi, exponentTest_value] at value
  exact ⟨value, (restT.1 .ebx (by decide)).trans lo,
    (restT.1 .edx (by decide)).trans hi, memT.trans memU, restU.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.X86
