module

public import VerifiedGarbage.Proof.Bignum.Arm.ExponentScan
import VerifiedGarbage.Proof.Bignum.Arm.ExponentTest
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The ARMv7 validator implements the shared public-exponent predicate -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem exponentCheck_ok (s : State) {ep : BitVec 32} {eb : List Byte}
    (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length)
    (bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i])
    (ptr : s.gpr .r1 = ep) (count : s.gpr .lr = BitVec.ofNat 32 eb.length) :
    WP isa exponentCheck s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)).toNat ∧
      t.mem = s.mem ∧ Rest exponentClobbers s t := by
  rw [exponentCheck, WP.seq_iff]
  refine WP.mono (exponentScan_ok s positive countFit sourceFit read bytes ptr count) ?_
  rintro u ⟨lo, hi, memU, restU⟩
  refine WP.mono (exponentTest_ok u) ?_
  rintro t ⟨value, memT, restT⟩
  rw [lo, hi, exponentTest_value] at value
  exact ⟨value, memT.trans memU, restU.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
