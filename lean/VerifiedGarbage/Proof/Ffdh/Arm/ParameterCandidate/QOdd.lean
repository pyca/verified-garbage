module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResidueBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/QOddLow.lean`, which only this module imported.
section

/-! Check the parity of q directly from the low bits of odd p. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

private theorem lowByte (b : Byte) : b.setWidth 32 &&& 3 = BitVec.ofNat 32 (b.toNat % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega : b.toNat < 2 ^ 32),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b.toNat % 4 < 2 ^ 32)]
  change b.toNat &&& (2 ^ 2 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem qOddLow_ok (s : State) (dst : BitVec 32) (n : Nat)
    (readOut : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 4)) 4)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12)) 4)
    (out : s.mem.readW (State.addr (s.sp + 4)) 32 = dst)
    (width : s.mem.readW (State.addr (s.sp + 12)) 32 = BitVec.ofNat 32 n)
    (read : InRegions (s.rd ++ s.wr) (State.addr (dst + BitVec.ofNat 32 n - 1)) 1) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd) s fun t =>
      (t.z = decide ((s.mem (State.addr (dst + BitVec.ofNat 32 n - 1))).toNat % 4 = 3) ∧ t.mem = s.mem) ∧
        Rest [.r2, .r4, .r5] s t := by
  have zero (b : Byte) : ((b.setWidth 32 &&& 3) - 3 == 0) = decide (b.toNat % 4 = 3) := by
    rw [lowByte, sub_beq_zero]
    exact ofNat_beq_eq (by omega) (by decide)
  refine withRest_all [.r2, .r4, .r5] ?_ (by rfl) (by rfl)
  change InRegions (s.rd ++ s.wr) (State.addr (s.sp + 4#32)) 4 at readOut
  change InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12#32)) 4 at readWidth
  change s.mem.readW (State.addr (s.sp + 4#32)) 32 = dst at out
  change s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 n at width
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd
  ffrun [BitVec.add_zero, readOut, readWidth, out, width, read, zero]

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem qOdd_ok {s : State} {dst : BitVec 32} {n : Nat} (h : ReadContext dst n s)
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)%2=1) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd) s fun t =>
      t.z=decide (((Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)-1)/2)%2=1) ∧
      t.mem=s.mem ∧ Rest [.r2,.r4,.r5] s t := by
  refine WP.mono (qOddLow_ok s dst n (h.frame.read (by decide)) (h.frame.read (by decide))
    h.out h.width (h.readable.low h.positive)) ?_
  rintro t ⟨⟨flag,memory⟩,rest⟩
  have last := candidate_mod8_last s.mem (State.addr dst) h.positive
  rw [←h.lastAddress] at last
  have low : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)%4 =
      (s.mem (State.addr (dst+BitVec.ofNat 32 n-1))).toNat%4 := by omega
  refine ⟨flag.trans (decide_eq_decide.mpr ?_),memory,rest⟩
  rw [←low]
  omega

end VG.Proof.Ffdh.Arm.ParameterCandidate
