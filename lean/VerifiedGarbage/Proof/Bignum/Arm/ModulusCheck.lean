module
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.ModulusCheck
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckRead
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCalc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # ARMv7 modulus validation is exactly the shared RSA validity predicate -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem modulusCheck_ok (s : State) {src : BitVec 32} {k : Nat}
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (fit : src.toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (source : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (.block modulusCheck) s fun t =>
      t.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) k ∧
      t.mem = s.mem ∧ Rest [.r1, .r2, .r7, .r9] s t := by
  rw [modulusCheck, WP.block_append_iff]
  refine WP.mono (modulusCheckRead_ok s (by omega) fit read source count) ?_
  rintro u ⟨first, last, mem, rest⟩
  have byteNat (b : Byte) : (b.setWidth 32).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  have firstNat : (u.gpr .r1).toNat = (s.mem (State.addr src)).toNat := by rw [first, byteNat]
  have lastNat : (u.gpr .r2).toNat = (s.mem (State.addr src + BitVec.ofNat 64 (k - 1))).toNat := by rw [last, byteNat]
  have countNat : (u.gpr .r6).toNat = k := by
    rw [rest.gpr .r6 (by simp), count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (modulusCheckCalc_ok u (by rw [firstNat]; exact (s.mem _).isLt)
    (by rw [countNat]; exact hk) (by rw [countNat]; exact hk')) ?_
  rintro t ⟨zero, memT, keep⟩
  rw [firstNat, lastNat, countNat] at zero
  refine ⟨?_, memT.trans mem, (rest.mono (by simp)).trans (keep.mono (by simp))⟩
  rw [VG.Proof.Bignum.modulusValid_iff (bytesAt_length _ _ _) hk hk']
  simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, BitVec.add_zero] using zero

end VG.Proof.Bignum.Arm
