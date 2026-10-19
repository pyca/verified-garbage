module

public import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputArgs
public import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer

/-! # Accepted RSA output is retained; rejected output is zeroed in constant time -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

theorem acceptance_byte_mask (b : Bool) (v : Byte) :
    v &&& (-BitVec.ofNat 32 b.toNat).setWidth 8 = if b then v else 0 :=
  VG.Proof.Rsa.acceptance_byte_mask b v

theorem acceptance_bytes_mask (b : Bool) (bs : List Byte) :
    bs.map (· &&& (-BitVec.ofNat 32 b.toNat).setWidth 8) = if b then bs else List.replicate bs.length 0 :=
  VG.Proof.Rsa.acceptance_bytes_mask b bs

theorem maskOutput_ok (s : State) {dst : BitVec 32} {k : Nat} {accepted : Bool}
    (positive : 0 < k) (countFit : k < 2 ^ 32) (outputFit : dst.toNat + k ≤ 2 ^ 32)
    (write : InRegions s.wr (State.addr dst) k)
    (stackFit : s.sp.toNat + 52 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4)
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat)
    (ptr : s.gpr .r4 = dst) (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa maskOutput s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if accepted then Spec.Rsa.bytesAt s.mem (State.addr dst) k else List.replicate k 0) ∧
      t.gpr .r0 = BitVec.ofNat 32 accepted.toNat ∧
      Frame [⟨State.addr dst, k⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r4, .lr] s t := by
  rw [maskOutput, WP.seq_iff]
  refine WP.mono (maskOutputArgs_ok s stackFit read) ?_
  rintro u ⟨out, len, bit, mask, memU, restU⟩
  rw [flag] at bit mask
  rw [WP.seq_iff]
  refine WP.mono (maskBuffer_ok u positive countFit outputFit (by rw [restU.wr]; exact write)
    (out.trans ptr) (len.trans count)) ?_
  rintro v ⟨bytes, frame, restV⟩
  rw [mask, memU, acceptance_bytes_mask] at bytes
  have length : (Spec.Rsa.bytesAt s.mem (State.addr dst) k).length = k := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  rw [length] at bytes
  refine wp_mov (op2_reg _ _) fun t a => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, (restU.mono (by simp)).trans ((restV.mono (by simp)).trans (a.rest (by simp)))⟩
  · rw [a.mem]; exact bytes
  · rw [a.gpr, restV.gpr .r4 (by simp), bit]
  · rw [a.mem]
    rw [memU] at frame
    exact frame

end VG.Proof.Bignum.Arm
