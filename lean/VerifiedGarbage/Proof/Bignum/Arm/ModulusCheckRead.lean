module

public import VerifiedGarbage.Impl.Bignum.Arm.ModulusCheck
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Read the leading byte and parity byte of an RSA modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldrb wp_dp op2_reg op2_imm dpVal)

theorem modulusCheckRead_ok (s : State) {src : BitVec 32} {k : Nat}
    (hk : 0 < k) (fit : src.toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (source : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (.block modulusCheckRead) s fun t =>
      t.gpr .r1 = (s.mem (State.addr src)).setWidth 32 ∧
      t.gpr .r2 = (s.mem (State.addr src + BitVec.ofNat 64 (k - 1))).setWidth 32 ∧
      t.mem = s.mem ∧ Rest [.r1, .r2] s t := by
  have first : InRegions (s.rd ++ s.wr) (State.addr src) 1 := by
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub (off := 0) read (by omega) (by omega)
  have last : InRegions (s.rd ++ s.wr) (State.addr src + BitVec.ofNat 64 (k - 1)) 1 :=
    CallLay.inRegions_sub read (by omega) (by omega)
  unfold modulusCheckRead
  refine wp_ldrb (a := State.addr src) (by decide) (by rw [source]; simp) first fun u h => ?_
  refine wp_dp (op2_reg _ _) fun v j => ?_
  refine wp_dp (op2_imm (by decide)) fun z l => ?_
  have lastAddr : State.addr (z.gpr .r2 + BitVec.ofNat 32 0) = State.addr src + BitVec.ofNat 64 (k - 1) := by
    rw [l.gpr, dpVal, j.gpr, dpVal, h.other .r4 (by decide), h.other .r6 (by decide), source, count]
    simp only [BitVec.add_zero]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg]
    change State.addr (src + (BitVec.ofNat 32 k - BitVec.ofNat 32 1)) = _
    rw [Offset.ofNat_sub_ofNat (by omega)]
    exact addr_add (by omega)
  refine wp_ldrb (a := State.addr src + BitVec.ofNat 64 (k - 1)) (by decide) lastAddr
    (by rw [l.rd, l.wr, j.rd, j.wr, h.rd, h.wr]; exact last) fun t q => WP.block_nil ?_
  refine ⟨?_, ?_, q.mem.trans (l.mem.trans (j.mem.trans h.mem)),
    (h.rest (by simp)).trans ((j.rest (by simp)).trans ((l.rest (by simp)).trans (q.rest (by simp))))⟩
  · rw [q.other .r1 (by decide), l.other .r1 (by decide), j.other .r1 (by decide), h.gpr]
  · rw [q.gpr, l.mem, j.mem, h.mem]

end VG.Proof.Bignum.Arm
