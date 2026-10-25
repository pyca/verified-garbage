module

public import VerifiedGarbage.Impl.Bignum.Arm.CombDigit
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay

/-! Big-endian exponent bytes are read at public, bounded bit positions. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

abbrev loadClobbers : List Reg := [.r2,.r11,.r12]

structure Source (src : BitVec 32) (bs : List Byte) (s : State) : Prop where
  fits : src.toNat + bs.length ≤ 2^32
  readable : InRegions (s.rd ++ s.wr) (State.addr src) bs.length
  bytes : ∀ j (hj : j < bs.length), s.mem (State.addr src + BitVec.ofNat 64 j) = bs[j]'hj

theorem load_ok (s : State) {src : BitVec 32} {bs : List Byte} {k : Nat}
    (source : Source src bs s) (bound : k < 8*bs.length) (size : bs.length < 2^32)
    (ptr : s.gpr .r4 = src) (length : s.gpr .r5 = BitVec.ofNat 32 bs.length)
    (index : s.gpr .r9 = BitVec.ofNat 32 k) (indexFit : k < 2^32) :
    WP isa (.block VG.Impl.Bignum.Arm.CombDigit.load) s fun t =>
      t.gpr .r11 = (bs[bs.length-1-k/8]'(by omega)).setWidth 32 ∧
      t.gpr .r2 = BitVec.ofNat 32 (k%8) ∧ t.z = decide (k%8=0) ∧
      t.mem = s.mem ∧ Rest loadClobbers s t := by
  have quotient : BitVec.ofNat 32 k >>> 3 = BitVec.ofNat 32 (k/8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt indexFit]
    rw [Nat.shiftRight_eq_div_pow]
    change k/8 = k/8%2^32
    rw [Nat.mod_eq_of_lt (by omega)]
  have rem : BitVec.ofNat 32 k &&& 7 = BitVec.ofNat 32 (k%8) := by
    change BitVec.ofNat 32 k &&& BitVec.ofNat 32 (2^3-1) = _
    rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod]
  have offset : (BitVec.ofNat 32 bs.length - BitVec.ofNat 32 (k/8)) - 1 =
      BitVec.ofNat 32 (bs.length-1-k/8) := by
    rw [BitVec.ofNat_sub_ofNat_of_le bs.length (k/8) (by omega) (by omega)]
    change BitVec.ofNat 32 (bs.length-k/8) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (bs.length-k/8) 1 (by decide) (by omega)]
    congr 1
    omega
  unfold VG.Impl.Bignum.Arm.CombDigit.load
  refine wp_mov (by rfl) fun a one => ?_
  refine wp_dp (op2_reg _ _) fun b two => ?_
  refine wp_dp (op2_imm (by decide)) fun c three => ?_
  refine wp_dp (op2_reg _ _) fun d four => ?_
  have kept : Rest loadClobbers s d :=
    (((one.rest (by decide)).trans (two.rest (by decide))).trans
      (three.rest (by decide))).trans (four.rest (by decide))
  have address : d.gpr .r12 = src + BitVec.ofNat 32 (bs.length-1-k/8) := by
    rw [four.gpr,three.gpr,two.gpr,one.gpr]
    change c.gpr .r4 + (a.gpr .r5 - (s.gpr .r9 >>> 3) - 1) = _
    rw [three.other .r4 (by decide),two.other .r4 (by decide),one.other .r4 (by decide),
      one.other .r5 (by decide),ptr,length,index,quotient,offset]
  have addr : State.addr (d.gpr .r12 + BitVec.ofNat 32 0) =
      State.addr src + BitVec.ofNat 64 (bs.length-1-k/8) := by
    rw [address,BitVec.add_zero]
    exact VG.Arm.addr_add (by have := source.fits; omega)
  have read : InRegions (d.rd ++ d.wr) (State.addr src + BitVec.ofNat 64 (bs.length-1-k/8)) 1 := by
    rw [kept.rd,kept.wr]
    exact VG.CallLay.inRegions_sub source.readable (by omega) (by have := source.fits; omega)
  refine wp_ldrb (by decide) addr read fun e five => ?_
  refine wp_dp (op2_imm (by decide)) fun f six => ?_
  refine wp_cmp (op2_imm (by decide)) fun t seven zero => WP.block_nil ?_
  have count : f.gpr .r2 = BitVec.ofNat 32 (k%8) := by
    rw [six.gpr]
    change e.gpr .r9 &&& 7 = _
    rw [five.other .r9 (by decide),kept.gpr .r9 (by decide),index,rem]
  refine ⟨?_,(congrArg (fun f => f .r2) seven.gpr).trans count,?_,?_,?_⟩
  · rw [seven.gpr,six.other .r11 (by decide),five.gpr]
    rw [four.mem,three.mem,two.mem,one.mem,source.bytes _ (by omega)]
  · rw [zero,count]
    change (BitVec.ofNat 32 (k%8) - BitVec.ofNat 32 0 == 0) = _
    rw [BitVec.sub_zero,ofNat_beq_zero (by omega)]
  · exact seven.mem.trans (six.mem.trans (five.mem.trans (four.mem.trans (three.mem.trans (two.mem.trans one.mem)))))
  · exact ((kept.trans (five.rest (by decide))).trans
      (six.rest (by decide))).trans (seven.rest _)

end VG.Proof.Bignum.Arm.CombDigit
