module

import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Mont.X86.Square.InputMath
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Proof.Mont
open VG.X86.RegUpd

theorem low_mask (v : Nat) : BitVec.ofNat 64 v &&& BitVec.ofNat 64 (2^32-1) = BitVec.ofNat 64 (v%2^32) := by
  rw [← BitVec.ofNat_and, Nat.and_two_pow_sub_one_eq_mod]

theorem shr32 {v : Nat} (hv : v<2^64) :
    (BitVec.ofNat 64 v) >>> 32 = BitVec.ofNat 64 (v/2^32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self ..) hv)]

def carryState (s : State) : State :=
  let t1 := (XOp.bin .movdqa .xmm2 .xmm3).exec s
  let t2 := (XOp.bin .pand .xmm2 .xmm7).exec t1
  let t3 := (XOp.bin .paddq .xmm0 .xmm2).exec t2
  let t4 := (XOp.shift .psrlq .xmm3 32).exec t3
  (XOp.bin .paddq .xmm1 .xmm3).exec t4

theorem run_carry (s : State) : runBlock isa VG.Impl.Mont.X86.Rt.Square.carryIn s = some (carryState s) := by rfl

theorem carry_values {s : State} {l h c : Nat}
    (low : s.xmm .xmm0 = packed (BitVec.ofNat 64 l))
    (high : s.xmm .xmm1 = packed (BitVec.ofNat 64 h))
    (carry : s.xmm .xmm3 = packed (BitVec.ofNat 64 c))
    (mask : s.xmm .xmm7 = packed (BitVec.ofNat 64 (2^32-1))) (hc : c<2^64) :
    (carryState s).xmm .xmm0 = packed (BitVec.ofNat 64 (l+c%2^32)) ∧
    (carryState s).xmm .xmm1 = packed (BitVec.ofNat 64 (h+c/2^32)) ∧
    (carryState s).xmm .xmm3 = packed (BitVec.ofNat 64 (c/2^32)) ∧
    (carryState s).xmm .xmm7 = s.xmm .xmm7 := by
  have shift (a : BitVec 64) : XShiftOp.eval .psrlq (packed a) (32 : BitVec 8) = packed (a >>> 32) :=
    packed_shr a (by decide)
  simp only [carryState, XOp.exec]
  simp (disch := decide) only [xmm_setXmm_self, xmm_setXmm_of_ne, eval_movdqa, low, high, carry, mask,
    packed_and, low_mask, packed_add, shift, shr32 hc, BitVec.ofNat_add, and_self]

theorem carry_scalar (s : State) :
    (carryState s).gpr = s.gpr ∧ (carryState s).mem = s.mem ∧
    (carryState s).rd = s.rd ∧ (carryState s).wr = s.wr := by
  simp only [carryState, XOp.exec, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, and_self]

end VG.Proof.Mont.X86.Square
