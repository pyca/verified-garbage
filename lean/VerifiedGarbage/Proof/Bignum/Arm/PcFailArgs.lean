module

import VerifiedGarbage.Proof.Bignum.Arm.PcHead
public import VerifiedGarbage.Proof.Bignum.Arm.PcStack
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Native-word count and output pointer for RSA rejection zeroing -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_dp wp_mov op2_imm op2_lsr op2_lsl dpVal)

theorem pcFailArgs_ok (s : State) {base dst src : BitVec 32} {len k : Nat}
    (stack : PcStack base dst src len k s) (hk : k ≤ 1024) (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (.block PcFn.failArgs) s fun t =>
      t.gpr .r0 = dst ∧ t.gpr .lr = BitVec.ofNat 32 (4 * Spec.Rsa.modulusWords k) ∧ t.gpr .r3 = 0 ∧
      t.mem = s.mem ∧ Rest [.r0, .r3, .lr] s t := by
  have kn : (s.gpr .r6).toNat = k := by rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have words := modulus_words_word (s.gpr .r6) (by rw [kn]; omega)
  rw [kn] at words
  unfold PcFn.failArgs
  refine wp_dp (op2_imm (by decide)) fun u h => ?_
  refine wp_mov (op2_lsr (by decide)) fun v j => ?_
  refine wp_mov (op2_lsl (by decide)) fun z l => ?_
  refine wp_loadStack (a := VG.Proof.Mont.off (State.addr s.sp) 4) (by decide)
    (by rw [l.sp, j.sp, h.sp]; exact addr_add (by have := stack.nowrap; omega))
    (by rw [l.rd, l.wr, j.rd, j.wr, h.rd, h.wr]; exact stack.read (by decide)) fun a q => ?_
  refine wp_mov (op2_imm (by decide)) fun t r => WP.block_nil ?_
  refine ⟨?_, ?_, r.gpr, r.mem.trans (q.mem.trans (l.mem.trans (j.mem.trans h.mem))),
    (h.rest (by simp)).trans ((j.rest (by simp)).trans ((l.rest (by simp)).trans
      ((q.rest (by simp)).trans (r.rest (by simp)))))⟩
  · rw [r.other .r0 (by decide), q.gpr, l.mem, j.mem, h.mem]; exact stack.savedOutput
  · rw [r.other .lr (by decide), q.other .lr (by decide), l.gpr, j.gpr, h.gpr, dpVal, words,
      BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 (Spec.Rsa.modulusWords k) * BitVec.ofNat 32 4 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]

end VG.Proof.Bignum.Arm
