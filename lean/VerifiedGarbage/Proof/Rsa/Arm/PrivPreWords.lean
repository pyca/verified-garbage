module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
import VerifiedGarbage.Proof.Bignum.Arm.PcHead
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Compute the reusable public precomputation length from the saved modulus length -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_dp wp_mov op2_imm op2_lsr op2_lsl dpVal)

theorem preWords_ok (r : Reg) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (.block (preWords r)) s fun t =>
      t.gpr r = BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length) ∧
      t.mem = s.mem ∧ Rest [r] s t := by
  have count : s.mem.readW (off (State.addr g.stack) oK) 32 = BitVec.ofNat 32 g.length := slots 2 (by decide)
  have kn : (BitVec.ofNat 32 g.length).toNat = g.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.valid.maxLength; omega)]
  have words := modulus_words_word (BitVec.ofNat 32 g.length) (by rw [kn]; have := h.valid.maxLength; omega)
  rw [kn] at words
  unfold preWords
  refine wp_loadStack (a := off (State.addr g.stack) oK) (by decide)
    (by rw [h.sp]; exact addr_add (by have := h.valid.stackHigh; simp only [oK, frameBytes] at *; omega))
    (h.inner.read (by decide)) fun u a => ?_
  refine wp_dp (op2_imm (by decide)) fun v b => ?_
  refine wp_mov (op2_lsr (by decide)) fun z c => ?_
  refine wp_mov (op2_lsl (by decide)) fun t d => WP.block_nil ?_
  refine ⟨?_, d.mem.trans (c.mem.trans (b.mem.trans a.mem)),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans ((c.rest (by simp)).trans (d.rest (by simp))))⟩
  rw [d.gpr, c.gpr, b.gpr, dpVal, a.gpr, count, words, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 32 (Spec.Rsa.modulusWords g.length) * BitVec.ofNat 32 2 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm]
end VG.Proof.Rsa.Arm
