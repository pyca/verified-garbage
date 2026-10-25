module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtBodyInput
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.StackPair
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.WideMul

/-! # Invalid public RSA moduli produce failure and an all-zero output -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem crt_failArgs_ok (s : State) {g : CrtGeometry} (h : CrtCallStack g s) :
    WP isa (.block PublicFn.failArgs) s fun t => t.gpr .r0 = g.output ∧ t.gpr .lr = BitVec.ofNat 32 g.length ∧
      t.gpr .r2 = 0 ∧ t.mem = s.mem ∧ Rest [.r0, .r2, .lr] s t := by
  change WP isa (.block ([.ldrSp .r0 4, .ldrSp .lr 12] ++ [.mov .r2 (.imm 0)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (stackPair_ok s .r0 .lr 4 12 (by decide) (by decide) (by decide)
    (by have := h.nowrap; omega) (by have := h.nowrap; omega)
    (h.read (by decide)) (h.read (by decide))) ?_
  rintro u ⟨output, count, mem, rest⟩
  refine wp_mov (op2_imm (by decide)) fun t a => WP.block_nil ?_
  exact ⟨(a.other .r0 (by decide)).trans (output.trans h.output),
    (a.other .lr (by decide)).trans (count.trans h.count), a.gpr, a.mem.trans mem,
    (rest.mono (by decide)).trans (a.rest (by decide))⟩

theorem crt_fail_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtBodyInput g bs s) :
    WP isa PublicFn.fail s fun t => t.gpr .r0 = 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr g.output) g.length = List.replicate g.length 0 ∧
      Frame [⟨State.addr g.output, g.length⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [PublicFn.fail, WP.seq_iff]
  refine WP.mono (crt_failArgs_ok s h.stack) ?_
  rintro u ⟨output, count, mask, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (maskBuffer_ok u (by have := h.buffers.lengthValid.1; omega)
    (by have := h.buffers.lengthValid.2; omega) h.buffers.outputFits
    (by rw [restU.wr]; exact h.buffers.write) output count) ?_
  rintro v ⟨bytes, frame, restV⟩
  have zero : (u.gpr .r2).setWidth 8 = (-BitVec.ofNat 32 false.toNat).setWidth 8 := by rw [mask]; rfl
  rw [zero, acceptance_bytes_mask] at bytes
  have length : (Spec.Rsa.bytesAt u.mem (State.addr g.output) g.length).length = g.length := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  simp only [Bool.false_eq_true, ite_false, length] at bytes
  refine wp_mov (op2_imm (by decide)) fun t a => WP.block_nil ?_
  refine ⟨a.gpr, ?_, ?_, (restU.mono (by decide)).trans
    ((restV.mono (by decide)).trans (a.rest (by decide)))⟩
  · rw [a.mem]; exact bytes
  · rw [a.mem, memU] at *; exact frame

end VG.Proof.Bignum.Arm
