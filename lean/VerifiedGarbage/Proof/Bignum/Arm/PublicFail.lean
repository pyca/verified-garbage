module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrepare
import VerifiedGarbage.Proof.Bignum.Arm.StackPair
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Bignum.Words

/-! # Invalid public keys produce an all-zero output and failure status -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem publicFailArgs_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    (h : PublicStack base dst np ep xp len k eLen s) :
    WP isa (.block PublicFn.failArgs) s fun t => t.gpr .r0 = dst ∧ t.gpr .lr = BitVec.ofNat 32 k ∧
      t.gpr .r2 = 0 ∧ t.mem = s.mem ∧ Rest [.r0, .r2, .lr] s t := by
  change WP isa (.block ([.ldrSp .r0 4, .ldrSp .lr 12] ++ [.mov .r2 (.imm 0)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (stackPair_ok s .r0 .lr 4 12 (by decide) (by decide) (by decide)
    (by have := h.nowrap; omega) (by have := h.nowrap; omega)
    (h.read (by decide) (by decide)) (h.read (by decide) (by decide))) ?_
  rintro u ⟨output, count, mem, rest⟩
  refine wp_mov (op2_imm (by decide)) fun t a => WP.block_nil ?_
  exact ⟨(a.other .r0 (by decide)).trans (output.trans h.savedOutput),
    (a.other .lr (by decide)).trans (count.trans h.savedCount), a.gpr, a.mem.trans mem,
    (rest.mono (by decide)).trans (a.rest (by decide))⟩

theorem publicFail_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicBodyInput base dst np ep xp len k eLen nb eb xb s) :
    WP isa PublicFn.fail s fun t => t.gpr .r0 = 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) k = List.replicate k 0 ∧
      Frame [⟨State.addr dst, k⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [PublicFn.fail, WP.seq_iff]
  refine WP.mono (publicFailArgs_ok s h.stack) ?_
  rintro u ⟨output, count, mask, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (maskBuffer_ok u (by have := h.buffers.minLength; omega)
    (by have := h.buffers.maxLength; omega) h.buffers.outputFit
    (by rw [restU.wr]; exact h.buffers.write) output count) ?_
  rintro v ⟨bytes, frame, restV⟩
  have zero : (u.gpr .r2).setWidth 8 = (-BitVec.ofNat 32 false.toNat).setWidth 8 := by rw [mask]; rfl
  rw [zero, acceptance_bytes_mask] at bytes
  have length : (Spec.Rsa.bytesAt u.mem (State.addr dst) k).length = k := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  simp only [Bool.false_eq_true, ite_false, length] at bytes
  refine wp_mov (op2_imm (by decide)) fun t a => WP.block_nil ?_
  refine ⟨a.gpr, ?_, ?_, (restU.mono (by decide)).trans
    ((restV.mono (by decide)).trans (a.rest (by decide)))⟩
  · rw [a.mem]; exact bytes
  · rw [a.mem]
    rw [memU] at frame
    exact frame

end VG.Proof.Bignum.Arm
