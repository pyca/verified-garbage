module

public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Framework.Block

/-! # Initialize a public array index to a fixed small constant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem ArithmeticReady.of_mem {s t : State} {base : BitVec 32} {len w : Nat} {rs : List Reg}
    (h : ArithmeticReady base len w s) (mem : t.mem = s.mem) (rest : Rest rs s t)
    (ptr : t.gpr .r0 = base) : ArithmeticReady base len w t := by
  refine ⟨h.workspace.congr rest.wr, ?_, ?_, ptr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem]; exact h.layout
  · rw [mem]; exact h.width
  · rw [mem]; exact h.inverse
  · rw [mem]; exact h.modulus
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · rw [mem, rest.sp]; exact h.saved

theorem smallConstArgs_ok (s : State) (o value : BitVec 32)
    (ho : encodable o = true) (hv : encodable value = true) :
    WP isa (.block (smallConstArgs o value)) s fun t =>
      t.gpr .r2 = o ∧ t.gpr .r5 = value ∧ t.mem = s.mem ∧ Rest [.r2, .r5] s t := by
  unfold smallConstArgs
  refine wp_mov (op2_imm ho) fun u h => ?_
  refine wp_mov (op2_imm hv) fun t j => WP.block_nil ?_
  exact ⟨(j.other .r2 (by decide)).trans h.gpr, j.gpr, j.mem.trans h.mem,
    (h.rest (by decide)).trans (j.rest (by decide))⟩

theorem smallConst_ok (s : State) {base : BitVec 32} {len w o : Nat} (value : BitVec 32)
    (h : ArithmeticReady base len w s) (ho : o < 8) (ho0 : o ≠ 0)
    (encO : encodable (BitVec.ofNat 32 o) = true) (encV : encodable value = true) :
    WP isa (smallConst (BitVec.ofNat 32 o) value) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w o = value.toNat ∧
      w32 t.mem (State.addr base) (arrAt w o) = value.toNat ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [smallConst, WP.seq_iff]
  refine WP.mono (smallConstArgs_ok s _ value encO encV) ?_
  rintro u ⟨index, val, mem, rest⟩
  have ready := h.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.ptr)
  refine WP.mono (ArithmeticReady.setSmall u ready ho ho0 index) ?_
  rintro t ⟨next, number, low, keeps, frame, keep⟩
  rw [val] at number low
  rw [mem] at keeps frame
  exact ⟨next, number, low, keeps, frame, (rest.mono (by decide)).trans keep⟩

end VG.Proof.Bignum.Arm
