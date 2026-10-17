module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivStackWord
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Save the register-passed output, modulus, and length before preparing calls -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem savedArguments_slots : Spill.Slots 64 76 savedArguments := by decide +kernel

theorem saveRegs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivContext g bs s)
    (output : s.gpr .r0 = g.output) (modulus : s.gpr .r2 = g.sources 0) (count : s.gpr .r3 = BitVec.ofNat 32 g.length) :
    WP isa (.block saveRegs) s fun t => PrivContext g bs t ∧
      (∀ i < 3, t.mem.readW (off (State.addr g.stack) (64 + 4 * i)) 32 = slotValue g i) ∧
      t.gpr .r12 = g.stack ∧ Frame [g.innerRegion] s.mem t.mem ∧ Rest [.r12] s t := by
  unfold saveRegs
  refine wp_stackAddr (by decide) fun u moved => ?_
  have ptr : u.gpr .r12 = g.stack := by simpa only [BitVec.add_zero, h.sp] using moved.gpr
  have fit := h.valid.stackHigh
  have ws := h.inner.congr moved.wr
  obtain ⟨trace, t, run, regs, rd, wr, mem⟩ := Spill.save_block_ok (b := .r12) savedArguments_slots
    (s := u) (by rw [ptr]; simp only [frameBytes] at fit; omega)
    (fun d _ hd => by rw [ptr]; exact ws.write (by simp only [frameBytes]; omega))
  have rest : Rest [.r12] s t := (moved.rest (by simp)).trans
    ⟨fun r _ => congrFun regs r, rd, wr, (Exec.rdwr run).2.2⟩
  have saved := Spill.saveMem_saved (State.addr g.stack) u.gpr u.mem savedArguments savedArguments_slots
  have frame : Frame [g.innerRegion] s.mem t.mem := by
    rw [mem, ptr]
    have f := Spill.saveMem_frame u.mem (State.addr g.stack) u.gpr (L := frameBytes) (by decide) savedArguments
      (by intro p hp; simp only [savedArguments, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl <;> decide)
    simpa only [moved.mem, PrivGeometry.innerRegion] using f
  refine ⟨trace, t, run, h.after (frame.mono (by simp [bodyWrites])) rest, ?_, ?_, frame, rest⟩
  · intro i hi
    rw [mem, ptr]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact (saved (.r0, oOut) (by simp [savedArguments])).trans ((moved.other .r0 (by decide)).trans output)
    · exact (saved (.r2, oN) (by simp [savedArguments])).trans ((moved.other .r2 (by decide)).trans modulus)
    · exact (saved (.r3, oK) (by simp [savedArguments])).trans ((moved.other .r3 (by decide)).trans count)
  · rw [regs]; exact ptr
end VG.Proof.Rsa.Arm
