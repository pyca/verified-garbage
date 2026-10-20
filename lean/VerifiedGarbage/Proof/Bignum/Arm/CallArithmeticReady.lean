module
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.CallStack
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Arithmetic readiness survives a callee's permitted writes below the stack. -/
@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand Keeps)
open VG.Proof.X25519.Arm (Rest)
theorem ArithmeticReady.after_call {s t : State} {base : BitVec 32} {len w o : Nat}
    (h : ArithmeticReady base len w s) (cs : CallStack base len s) (ho : o ≠ 0)
    (keeps : Keeps (State.addr base) len w o s.mem t.mem)
    (frame : Frame [⟨State.addr base, 8 * len⟩, FrameStack.belowA s.sp 48] s.mem t.mem)
    (rest : Rest roundClobbers s t) (ptr : t.gpr .r0 = base) :
    ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits; omega
  have op0 : Operand 0 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have kl := keeps_layout h.layout (by rw [h.width]; exact keeps)
  have oldM := keeps_array_num keeps fits op0 (Ne.symm ho)
  have oldLow := keeps_array_word (d := 0) (bits := 64) keeps fits op0 (Ne.symm ho) (by omega)
  simp only [Nat.add_zero] at oldLow
  refine ⟨⟨h.workspace.congr rest.wr, kl.2, kl.1.trans h.width, ptr, ?_, ?_, ?_, ?_, ?_⟩, oldM⟩
  · change ((t.mem.readW (off (State.addr base) (arrAt w 0)) 64).toNat *
      (t.mem.readW (off (State.addr base) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [oldLow, keeps_header_readW keeps size (d := 56) (bits := 64) (by decide)]
    exact h.inverse
  · rw [oldM]; exact h.modulus
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · rw [rest.sp]
    have sep : Region.Disjoint ⟨State.addr s.sp, 4⟩ (FrameStack.belowA s.sp 48) := by
      rw [FrameStack.belowA, FrameStack.addr_sub' cs.fit]
      exact (Offset.below_disjoint _ (by decide)).symm
    exact (frame.readW (r := ⟨State.addr s.sp, 4⟩) (Region.contains_self _ _)
      (by intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · subst r; exact h.stackSep
          · have er := List.mem_singleton.mp hr; subst r; exact sep) (by decide)).trans h.saved

end VG.Proof.Bignum.Arm
