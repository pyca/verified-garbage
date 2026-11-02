module

public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase

/-! # Buffer operations preserve workspace shape before factor validation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem LayoutFrameReady.of_mem {s t : State} {base : BitVec 32} {len w : Nat} {rs : List Reg}
    (h : LayoutFrameReady base len w s) (mem : t.mem = s.mem) (rest : Rest rs s t)
    (ptr : t.gpr .r0 = base) : LayoutFrameReady base len w t := by
  refine ⟨⟨h.workspace.congr rest.wr, ?_, ?_, ptr⟩, ?_, ?_, ?_⟩
  · rw [mem]; exact h.layout
  · rw [mem]; exact h.width
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · rw [mem, rest.sp]; exact h.saved

theorem LayoutFrameReady.after_array {s t : State} {base : BitVec 32} {len w o : Nat}
    (h : LayoutFrameReady base len w s) (keeps : Keeps (State.addr base) len w o s.mem t.mem)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem)
    (rest : Rest roundClobbers s t) (ptr : t.gpr .r0 = base) : LayoutFrameReady base len w t := by
  have kl := keeps_layout h.layout (by rw [h.width]; exact keeps)
  refine ⟨⟨h.workspace.congr rest.wr, kl.2, kl.1.trans h.width, ptr⟩, ?_, ?_, ?_⟩
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · exact saved_base_kept frame h.stackSep h.saved rest.sp

end VG.Proof.Bignum.Arm
