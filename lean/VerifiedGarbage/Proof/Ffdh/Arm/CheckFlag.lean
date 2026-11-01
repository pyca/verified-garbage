module

public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! Save comparison flags inside RSA's unused FFDH header slot. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest wp_str)

theorem saveFlag_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa (.block VG.Impl.Ffdh.Arm.saveFlag) s fun t => ArithmeticReady base len w t ∧
      t.mem.readW (off (State.addr base) 136) 32 = s.gpr .r11 ∧
      (∀ q < 8, numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest [] s t := by
  have size : 256 ≤ 8 * len := by
    have := h.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  unfold VG.Impl.Ffdh.Arm.saveFlag
  refine wp_str (a := off (State.addr base) 136) (by decide)
    (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega))
    (h.workspace.write (by omega)) fun t a => WP.block_nil ?_
  have rest : Rest [] s t := a.rest []
  obtain ⟨ready, frame, arrays⟩ := h.after_header (d := 136) (by decide) (by decide) a.mem rest
    ((rest.gpr .r0 (by simp)).trans h.ptr)
  exact ⟨ready, by rw [a.mem, Mem.readW_writeW_self32], arrays, frame, rest⟩

end VG.Proof.Ffdh.Arm
