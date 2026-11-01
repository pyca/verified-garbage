module

public import VerifiedGarbage.Impl.Bignum.Arm.ExpControls
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Initialize exponent control slots while preserving every RSA arithmetic array -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest wp_str)

theorem expControls_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa (.block expControls) s fun t => ArithmeticReady base len w t ∧
      t.mem.readW (off (State.addr base) 128) 32 = s.gpr .r1 ∧
      t.mem.readW (off (State.addr base) 132) 32 = s.gpr .r2 ∧
      (∀ q < 8, numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest [] s t := by
  have size : 256 ≤ 8 * len := by
    have := h.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  have addr (d : Nat) (hd : d ≤ 252) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega)
  unfold expControls
  refine wp_str (a := off (State.addr base) 128) (by decide) (addr 128 (by decide))
    (h.workspace.write (by omega)) fun u a => ?_
  have restU : Rest [] s u := a.rest []
  obtain ⟨readyU, frameU, arraysU⟩ := h.after_header (d := 128) (by decide) (by decide) a.mem restU
    ((restU.gpr .r0 (by simp)).trans h.ptr)
  refine wp_str (a := off (State.addr base) 132) (by decide)
    (by rw [restU.gpr .r0 (by simp)]; exact addr 132 (by decide))
    (by rw [restU.wr]; exact h.workspace.write (by omega)) fun t b => WP.block_nil ?_
  have restT : Rest [] u t := b.rest []
  obtain ⟨readyT, frameT, arraysT⟩ := readyU.after_header (d := 132) (by decide) (by decide) b.mem restT
    ((restT.gpr .r0 (by simp)).trans readyU.ptr)
  refine ⟨readyT, ?_, ?_, fun q hq => (arraysT q hq).trans (arraysU q hq), frameU.trans frameT, restU.trans restT⟩
  · have outside := writeW32_outside u.mem (State.addr base) (d := 132) (u.gpr .r2) (by decide)
    rw [b.mem, outside_read32 outside (d := 128) (by decide) (by decide), a.mem, Mem.readW_writeW_self32]
  · rw [b.mem, Mem.readW_writeW_self32, restU.gpr .r2 (by simp)]

end VG.Proof.Bignum.Arm
