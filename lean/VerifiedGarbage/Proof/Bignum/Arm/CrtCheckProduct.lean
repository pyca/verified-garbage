module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckProductState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Full-width factor validation against the original modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_checkProduct_ok (s : State) {base : BitVec 32} {size len o a d w : Nat}
    (h : CrtCheckProductInput base size len o a d w s) :
    WP isa checkProduct s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a (4 * w + 2) =
        Spec.Rsa.Mont.numAt s.mem (State.addr base) w 0 then 1 else 0) ∧
      Outs (State.addr base) [(d, 4 * (4 * w + 2)), (o, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [checkProduct, WP.seq_iff]
  refine WP.mono (crt_padComparison_ready s h) ?_
  rintro u ⟨ready, first, second, outsideU, restU⟩
  refine WP.mono (crt_compareProduct_ok u ready) ?_
  rintro t ⟨value, outsideT, frameT, ptrT, restT⟩
  rw [first, second] at value
  exact ⟨value, (Outs.of_outside outsideU (by simp)).trans (Outs.of_outside outsideT (by simp)),
    (outside_workspace outsideU h.padding.fits).trans frameT, ptrT, restU.trans restT⟩

end VG.Proof.Bignum.Arm
