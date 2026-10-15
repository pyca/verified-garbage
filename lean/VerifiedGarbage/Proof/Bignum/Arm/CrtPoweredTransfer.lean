module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPoweredState
public import VerifiedGarbage.Proof.Bignum.Arm.TransferArray
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Importing the other residue preserves the completed factor power -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt arrAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem CrtPoweredState.after_transfer {s t : State} {base : BitVec 32} {len w M value : Nat}
    (h : CrtPoweredState base len w M value s.mem) (selected : LayoutFrameReady base len w s)
    (ptr : t.gpr .r0 = base) (keeps : Keeps (State.addr base) len w 1 s.mem t.mem)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest roundClobbers s t) :
    CrtPoweredState base len w M value t.mem := by
  have fit : arrAt w 8 ≤ 8 * len := h.layout.width ▸ h.layout.layout.2.2.1
  obtain ⟨ready, modulus⟩ := (h.ready selected).after_array (by decide : 1 ≠ 0) keeps frame rest ptr
  have op (j : Nat) (hj : j = 4 ∨ j = 6 ∨ j = 7) : Operand j := by
    rcases hj with rfl | rfl | rfl <;> simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  exact CrtPoweredState.of_ready ready (modulus.trans h.modulus)
    ((keeps_array_num keeps fit (op 6 (by simp)) (by decide)).trans h.result)
    ((keeps_array_num keeps fit (op 4 (by simp)) (by decide)).trans h.r2)
    ((keeps_array_num keeps fit (op 7 (by simp)) (by decide)).trans h.one)

end VG.Proof.Bignum.Arm
