module

public import VerifiedGarbage.Proof.Bignum.Arm.PdCheckState
public import VerifiedGarbage.Impl.Bignum.Arm.ArrayCompare
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompare
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Framework.Block

/-! # Check that the public packed modulus exceeds one -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem pdCheckFirst_ok (s : State) {base : BitVec 32} {len w N R : Nat}
    (h : PdCheckState base len w N R s) :
    WP isa (.seq (smallConst 7 1) (arrayCompare 7 0)) s fun t =>
      PdCheckState base len w N R t ∧ t.gpr .r11 = BitVec.ofNat 32 (decide (1 < N)).toNat ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (smallConstLayout_ok s 1 h.ready.workspace h.ready.layout h.ready.width h.ready.ptr
    (by decide : 7 < 8) (by decide) (by decide) h.ready.stackRead h.ready.stackSep h.ready.saved) ?_
  rintro u ⟨_, _, one, outside, frameU, restU, ptr⟩
  have keeps := outside_array_keeps outside (len := len) (by have := h.ready.workspace.nowrap; omega)
  have readyU := h.ready.after_array keeps frameU restU ptr
  have hu := h.after_array readyU restU keeps (by decide) (by decide)
  refine WP.mono (arrayCompare_ok u hu.ready (by decide : 7 < 8) (by decide : 0 < 8)
    (by decide) (by decide)) ?_
  rintro t ⟨readyT, flag, keepsT, frameT, restT⟩
  rw [one, hu.modulus] at flag
  refine ⟨hu.after_array readyT restT keepsT (by decide) (by decide), ?_, frameU.trans frameT, restU.trans restT⟩
  by_cases valid : 1 < N <;> simpa [valid] using flag

end VG.Proof.Bignum.Arm
