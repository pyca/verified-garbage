module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicArithmetic
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
import VerifiedGarbage.Proof.Bignum.Arm.PublicArgs
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Block

/-! # Import the secret RSA input while retaining precomputed public-key arithmetic -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem publicImport_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicArithmetic base dst np ep xp len k eLen nb eb xb s) :
    WP isa PublicFn.importInput s fun t => PublicOperand base dst np ep xp len k eLen nb eb xb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [PublicFn.importInput, WP.seq_iff]
  refine WP.mono (publicInputArgs_ok s h.stack) ?_
  rintro u ⟨source, count, memU, restU⟩
  have hu := h.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ready.ptr)
  have dims := pc_dimensions hu.buffers.minLength hu.buffers.maxLength hu.buffers.space
  refine WP.mono (importOperand_ok u hu.ready (by decide : 1 < 8) (by decide)
    (by have := hu.buffers.minLength; omega) dims.2.2.2.1 hu.buffers.input.fits
    hu.buffers.input.read hu.buffers.inputSeparate source count) ?_
  rintro t ⟨ready, value, keeps, frameT, restT⟩
  rw [hu.buffers.input.bytes] at value
  have ht := hu.after_array ready keeps frameT restT (by decide) (by decide)
  rw [memU] at frameT
  exact ⟨⟨ht, value⟩, frameT, (restU.mono (by decide)).trans restT⟩

end VG.Proof.Bignum.Arm
