module

import VerifiedGarbage.Proof.Bignum.Arm.PublicAccepted
import VerifiedGarbage.Proof.Bignum.Arm.PublicArgs
import VerifiedGarbage.Proof.Bignum.Arm.ExpControls
public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
public import VerifiedGarbage.Proof.Bignum.Arm.PublicArithmetic
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT

/-! # Establish the complete exponentiation precondition from public RSA arguments -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem publicPhaseInput (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicAccepted base dst np ep xp len k eLen nb eb xb s)
    (ptr : s.mem.readW (off (State.addr base) 128) 32 = ep)
    (count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 eLen) :
    ExpPhaseInput base ep len (Spec.Rsa.modulusWords k) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) eb s := by
  have length := h.buffers.exponent.length
  have modulusPos : 0 < Spec.Rsa.os2ip nb := by have := h.ready.modulus; rw [h.modulus] at this; omega
  refine ⟨h.ready, h.modulus, h.odd, h.input, ?_, ?_, ptr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.r2]; exact Nat.mod_lt _ modulusPos
  · rw [h.r2, Nat.mod_mod, ← Nat.pow_add, show 64 * Spec.Rsa.modulusWords k + 64 * Spec.Rsa.modulusWords k =
        128 * Spec.Rsa.modulusWords k by omega]
  · rw [length]; exact count
  · rw [length]; exact h.buffers.exponentPositive
  · rw [length]; have := h.buffers.exponentFits; have := h.buffers.maxLength; omega
  · rw [length]; exact h.buffers.exponent.fits
  · rw [length]; exact h.buffers.exponent.read
  · rw [length]; exact h.buffers.exponentSeparate
  · exact h.buffers.exponent.byte

theorem publicControls_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicAccepted base dst np ep xp len k eLen nb eb xb s) :
    WP isa PublicFn.controls s fun t => PublicAccepted base dst np ep xp len k eLen nb eb xb t ∧
      ExpPhaseInput base ep len (Spec.Rsa.modulusWords k) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) eb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [PublicFn.controls, WP.seq_iff]
  refine WP.mono (publicControlArgs_ok s h.stack) ?_
  rintro u ⟨ptr, count, memU, restU⟩
  have hu := h.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ready.ptr)
  refine WP.mono (expControls_ok u hu.ready) ?_
  rintro t ⟨ready, pointer, counter, arrays, frame, restT⟩
  have ht := hu.after_arrays ready arrays frame restT
  rw [ptr] at pointer
  rw [count] at counter
  have phase := publicPhaseInput t ht pointer counter
  rw [memU] at frame
  exact ⟨ht, phase, frame, (restU.mono (by decide)).trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
