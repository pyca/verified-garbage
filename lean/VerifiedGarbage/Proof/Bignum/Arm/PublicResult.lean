module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicControls
public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhase
import VerifiedGarbage.Proof.Rsa.Octets
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The exponentiation result fits the RSA output buffer and retains acceptance -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure PublicResult (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop where
  buffers : PublicData base dst ep xp len k eLen eb xb s
  stack : PublicStack base dst np ep xp len k eLen s
  ready : ArithmeticReady base len (Spec.Rsa.modulusWords k) s
  value : numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 6 =
    Spec.Rsa.powMod (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip nb)
  valueFit : numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 6 < 2 ^ (8 * k)
  flag : s.mem.readW (off (State.addr s.sp) 48) 32 =
    BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)).toNat

theorem publicExponentiate_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicAccepted base dst np ep xp len k eLen nb eb xb s)
    (phase : ExpPhaseInput base ep len (Spec.Rsa.modulusWords k) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) eb s) :
    WP isa expPhase s fun t => PublicResult base dst np ep xp len k eLen nb eb xb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (expPhase_ok s phase) ?_
  rintro t ⟨ready, value, frame, rest⟩
  have modulusPos : 0 < Spec.Rsa.os2ip nb := by have := h.ready.modulus; rw [h.modulus] at this; omega
  have bound : Spec.Rsa.os2ip nb < 2 ^ (8 * k) := by
    have hb := VG.Proof.Rsa.lt_of_os2ip nb
    rw [h.modulusLength, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at hb
    exact hb
  have valueFit : numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 6 < 2 ^ (8 * k) := by
    rw [value, VG.Proof.Bignum.powMod_eq]
    exact Nat.lt_trans (Nat.mod_lt _ modulusPos) bound
  exact ⟨⟨h.buffers.after_workspace frame rest, h.stack.after_workspace frame rest, ready, value, valueFit,
    (h.stack.keep_acceptance frame rest).trans h.flag⟩, frame, rest⟩

end VG.Proof.Bignum.Arm
