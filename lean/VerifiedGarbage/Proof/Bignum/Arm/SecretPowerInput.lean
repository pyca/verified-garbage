module

public import VerifiedGarbage.Impl.Bignum.Arm.SecretPower
public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.ExpControls
public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Secret operands and public geometry for a prepared modular power -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure SecretPowerInput (base xp ep : BitVec 32) (len w k eLen M : Nat)
    (xb eb : List Byte) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  modulus : numAt s.mem (State.addr base) w 0 = M
  odd : M % 2 = 1
  r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M
  input : PublicBytes xp k xb s
  exponent : PublicBytes ep eLen eb s
  inputSeparate : Region.Disjoint ⟨State.addr xp, k⟩ ⟨State.addr base, 8 * len⟩
  exponentSeparate : Region.Disjoint ⟨State.addr ep, eLen⟩ ⟨State.addr base, 8 * len⟩
  inputPositive : 0 < k
  inputFits : k ≤ 8 * w
  exponentPositive : 0 < eLen
  exponentFits : eLen < 2 ^ 32
  source : s.gpr .r4 = xp
  count : s.gpr .r6 = BitVec.ofNat 32 k
  exponentPointer : s.gpr .r1 = ep
  exponentCount : s.gpr .r2 = BitVec.ofNat 32 eLen

theorem secretPower_controls_ready (s : State) {base xp ep : BitVec 32} {len w k eLen M : Nat} {xb eb : List Byte}
    (h : SecretPowerInput base xp ep len w k eLen M xb eb s) :
    WP isa (.block expControls) s fun t => SecretPowerInput base xp ep len w k eLen M xb eb t ∧
      t.mem.readW (off (State.addr base) 128) 32 = ep ∧
      t.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 eLen ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest [] s t := by
  refine WP.mono (expControls_ok s h.ready) ?_
  rintro t ⟨ready, pointer, count, arrays, frame, rest⟩
  have input := h.input.after_frame frame rest
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.inputSeparate)
  have exponent := h.exponent.after_frame frame rest
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.exponentSeparate)
  exact ⟨⟨ready, (arrays 0 (by decide)).trans h.modulus, h.odd, (arrays 4 (by decide)).trans h.r2,
    input, exponent, h.inputSeparate, h.exponentSeparate, h.inputPositive, h.inputFits, h.exponentPositive, h.exponentFits,
    (rest.gpr .r4 (by simp)).trans h.source, (rest.gpr .r6 (by simp)).trans h.count,
    (rest.gpr .r1 (by simp)).trans h.exponentPointer, (rest.gpr .r2 (by simp)).trans h.exponentCount⟩,
    pointer.trans h.exponentPointer, count.trans h.exponentCount, frame, rest⟩

end VG.Proof.Bignum.Arm
