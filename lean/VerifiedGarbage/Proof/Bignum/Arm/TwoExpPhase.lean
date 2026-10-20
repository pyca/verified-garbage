module

public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpInit
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpFinish
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpByteState
public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpBytes
import VerifiedGarbage.Proof.Framework.Block

/-! # Complete generator-two exponentiation from the existing RSA inputs -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure Input (base ep : BitVec 32) (len w M : Nat) (P : State → Prop)
    (regions : List Region) (eb : List Byte) (s : State) : Prop where
  phase : ExpPhaseInput base ep len w M 2 eb s
  persistent : P s
  separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r

def Montgomery.phase {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (A : Montgomery base len w P regions) : Prog isa :=
  VG.Impl.Bignum.Arm.TwoExp.phase A.init A.kernel.square A.kernel.twice (A.op 6 6 7)

theorem init_bytes_ready {base ep : BitVec 32} {len w M : Nat} {P : State → Prop}
    {regions : List Region} {eb : List Byte}
    (A : Montgomery base len w P regions) (s : State) (h : Input base ep len w M P regions eb s) :
    WP isa A.init s fun t => ByteState base ep len w M P regions eb 0 t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M := by
    have value := h.phase.r2value
    rw [Nat.mod_eq_of_lt h.phase.r2bound, ← Nat.pow_add,
      show 64 * w + 64 * w = 128 * w by omega] at value
    exact value
  refine WP.mono (init_ok A s h.phase.ready h.persistent h.phase.modulus h.phase.odd r2) ?_
  rintro t ⟨power, persistent, header, frame, rest⟩
  refine ⟨⟨by simpa only [pre_zero] using power, persistent, ?_, ?_, h.phase.countFit,
    h.phase.sourceFit, ?_, h.separate, ?_⟩, frame, rest⟩
  · rw [header 128 (by decide), BitVec.add_zero]; exact h.phase.pointer
  · rw [header 132 (by decide), Nat.sub_zero]; exact h.phase.count
  · rw [rest.rd, rest.wr]; exact h.phase.read
  · intro i hi
    rw [frame.bytes h.separate (by change eb.length ≤ 2 ^ 64; have := h.phase.countFit; omega) hi]
    exact h.phase.bytes i hi

theorem phase_ok {base ep : BitVec 32} {len w M : Nat} {P : State → Prop} {regions : List Region}
    {eb : List Byte} (A : Montgomery base len w P regions) (s : State)
    (h : Input base ep len w M P regions eb s) :
    WP isa A.phase s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod 2 (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧ P t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [Montgomery.phase, VG.Impl.Bignum.Arm.TwoExp.phase, WP.seq_iff]
  refine WP.mono (init_bytes_ready A s h) ?_
  rintro u ⟨ready, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (bytes_ok A.kernel u (by simpa only [pre_zero] using ready.power) ready.persistent
    h.phase.positive ready.countFit ready.sourceFit ready.read ready.separate ready.bytes
    (by simpa only [BitVec.add_zero] using ready.pointer) (by simpa only [Nat.sub_zero] using ready.count)) ?_
  rintro v ⟨power, persistent, frameV, restV⟩
  refine WP.mono (finish_ok A v power persistent) ?_
  rintro t ⟨final, result, modulus, r2, one, pt, _, frameT, restT⟩
  exact ⟨final, result, modulus, r2, one, pt, frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm.TwoExp
