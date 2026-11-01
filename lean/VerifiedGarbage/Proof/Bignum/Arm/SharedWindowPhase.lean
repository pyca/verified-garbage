module

public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowBuild
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowApply
public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
public import VerifiedGarbage.Proof.Bignum.Arm.WindowPhase
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowBytes
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowArithmetic

/-! # Three-bit exponentiation through shared arithmetic calls

The exponent source is separate from every permitted working region,
including the callee's saved-register stack, throughout the fixed schedule.
-/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

section
variable {base ep : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
variable (K : TwoExp.Montgomery base len w P regions)

theorem sharedPhaseInit_ready (s : State) {M x : Nat} {eb : List Byte}
    (h : ExpPhaseInput base ep len w M x eb s) (hp : P s)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    WP isa (SharedWindow.init K.op) s fun t =>
      ExpByteState base ep len w M x eb 0 t ∧ P t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (sharedWindowInit_ok K s h.ready hp h.modulus h.odd h.input h.r2bound h.r2value) ?_
  rintro t ⟨power, header, pt, frame, rest⟩
  refine ⟨⟨power, ?_, ?_, h.countFit, h.sourceFit, ?_, h.separate, ?_⟩, pt, frame, rest⟩
  · rw [header 128 (by decide), BitVec.add_zero]; exact h.pointer
  · rw [header 132 (by decide)]; exact h.count
  · rw [rest.rd, rest.wr]; exact h.read
  · intro i hi
    rw [frame.bytes (R := ⟨State.addr ep, eb.length⟩) separate
      (by change eb.length ≤ 2 ^ 64; have := h.countFit; omega) hi]
    exact h.bytes i hi

theorem sharedPhaseTable_ok (s : State) {M x : Nat} {eb : List Byte}
    (ready : ExpByteState base ep len w M x eb 0 s) (hp : P s)
    (fits : arrAt w 16 ≤ 8 * len)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    WP isa (SharedWindow.tableBuild K.op) s fun t =>
      WinReady base ep len w M x eb t ∧ P t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (sharedTableBuild_ok K s ready.power hp fits) ?_
  rintro t ⟨power, table, keeps, pt, frame, rest⟩
  refine ⟨⟨power, table, fits, ?_, ?_, ready.countFit, ready.sourceFit,
    by rw [rest.rd, rest.wr]; exact ready.read, ready.separate, ?_⟩, pt, frame, rest⟩
  · rw [keeps 128 (by simp), ready.pointer, BitVec.add_zero]
  · rw [keeps 132 (by simp), ready.count, Nat.sub_zero]
  · intro i hi
    rw [frame.bytes (R := ⟨State.addr ep, eb.length⟩) separate
      (by change eb.length ≤ 2 ^ 64; have := ready.countFit; omega) hi]
    exact ready.bytes i hi

theorem sharedWindowExpPhase_ok (s : State) {M x : Nat} {eb : List Byte}
    (h : ExpPhaseInput base ep len w M x eb s) (hp : P s) (fits : arrAt w 16 ≤ 8 * len)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    WP isa (SharedWindow.phase K.op) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [SharedWindow.phase, WP.seq_iff]
  refine WP.mono (sharedPhaseInit_ready K s h hp separate) ?_
  rintro u ⟨ready, pu, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (sharedPhaseTable_ok K u ready pu fits separate) ?_
  rintro v ⟨readyV, pv, frameV, restV⟩
  rw [WP.seq_iff]
  refine WP.mono (phaseReset_ok v readyV) ?_
  rintro z ⟨loopZ, frameZ, restZ⟩
  have pz := K.stable frameZ restZ pv
  rw [WP.seq_iff]
  refine WP.mono (sharedWindowBytes_ok K z loopZ pz h.positive separate) ?_
  rintro y ⟨⟨A, p, stateY, sum⟩, py, frameY, restY⟩
  rw [WP.seq_iff]
  refine WP.mono (sharedWindowApply_ok K y stateY.power py stateY.table fits
    (pending_digit stateY) stateY.digit) ?_
  rintro r ⟨powerR, _, _, _, _, pr, frameR, restR⟩
  rw [sum] at powerR
  refine WP.mono (sharedExpFinish_ok K r powerR pr) ?_
  rintro t ⟨final, value, keeps, pt, frameT, restT⟩
  have fits8 : arrAt w 8 ≤ 8 * len := powerR.ready.width ▸ powerR.ready.layout.2.2.1
  have modulus := (keeps_array_num keeps fits8 (q := 0)
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerR.modulus
  have r2 := (keeps_array_num keeps fits8 (q := 4)
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerR.r2
  have one := (keeps_array_num keeps fits8 (q := 7)
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerR.one
  exact ⟨final, value, modulus, r2, one, pt,
    frameU.trans (frameV.trans ((frameZ.mono (by simpa using K.workspace)).trans
      (frameY.trans (frameR.trans frameT)))),
    restU.trans (restV.trans (restZ.trans (restY.trans (restR.trans restT))))⟩

end
end VG.Proof.Bignum.Arm
