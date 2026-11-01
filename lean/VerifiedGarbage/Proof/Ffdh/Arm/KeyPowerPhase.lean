module

public import VerifiedGarbage.Impl.Ffdh.Arm.KeyPower
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpPhase
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerDetect
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block

/-! # Public generator dispatch with a full-width secret exponent

The fallback is supplied with its verified arithmetic and timing behavior.
Both paths use the original imported exponent bytes without shortening.
-/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

structure PhaseInput (base ep : BitVec 32) (len w M x : Nat) (P : State → Prop)
    (regions : List Region) (eb : List Byte) (s : State) : Prop where
  phase : ExpPhaseInput base ep len w M x eb s
  persistent : P s
  separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r

abbrev PhaseResult (base : BitVec 32) (len w M x : Nat) (P : State → Prop)
    (regions : List Region) (eb : List Byte) (s t : State) : Prop :=
  ArithmeticReady base len w t ∧
    numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x (Spec.Rsa.os2ip eb) M ∧
    numAt t.mem (State.addr base) w 0 = M ∧
    numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
    numAt t.mem (State.addr base) w 7 = 1 ∧ P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t

structure Fallback (base : BitVec 32) (len w : Nat) (P : State → Prop) (regions : List Region) where
  code : Prog isa
  correct : ∀ (s : State) {ep : BitVec 32} {M x : Nat} {eb : List Byte},
    PhaseInput base ep len w M x P regions eb s →
    WP isa code s (PhaseResult base len w M x P regions eb s)
  ct : ∀ {ep : BitVec 32} {M1 M2 x : Nat} {eb1 eb2 : List Byte},
    0 < eb1.length → eb1.length = eb2.length →
    RelCT isa (fun s t => PhaseInput base ep len w M1 x P regions eb1 s ∧
      PhaseInput base ep len w M2 x P regions eb2 t ∧ s.sp = t.sp) code (fun _ _ => True)

theorem PhaseInput.of_mem {base ep : BitVec 32} {len w M x : Nat} {P : State → Prop}
    {regions : List Region} {eb : List Byte} {s t : State} {rs : List Reg}
    (A : TwoExp.Montgomery base len w P regions) (h : PhaseInput base ep len w M x P regions eb s)
    (mem : t.mem = s.mem) (rest : Rest rs s t) (small : ∀ r ∈ rs, r ∈ roundClobbers)
    (ptr : t.gpr .r0 = base) : PhaseInput base ep len w M x P regions eb t := by
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  refine ⟨⟨h.phase.ready.of_mem mem rest ptr, ?_, h.phase.odd, ?_, ?_, ?_, ?_, ?_, h.phase.positive,
    h.phase.countFit, h.phase.sourceFit, ?_, h.phase.separate, ?_⟩,
    A.stable frame (rest.mono small) h.persistent, h.separate⟩
  · rw [mem]; exact h.phase.modulus
  · rw [mem]; exact h.phase.input
  · rw [mem]; exact h.phase.r2bound
  · rw [mem]; exact h.phase.r2value
  · rw [mem]; exact h.phase.pointer
  · rw [mem]; exact h.phase.count
  · rw [rest.rd, rest.wr]; exact h.phase.read
  · intro i hi; rw [mem]; exact h.phase.bytes i hi

structure Detected (base ep : BitVec 32) (len w M x : Nat) (P : State → Prop)
    (regions : List Region) (eb : List Byte) (s : State) : Prop where
  input : PhaseInput base ep len w M x P regions eb s
  flag : s.gpr .r11 = if x = 2 then 1 else 0

theorem detected_ok {base ep : BitVec 32} {len w M x : Nat} {P : State → Prop}
    {regions : List Region} {eb : List Byte}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : PhaseInput base ep len w M x P regions eb s) :
    WP isa VG.Impl.Ffdh.Arm.detectTwo s fun t => Detected base ep len w M x P regions eb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (detectTwo_phase_ok s h.phase) ?_
  rintro t ⟨ready, flag, frame, rest⟩
  exact ⟨⟨⟨ready, A.stable frame rest h.persistent, h.separate⟩, flag⟩, frame, rest⟩

theorem phase_ok {base ep : BitVec 32} {len w M x : Nat} {P : State → Prop}
    {regions : List Region} {eb : List Byte}
    (A : TwoExp.Montgomery base len w P regions) (fallback : Fallback base len w P regions)
    (s : State) (h : PhaseInput base ep len w M x P regions eb s) :
    WP isa (VG.Impl.Ffdh.Arm.KeyPower.phase A.phase fallback.code) s (PhaseResult base len w M x P regions eb s) := by
  rw [VG.Impl.Ffdh.Arm.KeyPower.phase, WP.seq_iff]
  refine WP.mono (detected_ok A s h) ?_
  rintro u ⟨detected, frameU, restU⟩
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok u) ?_
  rintro v ⟨⟨zero, mem⟩, rest⟩
  have input := detected.input.of_mem A mem rest (by simp) ((rest.gpr .r0 (by simp)).trans detected.input.phase.ready.ptr)
  have frameV : Frame regions s.mem v.mem := by
    rw [mem]; exact frameU.mono (by simpa using A.workspace)
  have restV : Rest roundClobbers s v := restU.trans (rest.mono (by simp))
  have finish {code : Prog isa} (run : WP isa code v (PhaseResult base len w M x P regions eb v)) :
      WP isa code v (PhaseResult base len w M x P regions eb s) := by
    refine WP.mono run ?_
    rintro t ⟨ready, value, modulus, r2, one, p, frameT, restT⟩
    exact ⟨ready, value, modulus, r2, one, p, frameV.trans frameT, restV.trans restT⟩
  by_cases two : x = 2
  · refine WP.ite true (by change some (!v.z) = some true; rw [zero, detected.flag, ite_eq_left two]; rfl) ?_ (by simp)
    intro _
    subst x
    exact finish (TwoExp.phase_ok A v ⟨input.phase, input.persistent, input.separate⟩)
  · refine WP.ite false (by change some (!v.z) = some false; rw [zero, detected.flag, ite_eq_right two]; rfl) (by simp) ?_
    intro _
    exact finish (fallback.correct v input)

end VG.Proof.Ffdh.Arm.KeyPower
