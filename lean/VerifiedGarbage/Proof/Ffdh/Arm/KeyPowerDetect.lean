module

public import VerifiedGarbage.Impl.Ffdh.Arm.KeyPowerDetect
public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
import VerifiedGarbage.Proof.Ffdh.Arm.Equal
import VerifiedGarbage.Proof.Ffdh.Arm.Checks
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! Public-base detection preserves the prepared arithmetic and exponent controls. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest wp_str)

abbrev DetectControls (base : BitVec 32) (s t : State) : Prop :=
  ∀ d, d + 4 ≤ 256 → d + 4 ≤ 136 ∨ 140 ≤ d →
    t.mem.readW (off (State.addr base) d) 32 = s.mem.readW (off (State.addr base) d) 32

theorem detectSave_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa (.block VG.Impl.Ffdh.Arm.saveFlag) s fun t => ArithmeticReady base len w t ∧
      t.mem.readW (off (State.addr base) 136) 32 = s.gpr .r11 ∧
      (∀ q < 8, numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      DetectControls base s t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest [] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  unfold VG.Impl.Ffdh.Arm.saveFlag
  refine wp_str (a := off (State.addr base) 136) (by decide)
    (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega))
    (h.workspace.write (by omega)) fun t a => WP.block_nil ?_
  have rest : Rest [] s t := a.rest []
  obtain ⟨ready, frame, arrays⟩ := h.after_header (d := 136) (by decide) (by decide) a.mem rest
    ((rest.gpr .r0 (by simp)).trans h.ptr)
  refine ⟨ready, by rw [a.mem, Mem.readW_writeW_self32], arrays, ?_, frame, rest⟩
  intro d hd sep
  have outside := writeW32_outside s.mem (State.addr base) (d := 136) (s.gpr .r11) (by decide)
  rw [a.mem]
  exact outside_read32 outside sep (by omega)

theorem equal_controls_ok (s : State) {base : BitVec 32} {len w a b : Nat}
    (h : ArithmeticReady base len w s) (ha : Operand a) (hb : Operand b) :
    WP isa (VG.Impl.Ffdh.Arm.equal a b) s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = (if numAt s.mem (State.addr base) w a = numAt s.mem (State.addr base) w b then 1 else 0) ∧
      (∀ q, Operand q → numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      DetectControls base s t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  rw [VG.Impl.Ffdh.Arm.equal, WP.seq_iff]
  refine WP.mono (compare_ok s h ha.1 hb.1 ha.2.2 hb.2.2) ?_
  rintro u ⟨readyU, less, keepsU, frameU, restU⟩
  have arraysU (q : Nat) (hq : Operand q) := keeps_array_num keepsU fits hq hq.2.2
  rw [WP.seq_iff]
  refine WP.mono (detectSave_ok u readyU) ?_
  rintro v ⟨readyV, saved, arraysV, controlsV, frameV, restV⟩
  have arraysUV (q : Nat) (hq : Operand q) := (arraysV q hq.1).trans (arraysU q hq)
  rw [WP.seq_iff]
  refine WP.mono (compare_ok v readyV hb.1 ha.1 hb.2.2 ha.2.2) ?_
  rintro z ⟨readyZ, greater, keepsZ, frameZ, restZ⟩
  have arraysZ (q : Nat) (hq : Operand q) := keeps_array_num keepsZ fits hq hq.2.2
  have savedZ := (keeps_header_readW keepsZ size (d := 136) (bits := 32) (by decide)).trans saved
  rw [arraysUV b hb, arraysUV a ha] at greater
  refine WP.mono (equalFinish_ok z readyZ) ?_
  rintro t ⟨⟨result, memT⟩, restT⟩
  have rest : Rest roundClobbers s t := restU.trans
    ((restV.mono (by simp [roundClobbers])).trans (restZ.trans (restT.mono (by simp [roundClobbers]))))
  have ptr := (restT.gpr .r0 (by simp)).trans readyZ.ptr
  refine ⟨readyZ.of_mem memT restT ptr, ?_, ?_, ?_, ?_, rest⟩
  · rw [result, greater, savedZ, less, equalFlags]; simp only [eq_comm]
  · intro q hq; rw [memT, arraysZ q hq, arraysUV q hq]
  · intro d hd sep
    rw [memT, keeps_header_readW keepsZ size (d := d) (bits := 32) hd,
      controlsV d hd sep, keeps_header_readW keepsU size (d := d) (bits := 32) hd]
  · rw [memT]; exact frameU.trans (frameV.trans frameZ)

theorem detectTwo_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa VG.Impl.Ffdh.Arm.detectTwo s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = (if numAt s.mem (State.addr base) w 1 = 2 then 1 else 0) ∧
      (∀ q, Operand q → q ≠ 5 → numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      DetectControls base s t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  rw [VG.Impl.Ffdh.Arm.detectTwo, WP.seq_iff]
  refine WP.mono (smallConst_ok s 2 h (o := 5) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, two, _, keepsU, frameU, restU⟩
  have oa : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have ob : Operand 5 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (equal_controls_ok u readyU oa ob) ?_
  rintro t ⟨ready, result, arrays, controls, frame, rest⟩
  rw [two, keeps_array_num keepsU fits oa (by decide)] at result
  change t.gpr .r11 = (if numAt s.mem (State.addr base) w 1 = 2 then 1 else 0) at result
  refine ⟨ready, result, ?_, ?_, frameU.trans frame, restU.trans rest⟩
  · intro q hq nq; rw [arrays q hq, keeps_array_num keepsU fits hq nq]
  · intro d hd sep
    rw [controls d hd sep, keeps_header_readW keepsU size (d := d) (bits := 32) hd]

theorem detectTwo_phase_ok (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (h : ExpPhaseInput base ep len w M x eb s) :
    WP isa VG.Impl.Ffdh.Arm.detectTwo s fun t => ExpPhaseInput base ep len w M x eb t ∧
      t.gpr .r11 = (if x = 2 then 1 else 0) ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  refine WP.mono (detectTwo_ok s h.ready) ?_
  rintro t ⟨ready, result, arrays, controls, frame, rest⟩
  have op (i : Nat) (hi : i = 0 ∨ i = 1 ∨ i = 4) : Operand i := by
    rcases hi with rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [h.input] at result
  refine ⟨⟨ready, (arrays 0 (op 0 (by simp)) (by decide)).trans h.modulus, h.odd,
    (arrays 1 (op 1 (by simp)) (by decide)).trans h.input,
    by rw [arrays 4 (op 4 (by simp)) (by decide)]; exact h.r2bound,
    by rw [arrays 4 (op 4 (by simp)) (by decide)]; exact h.r2value,
    (controls 128 (by decide) (by left; decide)).trans h.pointer,
    (controls 132 (by decide) (by left; decide)).trans h.count,
    h.positive, h.countFit, h.sourceFit, by rw [rest.rd, rest.wr]; exact h.read,
    h.separate, ?_⟩, result, frame, rest⟩
  intro i hi
  rw [frame.bytes (R := ⟨State.addr ep, eb.length⟩)
    (by simpa using h.separate) (by change eb.length ≤ 2 ^ 64; have := h.countFit; omega) hi]
  exact h.bytes i hi

end VG.Proof.Ffdh.Arm
