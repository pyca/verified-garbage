module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.Checks
import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Array equality has no secret-dependent branch. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem equalFlags (a b : Nat) :
    (((if a < b then 1 else 0) : BitVec 32) ||| (if b < a then 1 else 0)) ^^^ 1 =
      (if a = b then 1 else 0) := by
  split_ifs <;> first | decide | omega

theorem equalFinish_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa (.block [.ldr .r3 .r0 136, .dp .orr .r11 .r11 (.reg .r3), .dp .eor .r11 .r11 (.imm 1)]) s fun t =>
      (t.gpr .r11 = (s.gpr .r11 ||| s.mem.readW (off (State.addr base) 136) 32) ^^^ 1 ∧
      t.mem = s.mem) ∧ Rest [.r3, .r11] s t := by
  have size : 256 ≤ 8 * len := by
    have := h.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  have addr : State.addr (base + BitVec.ofNat 32 136) = off (State.addr base) 136 :=
    VG.Arm.addr_add (by have := h.workspace.nowrap; omega)
  have read := h.workspace.read (off := 136) (by omega)
  refine withRest_all [.r3, .r11] ?_ (by rfl) (by rfl)
  ffrun [h.ptr, addr, read, off]

theorem equal_ok (s : State) {base : BitVec 32} {len w a b : Nat}
    (h : ArithmeticReady base len w s) (ha : Operand a) (hb : Operand b) :
    WP isa (VG.Impl.Ffdh.Arm.equal a b) s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = (if numAt s.mem (State.addr base) w a = numAt s.mem (State.addr base) w b then 1 else 0) ∧
      (∀ q, Operand q → numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  rw [VG.Impl.Ffdh.Arm.equal, WP.seq_iff]
  refine WP.mono (compare_ok s h ha.1 hb.1 ha.2.2 hb.2.2) ?_
  rintro u ⟨readyU, less, keepsU, frameU, restU⟩
  have arraysU (q : Nat) (hq : Operand q) := keeps_array_num keepsU fits hq hq.2.2
  rw [WP.seq_iff]
  refine WP.mono (saveFlag_ok u readyU) ?_
  rintro v ⟨readyV, saved, arraysV, frameV, restV⟩
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
  refine ⟨readyZ.of_mem memT restT ptr, ?_, ?_, ?_, rest⟩
  · rw [result, greater, savedZ, less, equalFlags]
    simp only [eq_comm]
  · intro q hq
    rw [memT, arraysZ q hq, arraysUV q hq]
  · rw [memT]; exact frameU.trans (frameV.trans frameZ)

end VG.Proof.Ffdh.Arm
