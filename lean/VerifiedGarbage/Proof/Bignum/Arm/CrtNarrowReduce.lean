module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePowerInput
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperand
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperand
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords

/-! # Reduce the input modulo a prepared factor at the modulus width

After the factor's full-width preparation, the input is imported into array
1 and reduced by R² and by one; array 6 is cleared for the narrow result.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt wordAt Operand)
open VG.Proof.X25519.Arm (Rest)

/-- A full-width factor workspace holding the input modulo the factor, and a cleared result. -/
structure CrtReducedState (base : BitVec 32) (len w M x : Nat) (mem : Mem) : Prop where
  layout : CrtLayoutState base len w mem
  inverse : ((word mem (State.addr base) (arrAt w 0)).toNat *
    (wordAt mem (State.addr base) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0
  positive : 1 < M
  odd : M % 2 = 1
  modulus : numAt mem (State.addr base) w 0 = M
  input : numAt mem (State.addr base) w 1 = x % M
  r2 : numAt mem (State.addr base) w 4 = 2 ^ (128 * w) % M
  one : numAt mem (State.addr base) w 7 = 1
  cleared : val32 mem (State.addr base) (arrAt w 6) (2 * w + 2) = 0

theorem CrtReducedState.congr {m m' : Mem} {base : BitVec 32} {len w M x : Nat}
    (h : CrtReducedState base len w M x m) (eq : WorkspaceEq (State.addr base) (8 * len) m m') :
    CrtReducedState base len w M x m' := by
  have fit : arrAt w 8 ≤ 8 * len := h.layout.width ▸ h.layout.layout.2.2.1
  have fit0 := Nat.le_trans (array_end_le (w := w) (by decide : 0 < 8)) fit
  have fit6 := Nat.le_trans (array_end_le (w := w) (by decide : 6 < 8)) fit
  have size := h.layout.size
  refine ⟨h.layout.congr eq, ?_, h.positive, h.odd,
    (eq.number fit (by decide)).trans h.modulus, (eq.number fit (by decide)).trans h.input,
    (eq.number fit (by decide)).trans h.r2, (eq.number fit (by decide)).trans h.one, ?_⟩
  · change ((m'.readW (off (State.addr base) (arrAt w 0)) 64).toNat *
      (m'.readW (off (State.addr base) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [eq.word (d := arrAt w 0) (bits := 64) (by omega), eq.word (d := 56) (bits := 64) (by omega)]
    exact h.inverse
  · rw [← read_eq_val32, eq.read _ _ (by omega), read_eq_val32]
    exact h.cleared

theorem crt_narrowReduce_ok (s : State) {base xp ep : BitVec 32} {len w k eLen slot : Nat} {xb eb : List Byte}
    (h : CrtPrimePowerInput base xp ep len w k eLen slot xb eb s) (countFits : 128 * w < 2 ^ 32) :
    WP isa reducePrime s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (numAt s.mem (State.addr base) w 0)
      ArithmeticReady base len w t ∧ CrtReducedState base len w M (Spec.Rsa.os2ip xb) t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [reducePrime, WP.seq_iff]
  refine WP.mono (crt_primePower_prepare s h countFits) ?_
  rintro u ⟨prepared, frameU, restU⟩
  have fits : arrAt w 8 ≤ 8 * len := prepared.ready.width ▸ prepared.ready.layout.2.2.1
  have src := prepared.sources
  have source : SavedOperand base xp len k 56 12 xb u :=
    ⟨src.stack.nowrap, ⟨src.stack.readable.1, src.stack.readable.2.1⟩, src.stack.separate, by decide, by decide,
      src.stack.input, src.stack.inputCount, src.input, src.inputSeparate⟩
  rw [reduceInput, WP.seq_iff, WP.seq_iff]
  refine WP.mono (savedOperand_ok u prepared.ready source (by decide : 1 < 8) (by decide)
    src.inputPositive src.inputFits) ?_
  rintro v ⟨readyV, inputV, keepsV, frameV, restV⟩
  have modV := (keeps_array_num keepsV fits op0 (by decide)).trans prepared.modulus
  have r2V := (keeps_array_num keepsV fits op4 (by decide)).trans prepared.r2
  rw [WP.seq_iff]
  refine WP.mono (smallConst_ok v 1 readyV (by decide : 7 < 8) (by decide) (by decide) (by decide)) ?_
  rintro z ⟨readyZ, oneZ, _, keepsZ, frameZ, restZ⟩
  have modZ := (keeps_array_num keepsZ fits op0 (by decide)).trans modV
  have r2Z := (keeps_array_num keepsZ fits op4 (by decide)).trans r2V
  have inputZ := (keeps_array_num keepsZ fits op1 (by decide)).trans inputV
  refine WP.mono (reduceOperand_ok z readyZ op1 (by decide) (by decide) modZ prepared.odd r2Z oneZ) ?_
  rintro y ⟨readyY, modY, reducedY, keepsY, frameY, restY⟩
  have r2Y := (keeps_array_num keepsY fits op4 (by decide)).trans r2Z
  have oneY := (keeps_array_num keepsY fits op7 (by decide)).trans oneZ
  rw [inputZ] at reducedY
  refine WP.mono (clearArrayWide_ok y readyY (o := 6) (by decide) (by decide)) ?_
  rintro t ⟨readyT, cleared, keepsT, frameT, restT⟩
  have op6 : (6 : Nat) ≠ 0 := by decide
  have modT := (keeps_array_num keepsT fits op0 (by decide)).trans modY
  refine ⟨readyT, ⟨⟨readyT.layout, readyT.width⟩, readyT.inverse, ?_, prepared.odd, modT,
    (keeps_array_num keepsT fits op1 (by decide)).trans reducedY,
    (keeps_array_num keepsT fits op4 (by decide)).trans r2Y,
    (keeps_array_num keepsT fits op7 (by decide)).trans oneY, cleared⟩,
    frameU.trans (frameV.trans (frameZ.trans (frameY.trans frameT))),
    restU.trans (restV.trans (restZ.trans (restY.trans restT)))⟩
  have := readyT.modulus
  rw [modT] at this
  exact this

end VG.Proof.Bignum.Arm
