module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePowerInput

import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrimeCT
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWideCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperand
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperand
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Layout

/-! # Reducing the input modulo a factor hides the factor, the input and acceptance -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt Operand)

/-- A prepared full-width factor workspace, with its constants, for some factor. -/
def CrtReduceReady (base : BitVec 32) (len w : Nat) (one : Bool) (s : State) : Prop :=
  ∃ M, ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M ∧ M % 2 = 1 ∧
    numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧ (one → numAt s.mem (State.addr base) w 7 = 1)

theorem crt_narrowReduce_ct {base xp ep : BitVec 32} {len w k eLen slot : Nat} {xb1 xb2 eb1 eb2 : List Byte}
    (countFits : 128 * w < 2 ^ 32) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => CrtPrimePowerInput base xp ep len w k eLen slot xb1 eb1 s ∧
      CrtPrimePowerInput base xp ep len w k eLen slot xb2 eb2 t ∧ s.sp = t.sp) reducePrime (fun _ _ => True) := by
  have op0 : Operand 0 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have size : 128 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fit; omega
  let Prepared := fun (xb eb : List Byte) (s : State) =>
    ∃ M, CrtPreparedPower base xp ep len w k eLen slot M xb eb s
  have prepare : RelCT isa (fun s t => CrtPrimePowerInput base xp ep len w k eLen slot xb1 eb1 s ∧
      CrtPrimePowerInput base xp ep len w k eLen slot xb2 eb2 t ∧ s.sp = t.sp)
      prepareAcceptedPrime (fun _ _ => True) :=
    (prepareAcceptedPrime_ct countFits).mono
      (fun _ _ h => ⟨h.1.accepted, h.2.1.accepted, h.2.2⟩) (fun _ _ _ => trivial)
  have prepareWP (s : State) {xb eb : List Byte}
      (h : CrtPrimePowerInput base xp ep len w k eLen slot xb eb s) : WP isa prepareAcceptedPrime s (Prepared xb eb) :=
    (crt_primePower_prepare s h countFits).mono (fun _ j => ⟨_, j.1⟩)
  -- The input.
  have source (s : State) {xb eb : List Byte} {M : Nat} (h : CrtPreparedPower base xp ep len w k eLen slot M xb eb s) :
      SavedOperand base xp len k 56 12 xb s :=
    ⟨h.sources.stack.nowrap, ⟨h.sources.stack.readable.1, h.sources.stack.readable.2.1⟩, h.sources.stack.separate,
      by decide, by decide, h.sources.stack.input, h.sources.stack.inputCount, h.sources.input, h.sources.inputSeparate⟩
  have load : RelCT isa (fun s t => Prepared xb1 eb1 s ∧ Prepared xb2 eb2 t ∧ s.sp = t.sp)
      (savedOperand 1 56 12) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨⟨M1, h1⟩, ⟨M2, h2⟩, sp⟩ := h
    exact (savedOperand_ct (by decide : 1 < 8)) s t tr1 tr2 u v
      ⟨⟨h1.ready, source s h1⟩, ⟨h2.ready, source t h2⟩, sp⟩ e1 e2
  have loadWP (s : State) {xb eb : List Byte} (h : Prepared xb eb s) :
      WP isa (savedOperand 1 56 12) s (CrtReduceReady base len w false) := by
    obtain ⟨M, h⟩ := h
    refine WP.mono (savedOperand_ok s h.ready (source s h) (by decide : 1 < 8) (by decide)
      h.sources.inputPositive h.sources.inputFits) ?_
    rintro t ⟨ready, _, keeps, _, _⟩
    have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
    exact ⟨M, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus, h.odd,
      (keeps_array_num keeps fits op4 (by decide)).trans h.r2, by simp⟩
  -- The constant one.
  have one : RelCT isa (fun s t => CrtReduceReady base len w false s ∧ CrtReduceReady base len w false t ∧ s.sp = t.sp)
      (smallConst 7 1) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨⟨_, h1, _⟩, ⟨_, h2, _⟩, sp⟩ := h
    exact (smallConst_ct (base := base) (len := len) (w := w) (o := 7) 1 (by decide) (by decide) (by decide))
      s t tr1 tr2 u v ⟨h1, h2, sp⟩ e1 e2
  have oneWP (s : State) (h : CrtReduceReady base len w false s) :
      WP isa (smallConst 7 1) s (CrtReduceReady base len w true) := by
    obtain ⟨M, ready, modulus, odd, r2, _⟩ := h
    refine WP.mono (smallConst_ok s (o := 7) 1 ready (by decide) (by decide) (by decide) (by decide)) ?_
    rintro t ⟨readyT, oneT, _, keeps, _, _⟩
    have fits : arrAt w 8 ≤ 8 * len := ready.width ▸ ready.layout.2.2.1
    exact ⟨M, readyT, (keeps_array_num keeps fits op0 (by decide)).trans modulus, odd,
      (keeps_array_num keeps fits op4 (by decide)).trans r2, fun _ => oneT⟩
  -- The reduction.
  have reduceReady (s : State) (h : CrtReduceReady base len w true s) : ReduceOperandReady base len w s := by
    obtain ⟨M, ready, modulus, _, r2, one⟩ := h
    have positive := ready.modulus
    refine ⟨ready, ?_, ?_⟩
    · rw [r2, modulus]; rw [modulus] at positive; exact Nat.mod_lt _ (by omega)
    · rw [one rfl]; exact positive
  have reduce : RelCT isa (fun s t => CrtReduceReady base len w true s ∧ CrtReduceReady base len w true t ∧ s.sp = t.sp)
      (reduceOperand 1) (fun _ _ => True) :=
    (reduceOperand_ct op1 (by decide) (by decide) fit).mono
      (fun s t h => ⟨reduceReady s h.1, reduceReady t h.2.1, h.2.2⟩) (fun _ _ _ => trivial)
  have reduceWP (s : State) (h : CrtReduceReady base len w true s) :
      WP isa (reduceOperand 1) s (ArithmeticReady base len w) := by
    obtain ⟨M, ready, modulus, odd, r2, one⟩ := h
    exact (reduceOperand_ok s ready op1 (by decide) (by decide) modulus odd r2 (one rfl)).mono (fun _ j => j.1)
  have clear : RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (clearOperandBuffer (64 + 8 * 6)) (fun _ _ => True) :=
    clearArrayWide_ct (by decide) size
  have midWP (s : State) {xb eb : List Byte} (h : Prepared xb eb s) :
      WP isa (.seq (savedOperand 1 56 12) (.seq (smallConst 7 1) (reduceOperand 1))) s (ArithmeticReady base len w) :=
    WP.seq_iff.mpr ((loadWP s h).mono fun _ hu => WP.seq_iff.mpr ((oneWP _ hu).mono fun _ hz => reduceWP _ hz))
  rw [reducePrime, reduceInput]
  exact crt_seq_ct prepare (fun s h => prepareWP s h) (fun s h => prepareWP s h)
    (crt_seq_ct (crt_seq_ct load (fun s h => loadWP s h) (fun s h => loadWP s h) (crt_seq_ct one oneWP oneWP reduce))
      (fun s h => midWP s h) (fun s h => midWP s h) clear)

end VG.Proof.Bignum.Arm
