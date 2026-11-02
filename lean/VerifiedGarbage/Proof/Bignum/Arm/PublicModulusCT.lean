module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrepare
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.PublicFailCT
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.PublicArithmetic
import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
import VerifiedGarbage.Proof.Bignum.Arm.PublicArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.PublicArgs
import VerifiedGarbage.Proof.Bignum.Arm.InputCompareCT
import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
import VerifiedGarbage.Proof.Bignum.Arm.PublicAccepted
import VerifiedGarbage.Proof.Bignum.Arm.ExportMaskedCT
import VerifiedGarbage.Proof.Bignum.Arm.PublicResult
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteState
import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
import VerifiedGarbage.Proof.Bignum.Arm.ExpInitCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpStepCT
import VerifiedGarbage.Proof.Bignum.Arm.PublicControls
import VerifiedGarbage.Proof.Bignum.Arm.PublicAccept
import VerifiedGarbage.Proof.Bignum.Arm.PublicImport
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT
import VerifiedGarbage.Proof.Bignum.Arm.PublicPrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
/-! # Modulus validation branches only on the public modulus -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicImportCT.lean`, which only this module imported.
section

/-! # Importing different secret RSA inputs produces identical public traces -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure PublicImportReady (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop where
  state : PublicArithmetic base dst np ep xp len k eLen nb eb xb s
  source : s.gpr .r4 = xp
  count : s.gpr .r6 = BitVec.ofNat 32 k

theorem publicInputArgs_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicArithmetic base dst np ep xp len k eLen nb eb xb s) :
    WP isa (.block PublicFn.inputArgs) s (PublicImportReady base dst np ep xp len k eLen nb eb xb) := by
  refine WP.mono (publicInputArgs_ok s h.stack) ?_
  rintro t ⟨source, count, mem, rest⟩
  exact ⟨h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr), source, count⟩

theorem publicImport_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicArithmetic base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicArithmetic base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.importInput (fun _ _ => True) := by
  let P := fun (s t : State) => PublicArithmetic base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicArithmetic base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  have args := (publicInputArgs_ct.mono (P' := P) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (fun s t h => ⟨publicInputArgs_ready s h.1, publicInputArgs_ready t h.2.1⟩)
  exact args.seq ((importOperand_ct (o := 1) (by decide)).mono
    (fun _ _ h => ⟨h.2.1.state.ready, h.2.2.state.ready, h.2.1.source, h.2.2.source,
      h.2.1.count, h.2.2.count, h.1⟩) (fun _ _ h => h))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicAcceptCT.lean`, which only this module imported.
section

/-! # Comparing and saving secret input acceptance reveals no acceptance decision -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem publicAccept_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicOperand base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicOperand base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.acceptInput (fun _ _ => True) := by
  let P := fun (s t : State) => PublicOperand base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicOperand base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  have compare := relCT_keep_sp (inputCompare_ct.mono (P' := P)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
  exact compare.seq saveAcceptance_ct

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicControlsCT.lean`, which only this module imported.
section

/-! # Exponent-control initialization is independent of secret input and acceptance -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem publicControls_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicAccepted base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicAccepted base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.controls (fun _ _ => True) := by
  let P := fun (s t : State) => PublicAccepted base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicAccepted base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  have wp (s : State) {xb : List Byte} (h : PublicAccepted base dst np ep xp len k eLen nb eb xb s) :
      WP isa (.block PublicFn.controlArgs) s (PublicAccepted base dst np ep xp len k eLen nb eb xb) := by
    refine WP.mono (publicControlArgs_ok s h.stack) ?_
    rintro t ⟨_, _, mem, rest⟩
    exact h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr)
  have args := (publicControlArgs_ct.mono (P' := P) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact args.seq (expControls_ct.mono (fun _ _ h => h.2.1.ready.ptr.trans h.2.2.ready.ptr.symm) (fun _ _ h => h))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicFinishCT.lean`, which only this module imported.
section

/-! # The final RSA output and status are released without input-dependent leakage -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem publicOutputArgs_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicResult base dst np ep xp len k eLen nb eb xb s) :
    WP isa (.block PublicFn.outputArgs) s (ExportMaskedInput base dst len (Spec.Rsa.modulusWords k) 6 k) := by
  refine WP.mono (publicOutputArgs_ok s h.stack) ?_
  rintro t ⟨index, output, count, mem, rest⟩
  have ready := h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr)
  have dims := pc_dimensions h.buffers.minLength h.buffers.maxLength h.buffers.space
  refine ⟨⟨ready.workspace, ready.layout, ready.width, ready.ptr, index⟩,
    by have := h.buffers.minLength; omega, dims.2.2.2.1, h.buffers.outputFit, ?_, h.buffers.outputSeparate,
    output, count, ?_, ?_⟩
  · rw [rest.wr]; exact h.buffers.write
  · rw [rest.sp]; have := h.stack.nowrap; omega
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stack.read (by decide) (by decide)

theorem publicFinish_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} (hk : 0 < k) :
    RelCT isa (fun s t => PublicResult base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicResult base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.finish (fun _ _ => True) := by
  let P := fun (s t : State) => PublicResult base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicResult base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  have args := (publicOutputArgs_ct.mono (P' := P) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (fun s t h => ⟨publicOutputArgs_ready s h.1, publicOutputArgs_ready t h.2.1⟩)
  exact args.seq ((exportMasked_ct (by decide : 6 < 8) hk).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/ExpBytesCT.lean`, which only this module imported.
section

/-! # The full exponent loop reveals only public exponent bytes and buffer dimensions -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem expBytes_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (positive : 0 < eb.length) :
    RelCT isa (fun s t => ExpByteState base ep len w M1 x1 eb 0 s ∧
      ExpByteState base ep len w M2 x2 eb 0 t ∧ s.sp = t.sp) expBytes (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = eb.length ∧ 0 < k ∧
    ExpByteState base ep len w M1 x1 eb j s ∧ ExpByteState base ep len w M2 x2 eb j t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) (.seq expByteHead (.seq expBits (.block expByteNext))) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ht, sp⟩ := h
    have hj : j < eb.length := by omega
    have ct := relCT_keep_sp (expByte_ct (base := base) (ep := ep + BitVec.ofNat 32 j)
      (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) (E := pre eb j) (b := eb[j]) fit) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨hs.input hj, ht.input hj, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1⟩ := expByteState_step s hs hj
    obtain ⟨_, _, run2, next2, zero2⟩ := expByteState_step t ht hj
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_ ) = some (!_ )
      rw [zero1, zero2]
    · intro again
      have notLast : j + 1 ≠ eb.length := by
        intro last
        change some (!_ ) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega, j + 1, by omega, by omega, next1, next2, sp'⟩
  exact (RelCT.loop I step eb.length).mono
    (fun _ _ h => ⟨0, by omega, positive, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/ExpPhaseCT.lean`, which only this module imported.
section

/-! # Complete RSA exponentiation reveals no input-dependent trace -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem expPhase_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (positive : 0 < eb.length) :
    RelCT isa (fun s t => ExpPhaseInput base ep len w M1 x1 eb s ∧
      ExpPhaseInput base ep len w M2 x2 eb t ∧ s.sp = t.sp) expPhase (fun _ _ => True) := by
  let P := fun (s t : State) => ExpPhaseInput base ep len w M1 x1 eb s ∧
    ExpPhaseInput base ep len w M2 x2 eb t ∧ s.sp = t.sp
  have wpInit (s : State) {M x : Nat} (h : ExpPhaseInput base ep len w M x eb s) :
      WP isa expInit s (ExpByteState base ep len w M x eb 0) :=
    WP.mono (expPhase_init_ready s h) (fun _ h => h.1)
  have init := (relCT_keep_sp ((expInit_ct fit).mono (P' := P)
    (fun _ _ h => ⟨⟨h.1.ready, by rw [h.1.modulus]; exact h.1.r2bound⟩,
      ⟨h.2.1.ready, by rw [h.2.1.modulus]; exact h.2.1.r2bound⟩, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wpInit s h.1, wpInit t h.2.1⟩)
  have wpBytes (s : State) {M x : Nat} (h : ExpByteState base ep len w M x eb 0 s) :
      WP isa expBytes s (ExpState base len w M x (Spec.Rsa.os2ip eb)) :=
    WP.mono (expPhase_bytes_ready s h positive) (fun _ h => h.1)
  have bytes := (relCT_keep_sp ((expBytes_ct (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) fit positive).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ ExpByteState base ep len w M1 x1 eb 0 s ∧
      ExpByteState base ep len w M2 x2 eb 0 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨wpBytes s h.2.1, wpBytes t h.2.2⟩)
  have finish := (exp_finish_ct (base := base) (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2)
    (E := Spec.Rsa.os2ip eb) fit).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ ExpState base len w M1 x1 (Spec.Rsa.os2ip eb) s ∧
      ExpState base len w M2 x2 (Spec.Rsa.os2ip eb) t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)
  exact init.seq (bytes.seq finish)

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicApplyCT.lean`, which only this module imported.
section

/-! # The complete public RSA arithmetic path is constant-time with respect to the input -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

structure PublicControlled (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop where
  state : PublicAccepted base dst np ep xp len k eLen nb eb xb s
  phase : ExpPhaseInput base ep len (Spec.Rsa.modulusWords k) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) eb s

theorem publicApply_ct_of_dims {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte}
    (hk : 0 < k) (he : 0 < eb.length) (fit : arrAt (Spec.Rsa.modulusWords k) 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => PublicArithmetic base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicArithmetic base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.applyInput (fun _ _ => True) := by
  have wpImport (s : State) {xb : List Byte} (h : PublicArithmetic base dst np ep xp len k eLen nb eb xb s) :
      WP isa PublicFn.importInput s (PublicOperand base dst np ep xp len k eLen nb eb xb) :=
    WP.mono (publicImport_ok s h) (fun _ h => h.1)
  have imported := (relCT_keep_sp (publicImport_ct (base := base) (dst := dst) (np := np) (ep := ep) (xp := xp)
    (len := len) (k := k) (eLen := eLen) (nb := nb) (eb := eb) (xb1 := xb1) (xb2 := xb2))
    (fun _ _ h => h.2.2)).wp (fun s t h => ⟨wpImport s h.1, wpImport t h.2.1⟩)
  have wpAccept (s : State) {xb : List Byte} (h : PublicOperand base dst np ep xp len k eLen nb eb xb s) :
      WP isa PublicFn.acceptInput s (PublicAccepted base dst np ep xp len k eLen nb eb xb) :=
    WP.mono (publicAccept_ok s h) (fun _ h => h.1)
  have accepted := (relCT_keep_sp (publicAccept_ct.mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PublicOperand base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicOperand base dst np ep xp len k eLen nb eb xb2 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨wpAccept s h.2.1, wpAccept t h.2.2⟩)
  have wpControls (s : State) {xb : List Byte} (h : PublicAccepted base dst np ep xp len k eLen nb eb xb s) :
      WP isa PublicFn.controls s (PublicControlled base dst np ep xp len k eLen nb eb xb) :=
    WP.mono (publicControls_ok s h) (fun _ h => ⟨h.1, h.2.1⟩)
  have controlled := (relCT_keep_sp (publicControls_ct.mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PublicAccepted base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicAccepted base dst np ep xp len k eLen nb eb xb2 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨wpControls s h.2.1, wpControls t h.2.2⟩)
  have wpPower (s : State) {xb : List Byte} (h : PublicControlled base dst np ep xp len k eLen nb eb xb s) :
      WP isa expPhase s (PublicResult base dst np ep xp len k eLen nb eb xb) :=
    WP.mono (publicExponentiate_ok s h.state h.phase) (fun _ h => h.1)
  have powered := (relCT_keep_sp ((expPhase_ct fit he).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PublicControlled base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicControlled base dst np ep xp len k eLen nb eb xb2 t)
    (fun _ _ h => ⟨h.2.1.phase, h.2.2.phase, h.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨wpPower s h.2.1, wpPower t h.2.2⟩)
  have finished := (publicFinish_ct hk).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PublicResult base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicResult base dst np ep xp len k eLen nb eb xb2 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)
  exact imported.seq (accepted.seq (controlled.seq (powered.seq finished)))

theorem publicApply_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicArithmetic base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicArithmetic base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.applyInput (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  have dims := pc_dimensions h.1.buffers.minLength h.1.buffers.maxLength h.1.buffers.space
  have fit : arrAt (Spec.Rsa.modulusWords k) 3 + 32 ≤ 8 * len := by
    have bound := array_end_le (w := Spec.Rsa.modulusWords k) (by decide : 3 < 8)
    have := dims.1
    omega
  exact publicApply_ct_of_dims (by have := h.1.buffers.minLength; omega)
    (by rw [h.1.buffers.exponent.length]; exact h.1.buffers.exponentPositive) fit s t tr1 tr2 u v h e1 e2

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicValidCT.lean`, which only this module imported.
section

/-! # Modulus precomputation and the public RSA arithmetic path share a public trace -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem publicValid_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicValidInput base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicValidInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.valid (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  have countFit := (pc_dimensions h.1.buffers.minLength h.1.buffers.maxLength h.1.buffers.space).2.2.2.2
  let P := fun (s t : State) => PublicPrepared base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicPrepared base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  have wp (s : State) {xb : List Byte} (h : PublicPrepared base dst np ep xp len k eLen nb eb xb s) :
      WP isa precompute s (PublicArithmetic base dst np ep xp len k eLen nb eb xb) :=
    WP.mono (publicPrecompute_ok s h) (fun _ h => h.1)
  have ready := (relCT_keep_sp ((precompute_ct countFit).mono (P' := P)
    (fun _ _ h => ⟨h.1.input, h.2.1.input, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have applyCT := publicApply_ct.mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PublicArithmetic base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicArithmetic base dst np ep xp len k eLen nb eb xb2 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)
  exact (publicPrepare_ct.seq (ready.seq applyCT)) s t tr1 tr2 u v h e1 e2

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure PublicModulusInput (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop extends PublicBodyInput base dst np ep xp len k eLen nb eb xb s where
  source : s.gpr .r4 = np
  count : s.gpr .r6 = BitVec.ofNat 32 k

structure PublicModulusChecked (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop extends PublicModulusInput base dst np ep xp len k eLen nb eb xb s where
  flag : s.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k

theorem publicModulusArgs_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} (h : PublicBodyInput base dst np ep xp len k eLen nb eb xb s) :
    WP isa (.block PcFn.inputs) s (PublicModulusInput base dst np ep xp len k eLen nb eb xb) := by
  refine WP.mono (pcInputs_ok s h.stack.pcStack) ?_
  rintro t ⟨source, count, mem, rest⟩
  exact ⟨h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr), source, count⟩

theorem publicModulusCheck_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} (h : PublicModulusInput base dst np ep xp len k eLen nb eb xb s) :
    WP isa (.block modulusCheck) s (PublicModulusChecked base dst np ep xp len k eLen nb eb xb) := by
  refine WP.mono (modulusCheck_ok s h.buffers.minLength h.buffers.maxLength h.buffers.modulus.fits
    h.buffers.modulus.read h.source h.count) ?_
  rintro t ⟨flag, mem, rest⟩
  exact ⟨⟨h.toPublicBodyInput.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr),
    (rest.gpr .r4 (by simp)).trans h.source, (rest.gpr .r6 (by simp)).trans h.count⟩,
    by rw [h.buffers.modulus.bytes] at flag; exact flag⟩

theorem publicModulus_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicBodyInput base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicBodyInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.modulus (fun _ _ => True) := by
  let P := fun (s t : State) => PublicBodyInput base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicBodyInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  let Q := fun (s t : State) => s.sp = t.sp ∧ PublicModulusInput base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicModulusInput base dst np ep xp len k eLen nb eb xb2 t
  have args := ((stackLoads_ct [(.r4, 8), (.r6, 12)]).mono (P' := P)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (fun s t h => ⟨publicModulusArgs_ready s h.1, publicModulusArgs_ready t h.2.1⟩)
  have check : RelCT isa Q (.block modulusCheck) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨modulusCheck_ct s t tr1 tr2 u v trivial trivial
      ⟨h.2.1.source.trans h.2.2.source.symm, h.2.1.count.trans h.2.2.count.symm⟩ e1 e2, trivial⟩
  have ready := (relCT_keep_sp check (fun _ _ h => h.1)).wp
    (fun s t h => ⟨publicModulusCheck_ready s h.2.1, publicModulusCheck_ready t h.2.2⟩)
  refine args.seq (ready.seq (RelCT.ite ?_ ?_ ?_))
  · intro s t h
    change some s.z = some t.z
    rw [h.2.1.flag, h.2.2.flag]
  · apply (publicValid_ct (base := base) (dst := dst) (np := np) (ep := ep) (xp := xp)
      (len := len) (k := k) (eLen := eLen) (nb := nb) (eb := eb) (xb1 := xb1) (xb2 := xb2)).mono ?_ (fun _ _ h => h)
    intro s t h
    have flag : s.z = true := Option.some.inj h.2
    have good := h.1.2.1.flag.symm.trans flag
    exact ⟨⟨h.1.2.1.toPublicBodyInput, good, h.1.2.1.source, h.1.2.1.count⟩,
      ⟨h.1.2.2.toPublicBodyInput, good, h.1.2.2.source, h.1.2.2.count⟩, h.1.1⟩
  · apply (publicFail_ct (base := base) (dst := dst) (np := np) (ep := ep) (xp := xp)
      (len := len) (k := k) (eLen := eLen) (nb := nb) (eb := eb) (xb1 := xb1) (xb2 := xb2)).mono ?_ (fun _ _ h => h)
    intro s t h
    exact ⟨h.1.2.1.toPublicBodyInput, h.1.2.2.toPublicBodyInput, h.1.1⟩

end VG.Proof.Bignum.Arm
