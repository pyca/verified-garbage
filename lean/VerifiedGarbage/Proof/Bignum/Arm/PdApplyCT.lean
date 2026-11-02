module
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Proof.Bignum.Arm.PdArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpPhaseInput

import VerifiedGarbage.Proof.Bignum.Arm.PdInputImportCT
import VerifiedGarbage.Proof.Bignum.Arm.PdAcceptCT
import VerifiedGarbage.Proof.Bignum.Arm.PdControlsCT
import VerifiedGarbage.Proof.Bignum.Arm.PdFinishCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpPhaseCT
import VerifiedGarbage.Proof.Bignum.Arm.PdControls
import VerifiedGarbage.Proof.Bignum.Arm.PdAccept
import VerifiedGarbage.Proof.Bignum.Arm.PdInputImport
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT

/-! # The complete public RSA arithmetic path is constant-time with respect to the input -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

structure PdControlled (base dst np ep xp : BitVec 32) (len k eLen N R : Nat)
    (eb xb : List Byte) (s : State) : Prop where
  state : PdAccepted base dst np ep xp len k eLen N R eb xb s
  phase : ConditionalExp.ExpPhaseInput (pdGood k N R) base ep len (Spec.Rsa.modulusWords k) N (Spec.Rsa.os2ip xb) eb s

theorem pdApply_ct_of_dims {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb1 xb2 : List Byte}
    (hk : 0 < k) (he : 0 < eb.length) (fit : arrAt (Spec.Rsa.modulusWords k) 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => PdArithmetic base dst np ep xp len k eLen N R eb xb1 s ∧
      PdArithmetic base dst np ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp)
      PublicFn.applyInput (fun _ _ => True) := by
  have wpImport (s : State) {xb : List Byte} (h : PdArithmetic base dst np ep xp len k eLen N R eb xb s) :
      WP isa PublicFn.importInput s (PdOperand base dst np ep xp len k eLen N R eb xb) :=
    WP.mono (pdInputImport_ok s h) (fun _ h => h.1)
  have imported := (relCT_keep_sp (pdInputImport_ct (base := base) (dst := dst) (np := np) (ep := ep) (xp := xp)
    (len := len) (k := k) (eLen := eLen) (N := N) (R := R) (eb := eb) (xb1 := xb1) (xb2 := xb2))
    (fun _ _ h => h.2.2)).wp (fun s t h => ⟨wpImport s h.1, wpImport t h.2.1⟩)
  have wpAccept (s : State) {xb : List Byte} (h : PdOperand base dst np ep xp len k eLen N R eb xb s) :
      WP isa PublicFn.acceptInput s (PdAccepted base dst np ep xp len k eLen N R eb xb) :=
    WP.mono (pdAccept_ok s h) (fun _ h => h.1)
  have accepted := (relCT_keep_sp (pdAccept_ct.mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PdOperand base dst np ep xp len k eLen N R eb xb1 s ∧
      PdOperand base dst np ep xp len k eLen N R eb xb2 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨wpAccept s h.2.1, wpAccept t h.2.2⟩)
  have wpControls (s : State) {xb : List Byte} (h : PdAccepted base dst np ep xp len k eLen N R eb xb s) :
      WP isa PublicFn.controls s (PdControlled base dst np ep xp len k eLen N R eb xb) :=
    WP.mono (pdControls_ok s h) (fun _ h => ⟨h.1, h.2.1⟩)
  have controlled := (relCT_keep_sp (pdControls_ct.mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PdAccepted base dst np ep xp len k eLen N R eb xb1 s ∧
      PdAccepted base dst np ep xp len k eLen N R eb xb2 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨wpControls s h.2.1, wpControls t h.2.2⟩)
  have wpPower (s : State) {xb : List Byte} (h : PdControlled base dst np ep xp len k eLen N R eb xb s) :
      WP isa expPhase s (PdResult base dst np ep xp len k eLen N R eb xb) :=
    WP.mono (pdExponentiate_ok s h.state h.phase) (fun _ h => h.1)
  have powered := (relCT_keep_sp ((ConditionalExp.expPhase_ct (ok := pdGood k N R) fit he).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PdControlled base dst np ep xp len k eLen N R eb xb1 s ∧
      PdControlled base dst np ep xp len k eLen N R eb xb2 t)
    (fun _ _ h => ⟨h.2.1.phase, h.2.2.phase, h.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨wpPower s h.2.1, wpPower t h.2.2⟩)
  have finished := (pdFinish_ct hk).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PdResult base dst np ep xp len k eLen N R eb xb1 s ∧
      PdResult base dst np ep xp len k eLen N R eb xb2 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)
  exact imported.seq (accepted.seq (controlled.seq (powered.seq finished)))

theorem pdApply_ct {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PdArithmetic base dst np ep xp len k eLen N R eb xb1 s ∧
      PdArithmetic base dst np ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp)
      PublicFn.applyInput (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  have dims := pc_dimensions h.1.buffers.minLength h.1.buffers.maxLength h.1.buffers.space
  have fit : arrAt (Spec.Rsa.modulusWords k) 3 + 32 ≤ 8 * len := by
    have bound := array_end_le (w := Spec.Rsa.modulusWords k) (by decide : 3 < 8)
    have := dims.1
    omega
  exact pdApply_ct_of_dims (by have := h.1.buffers.minLength; omega)
    (by rw [h.1.buffers.exponent.length]; exact h.1.buffers.exponentPositive) fit s t tr1 tr2 u v h e1 e2

end VG.Proof.Bignum.Arm
