module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicApply
public import VerifiedGarbage.Proof.Bignum.Arm.PublicImportCT
public import VerifiedGarbage.Proof.Bignum.Arm.PublicAcceptCT
public import VerifiedGarbage.Proof.Bignum.Arm.PublicControlsCT
public import VerifiedGarbage.Proof.Bignum.Arm.PublicFinishCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The complete public RSA arithmetic path is constant-time with respect to the input -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

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
