module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtCoefficient
public import VerifiedGarbage.Proof.Bignum.Arm.CrtInverseInput
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperand
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! # Loading and multiplying by qInv exposes no inverse or residue values -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (numAt arrAt Operand)

theorem crt_timesInverse_ct {base src : BitVec 32} {len w k M1 M2 : Nat} {bs1 bs2 : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => CrtInverseInput base src len w k M1 bs1 s ∧
      CrtInverseInput base src len w k M2 bs2 t ∧ s.sp = t.sp) timesInverse (fun _ _ => True) := by
  let P := fun (s t : State) => CrtInverseInput base src len w k M1 bs1 s ∧
    CrtInverseInput base src len w k M2 bs2 t ∧ s.sp = t.sp
  let Q := fun (b : Nat) (s : State) => ArithmeticReady base len w s ∧
    numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0
  have op (q : Nat) (hq : q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 5) : Operand q := by
    rcases hq with rfl | rfl | rfl | rfl <;> simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have load : RelCT isa P (savedOperand 1 96 100) (fun _ _ => True) :=
    (savedOperand_ct (base := base) (src := src) (len := len) (w := w) (k := k)
      (ps := 96) (cs := 100) (bs1 := bs1) (bs2 := bs2) (by decide : 1 < 8)).mono
      (fun _ _ h => ⟨⟨h.1.ready, h.1.source⟩, ⟨h.2.1.ready, h.2.1.source⟩, h.2.2⟩) (fun _ _ _ => trivial)
  have loadWP (s : State) {M : Nat} {bs : List Byte} (h : CrtInverseInput base src len w k M bs s) :
      WP isa (savedOperand 1 96 100) s (Q 4) := by
    have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
    have positive : 0 < M := by have := h.ready.modulus; rw [h.modulus] at this; omega
    refine WP.mono (savedOperand_ok s h.ready h.source (by decide : 1 < 8) (by decide) h.positive h.fits) ?_
    rintro t ⟨ready, _, keeps, _, _⟩
    have modulus := (keeps_array_num keeps fits (op 0 (by decide)) (by decide)).trans h.modulus
    have r2 := (keeps_array_num keeps fits (op 4 (by decide)) (by decide)).trans h.r2
    exact ⟨ready, by rw [modulus, r2]; exact Nat.mod_lt _ positive⟩
  have first := (relCT_keep_sp load (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨loadWP s h.1, loadWP t h.2.1⟩)
  have encode : RelCT isa (fun (s t : State) => s.sp = t.sp ∧ Q 4 s ∧ Q 4 t)
      (montOp 1 1 4) (fun _ _ => True) :=
    (montOp_ct (op 1 (by decide)) (op 1 (by decide)) (op 4 (by decide)) fit).mono
      (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial)
  have encodeWP (s : State) (h : Q 4 s) : WP isa (montOp 1 1 4) s (Q 1) := by
    refine WP.mono (montOp_ok s h.1 (op 1 (by decide)) (op 1 (by decide)) (op 4 (by decide)) (by decide) h.2) ?_
    rintro t ⟨ready, modulus, bound, _, _, _, _⟩
    exact ⟨ready, by rw [modulus]; exact bound⟩
  have second := (relCT_keep_sp encode (fun _ _ h => h.1)).wp
    (fun s t h => ⟨encodeWP s h.2.1, encodeWP t h.2.2⟩)
  exact first.seq (second.seq ((montOp_ct (op 5 (by decide)) (op 5 (by decide)) (op 1 (by decide)) fit).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial)))

end VG.Proof.Bignum.Arm
