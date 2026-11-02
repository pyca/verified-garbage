module

public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Bignum.Arm.WindowScanCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExpInitCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout

/-! # Shared window initialization and masked table application are constant time -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.SharedWindow
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.Bignum.Arm.TwoExp (Montgomery MontgomeryTiming OpInput)

section
variable {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
variable (A : Montgomery base len w P regions) (ct : MontgomeryTiming A)
include ct

theorem init_ct :
    RelCT isa (fun s t => (ExpInitReady base len w s ∧ P s) ∧
      (ExpInitReady base len w t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedWindow.init A.op) (fun _ _ => True) := by
  have op (q : Nat) (hq : q = 1 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) : Operand q := by
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  let Q := fun s : State => ExpInitReady base len w s ∧ P s ∧ numAt s.mem (State.addr base) w 7 = 1
  have one (s : State) (h : ExpInitReady base len w s ∧ P s) : WP isa (smallConst 7 1) s Q := by
    have fits : arrAt w 8 ≤ 8 * len := h.1.ready.width ▸ h.1.ready.layout.2.2.1
    refine WP.mono (smallConst_ok s (1 : BitVec 32) h.1.ready (o := 7) (by decide) (by decide) (by decide) (by decide)) ?_
    rintro t ⟨ready, one, _, keeps, frame, rest⟩
    have r2 := keeps_array_num keeps fits (q := 4) (op 4 (by decide)) (by decide)
    have modulus := keeps_array_num keeps fits (q := 0) (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    exact ⟨⟨ready, by rw [r2, modulus]; exact h.1.r2bound⟩, A.stable frame rest h.2, one⟩
  have first (s : State) (h : Q s) : WP isa (A.op 6 4 7) s fun t => ExpInitReady base len w t ∧ P t := by
    have fits : arrAt w 8 ≤ 8 * len := h.1.ready.width ▸ h.1.ready.layout.2.2.1
    refine WP.mono (A.op_ok s 6 4 7 h.1.ready h.2.1 (op 6 (by decide)) (op 4 (by decide)) (op 7 (by decide))
      (by decide) (by rw [h.2.2]; exact h.1.ready.modulus)) ?_
    rintro t ⟨ready, modulus, _, _, keeps, pt, _, _⟩
    have r2 := keeps_array_num keeps fits (q := 4) (op 4 (by decide)) (by decide)
    exact ⟨⟨ready, by rw [r2, modulus]; exact h.1.r2bound⟩, pt⟩
  unfold VG.Impl.Bignum.Arm.SharedWindow.init
  refine relCT_chain ((smallConst_ct (1 : BitVec 32) (o := 7) (by decide) (by decide) (by decide)).mono
    (fun _ _ h => ⟨h.1.1.ready, h.2.1.1.ready, h.2.2⟩) (fun _ _ h => h)) one one ?_
  refine relCT_chain ((ct.op_ct 6 4 7 (op 6 (by decide)) (op 4 (by decide)) (op 7 (by decide))).mono
    (fun _ _ h => ⟨⟨h.1.1.ready, h.1.2.1, by rw [h.1.2.2]; exact h.1.1.ready.modulus⟩,
      ⟨h.2.1.1.ready, h.2.1.2.1, by rw [h.2.1.2.2]; exact h.2.1.1.ready.modulus⟩, h.2.2⟩)
    (fun _ _ h => h)) first first ?_
  exact (ct.op_ct 5 1 4 (op 5 (by decide)) (op 1 (by decide)) (op 4 (by decide))).mono
    (fun _ _ h => ⟨⟨h.1.1.ready, h.1.2, h.1.1.r2bound⟩,
      ⟨h.2.1.1.ready, h.2.1.2, h.2.1.1.r2bound⟩, h.2.2⟩) (fun _ _ h => h)

theorem apply_ct {M1 M2 x1 x2 E1 E2 d1 d2 : Nat} (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => (ScanPre base len w M1 x1 E1 d1 s ∧ P s) ∧
      (ScanPre base len w M2 x2 E2 d2 t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedWindow.apply A.op) (fun _ _ => True) := by
  have op6 : Operand 6 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have selected (s : State) {M x E d : Nat} (h : ScanPre base len w M x E d s ∧ P s) :
      WP isa scan s (OpInput base len w P 1) := by
    refine WP.mono (scan_ok s h.1.power h.1.table fits h.1.digitLt h.1.digit) ?_
    rintro t ⟨power, table, value, _, _, frame, rest⟩
    exact ⟨power.ready, A.stable frame rest h.2,
      by rw [value, power.modulus]; exact (table d h.1.digitLt).1⟩
  have multiplied (s : State) (h : OpInput base len w P 1 s) :
      WP isa (A.op 6 6 1) s fun t => t.gpr .r0 = base :=
    WP.mono (A.op_ok s 6 6 1 h.1 h.2.1 op6 op6 op1 (by decide) h.2.2) fun _ k => k.1.ptr
  unfold VG.Impl.Bignum.Arm.SharedWindow.apply
  refine relCT_chain ((scan_ct fits).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    (fun s h => selected s h) (fun s h => selected s h) ?_
  exact relCT_chain (ct.op_ct 6 6 1 op6 op6 op1) multiplied multiplied
    (windowReset_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

end
end VG.Proof.Bignum.Arm.SharedWindow
