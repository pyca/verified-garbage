module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild

public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowBuild
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBuildCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # Shared-window table preparation and multiplication have public traces -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.SharedWindow
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.Bignum.Arm.TwoExp (Montgomery MontgomeryTiming OpInput)

theorem tablePrepare_ct {base : BitVec 32} {len w M1 M2 x1 x2 : Nat}
    (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => ExpState base len w M1 x1 0 s ∧ ExpState base len w M2 x2 0 t ∧ s.sp = t.sp)
      VG.Impl.Bignum.Arm.SharedWindow.tablePrepare (fun _ _ => True) := by
  have entry (j : Nat) {M x : Nat} (s : State) (h : TablePre base len w M x j s) : EntryReady base len w j s :=
    ⟨h.power.ready, h.entry⟩
  unfold VG.Impl.Bignum.Arm.SharedWindow.tablePrepare
  refine relCT_chain (Q₁ := TablePre base len w M1 x1 0) (Q₂ := TablePre base len w M2 x2 0)
    (tableInit_ct.mono (fun _ _ h => h.1.ready.ptr.trans h.2.1.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => WP.mono (tableStage0_ok s h fits) fun _ k => k.1)
    (fun s h => WP.mono (tableStage0_ok s h fits) fun _ k => k.1) ?_
  refine relCT_chain (Q₁ := TablePre base len w M1 x1 1) (Q₂ := TablePre base len w M2 x2 1)
    ((entryStepCT (a := 6) (j := 0) (by decide) (by decide) fits).mono
      (fun _ _ h => ⟨entry 0 _ h.1, entry 0 _ h.2.1, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (tableStageStep_ok s h (a := 6) (by decide) (by decide) h.power.powerBound
      h.power.powerValue) fun _ k => k.1)
    (fun s h => WP.mono (tableStageStep_ok s h (a := 6) (by decide) (by decide) h.power.powerBound
      h.power.powerValue) fun _ k => k.1) ?_
  refine relCT_chain (Q₁ := TablePre base len w M1 x1 2) (Q₂ := TablePre base len w M2 x2 2)
    ((entryStepCT (a := 5) (j := 1) (by decide) (by decide) fits).mono
      (fun _ _ h => ⟨entry 1 _ h.1, entry 1 _ h.2.1, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (tableStageStep_ok s h (a := 5) (by decide) (by decide) h.power.inputBound
      (by rw [Nat.pow_one]; exact h.power.inputValue)) fun _ k => k.1)
    (fun s h => WP.mono (tableStageStep_ok s h (a := 5) (by decide) (by decide) h.power.inputBound
      (by rw [Nat.pow_one]; exact h.power.inputValue)) fun _ k => k.1) ?_
  exact prodInit_ct

section
variable {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
variable (A : Montgomery base len w P regions) (ct : MontgomeryTiming A)
include ct

theorem tableBody_ct {M1 M2 x1 x2 j : Nat} (hj : j < 8) (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => (BuildInv base len w M1 x1 j s ∧ P s) ∧
      (BuildInv base len w M2 x2 j t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedWindow.tableBody A.op) (fun _ _ => True) := by
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op5 : Operand 5 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have entryOf (s : State) {M x : Nat} (h : BuildInv base len w M x j s ∧ P s) :
      WP isa (A.op 1 1 5) s (EntryReady base len w j) := by
    have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega) h.1.fits
    refine WP.mono (A.op_ok s 1 1 5 h.1.power.ready h.2 op1 op1 op5 (by decide)
      (by rw [h.1.power.modulus]; exact h.1.power.inputBound)) ?_
    rintro t ⟨ready, _, _, _, keeps, _, _, _⟩
    exact ⟨ready, (keeps_header_readW keeps size (d := 220) (bits := 32) (by decide)).trans h.1.entry⟩
  unfold VG.Impl.Bignum.Arm.SharedWindow.tableBody
  exact relCT_chain ((ct.op_ct 1 1 5 op1 op1 op5).mono
    (fun _ _ h => ⟨⟨h.1.1.power.ready, h.1.2, by rw [h.1.1.power.modulus]; exact h.1.1.power.inputBound⟩,
      ⟨h.2.1.1.power.ready, h.2.1.2, by rw [h.2.1.1.power.modulus]; exact h.2.1.1.power.inputBound⟩, h.2.2⟩)
    (fun _ _ h => h)) (fun s h => entryOf s h) (fun s h => entryOf s h) (entryStepCT (by decide) hj fits)

theorem tableLoop_ct {M1 M2 x1 x2 : Nat} (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => (BuildInv base len w M1 x1 2 s ∧ P s) ∧
      (BuildInv base len w M2 x2 2 t ∧ P t) ∧ s.sp = t.sp)
      (.loop (VG.Impl.Bignum.Arm.SharedWindow.tableBody A.op) .ne) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = 8 ∧ 0 < k ∧ 2 ≤ j ∧
    (BuildInv base len w M1 x1 j s ∧ P s) ∧ (BuildInv base len w M2 x2 j t ∧ P t) ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) (VG.Impl.Bignum.Arm.SharedWindow.tableBody A.op) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hj, hs, ht, sp⟩ := h
    have c := relCT_keep_sp (tableBody_ct A ct (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2)
      (j := j) (by omega) fits) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := c s t tr1 tr2 u z ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1, _, p1, _, _⟩ := sharedTableBody_ok A s hs.1 hs.2 hj (by omega)
    obtain ⟨_, _, run2, next2, zero2, _, p2, _, _⟩ := sharedTableBody_ok A t ht.1 ht.2 hj (by omega)
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_) = some (!_)
      rw [zero1, zero2]
    · intro again
      have notLast : j + 1 ≠ 8 := by
        intro last
        change some (!_) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega, j + 1, by omega, by omega, by omega, ⟨next1, p1⟩, ⟨next2, p2⟩, sp'⟩
  exact (RelCT.loop I step 6).mono (fun _ _ h => ⟨2, by decide, by decide, by decide, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

theorem tableBuild_ct {M1 M2 x1 x2 : Nat} (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => (ExpState base len w M1 x1 0 s ∧ P s) ∧
      (ExpState base len w M2 x2 0 t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedWindow.tableBuild A.op) (fun _ _ => True) := by
  have ready (s : State) {M x : Nat} (h : ExpState base len w M x 0 s ∧ P s) :
      WP isa VG.Impl.Bignum.Arm.SharedWindow.tablePrepare s fun t => BuildInv base len w M x 2 t ∧ P t :=
    WP.mono (sharedTablePrepare_ok A s h.1 h.2 fits) fun _ k => ⟨k.1, k.2.2.1⟩
  unfold VG.Impl.Bignum.Arm.SharedWindow.tableBuild
  exact relCT_chain ((tablePrepare_ct fits).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    (fun s h => ready s h) (fun s h => ready s h) (tableLoop_ct A ct fits)

end
end VG.Proof.Bignum.Arm.SharedWindow
