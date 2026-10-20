module

public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowApplyCT
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowBytes

import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhase
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowBuildCT
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowApply
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! # The shared three-bit exponentiation schedule hides scalar values -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.SharedWindow
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.Bignum.Arm.TwoExp (Montgomery MontgomeryTiming OpInput)

theorem phase_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb1 eb2 : List Byte}
    {P : State → Prop} {regions : List Region}
    (K : Montgomery base len w P regions) (ct : MontgomeryTiming K)
    (fits : arrAt w 16 ≤ 8 * len) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb1.length⟩ r) :
    RelCT isa (fun s t => (ExpPhaseInput base ep len w M1 x1 eb1 s ∧ P s) ∧
      (ExpPhaseInput base ep len w M2 x2 eb2 t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedWindow.phase K.op) (fun _ _ => True) := by
  let F := fun (M x : Nat) (eb : List Byte) (s : State) =>
    ∃ A p, WinState base len w M x A p (8 * eb.length % 3) s ∧ A + p = Spec.Rsa.os2ip eb
  have separate2 : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb2.length⟩ r := by
    rw [← length]; exact separate
  have finishReady (s : State) {M x : Nat} {eb : List Byte} (h : F M x eb s ∧ P s) :
      WP isa (VG.Impl.Bignum.Arm.SharedWindow.apply K.op) s (OpInput base len w P 7) := by
    obtain ⟨⟨A, p, state, _⟩, hp⟩ := h
    refine WP.mono (sharedWindowApply_ok K s state.power hp state.table fits (pending_digit state) state.digit) ?_
    rintro t ⟨power, _, _, _, _, pt, _, _⟩
    exact ⟨power.ready, pt, by rw [power.one]; exact power.ready.modulus⟩
  have applying : RelCT isa (fun s t => (F M1 x1 eb1 s ∧ P s) ∧
      (F M2 x2 eb2 t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedWindow.apply K.op) (fun _ _ => True) := by
    intro s t tr1 tr2 u z h e1 e2
    obtain ⟨⟨⟨A1, p1, state1, _⟩, ps⟩, ⟨⟨A2, p2, state2, _⟩, pt⟩, sp⟩ := h
    exact apply_ct K ct fits s t tr1 tr2 u z
      ⟨⟨⟨state1.power, state1.table, pending_digit state1, state1.digit⟩, ps⟩,
        ⟨⟨state2.power, state2.table, pending_digit state2, state2.digit⟩, pt⟩, sp⟩ e1 e2
  have reset (s : State) {M x : Nat} {eb : List Byte} (h : WinReady base ep len w M x eb s ∧ P s) :
      WP isa (.block windowReset) s fun t => WinByteLoop base ep len w M x eb 0 t ∧ P t :=
    WP.mono (phaseReset_ok s h.1) fun _ k => ⟨k.1, K.stable k.2.1 k.2.2 h.2⟩
  unfold VG.Impl.Bignum.Arm.SharedWindow.phase
  refine relCT_chain (Q₁ := fun s => ExpByteState base ep len w M1 x1 eb1 0 s ∧ P s)
    (Q₂ := fun s => ExpByteState base ep len w M2 x2 eb2 0 s ∧ P s)
    ((init_ct K ct).mono
      (fun _ _ h => ⟨⟨⟨h.1.1.ready, by rw [h.1.1.modulus]; exact h.1.1.r2bound⟩, h.1.2⟩,
        ⟨⟨h.2.1.1.ready, by rw [h.2.1.1.modulus]; exact h.2.1.1.r2bound⟩, h.2.1.2⟩, h.2.2⟩)
      (fun _ _ h => h))
    (fun s h => WP.mono (sharedPhaseInit_ready K s h.1 h.2 separate) fun _ k => ⟨k.1, k.2.1⟩)
    (fun s h => WP.mono (sharedPhaseInit_ready K s h.1 h.2 separate2) fun _ k => ⟨k.1, k.2.1⟩) ?_
  refine relCT_chain (Q₁ := fun s => WinReady base ep len w M1 x1 eb1 s ∧ P s)
    (Q₂ := fun s => WinReady base ep len w M2 x2 eb2 s ∧ P s)
    ((tableBuild_ct K ct fits).mono
      (fun _ _ h => ⟨⟨h.1.1.power, h.1.2⟩, ⟨h.2.1.1.power, h.2.1.2⟩, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (sharedPhaseTable_ok K s h.1 h.2 fits separate) fun _ k => ⟨k.1, k.2.1⟩)
    (fun s h => WP.mono (sharedPhaseTable_ok K s h.1 h.2 fits separate2) fun _ k => ⟨k.1, k.2.1⟩) ?_
  refine relCT_chain
    (windowReset_ct.mono (fun _ _ h => h.1.1.power.ready.ptr.trans h.2.1.1.power.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => reset s h) (fun s h => reset s h) ?_
  refine relCT_chain (Q₁ := fun s => F M1 x1 eb1 s ∧ P s) (Q₂ := fun s => F M2 x2 eb2 s ∧ P s)
    (bytes_ct K ct fits positive length separate)
    (fun s h => WP.mono (sharedWindowBytes_ok K s h.1 h.2 positive separate) fun _ k => ⟨k.1, k.2.1⟩)
    (fun s h => WP.mono (sharedWindowBytes_ok K s h.1 h.2 (by omega) separate2) fun _ k => ⟨k.1, k.2.1⟩) ?_
  exact relCT_chain applying (fun s h => finishReady s h) (fun s h => finishReady s h)
    (ct.op_ct 6 6 7
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]))

end VG.Proof.Bignum.Arm.SharedWindow
