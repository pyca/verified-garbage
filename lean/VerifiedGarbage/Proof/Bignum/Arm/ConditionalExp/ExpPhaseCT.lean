module

public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpPhaseInput
public import VerifiedGarbage.Proof.Bignum.Arm.ExpInitCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpStep
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpStepCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpState

/-! # Complete RSA exponentiation reveals no input-dependent trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
variable {ok : Prop} {Q : State → Prop} {regions : List Region}

/-- `expInit_ct`, by `K`'s product. -/
theorem expInitWith_ct {base : BitVec 32} {len w : Nat} (K : TwoExp.Montgomery base len w Q regions)
    (ct : TwoExp.MontgomeryTiming K) :
    RelCT isa (fun s t => (ExpInitReady base len w s ∧ Q s) ∧ (ExpInitReady base len w t ∧ Q t) ∧ s.sp = t.sp)
      (expInitWith K.op) (fun _ _ => True) := by
  have fitsOf := fun {s : State} (h : ExpInitReady base len w s) =>
    (h.ready.width ▸ h.ready.layout.2.2.1 : arrAt w 8 ≤ 8 * len)
  have oneWp (s : State) (h : ExpInitReady base len w s ∧ Q s) :
      WP isa (smallConst 7 1) s fun t => (ExpInitReady base len w t ∧ Q t) ∧
        numAt t.mem (State.addr base) w 7 = 1 := by
    refine WP.mono (smallConst_ok s (1 : BitVec 32) h.1.ready (o := 7) (by decide) (by decide) (by decide)
      (by decide)) ?_
    rintro t ⟨ready, one, _, keeps, frame, rest⟩
    have r2 := keeps_array_num keeps (fitsOf h.1) (q := 4)
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    have modulus := keeps_array_num keeps (fitsOf h.1) (q := 0)
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    exact ⟨⟨⟨ready, by rw [r2, modulus]; exact h.1.r2bound⟩, K.stable frame rest h.2⟩, one⟩
  have init := (relCT_keep_sp ((smallConst_ct (base := base) (len := len) (w := w) (o := 7) 1
    (by decide) (by decide) (by decide)).mono
    (P' := fun (s t : State) => (ExpInitReady base len w s ∧ Q s) ∧ (ExpInitReady base len w t ∧ Q t) ∧
      s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1.ready, h.2.1.1.ready, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨oneWp s h.1, oneWp t h.2.1⟩)
  have op6 : Operand 6 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have yWp (s : State) (h : (ExpInitReady base len w s ∧ Q s) ∧ numAt s.mem (State.addr base) w 7 = 1) :
      WP isa (K.op 6 4 7) s fun t => ExpInitReady base len w t ∧ Q t := by
    refine WP.mono (K.op_ok s 6 4 7 h.1.1.ready h.1.2 op6 op4 op7 (by decide)
      (by rw [h.2]; exact h.1.1.ready.modulus)) ?_
    rintro t ⟨ready, modulus, _, _, keeps, qt, _, _⟩
    have r2 := keeps_array_num keeps (fitsOf h.1.1) (q := 4)
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    exact ⟨⟨ready, by rw [r2, modulus]; exact h.1.1.r2bound⟩, qt⟩
  have y := (relCT_keep_sp ((ct.op_ct 6 4 7 op6 op4 op7).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧
      ((ExpInitReady base len w s ∧ Q s) ∧ numAt s.mem (State.addr base) w 7 = 1) ∧
      ((ExpInitReady base len w t ∧ Q t) ∧ numAt t.mem (State.addr base) w 7 = 1))
    (fun _ _ h => ⟨⟨h.2.1.1.1.ready, h.2.1.1.2, by rw [h.2.1.2]; exact h.2.1.1.1.ready.modulus⟩,
      ⟨h.2.2.1.1.ready, h.2.2.1.2, by rw [h.2.2.2]; exact h.2.2.1.1.ready.modulus⟩, h.1⟩) (fun _ _ h => h))
    (fun _ _ h => h.1)).wp
    (fun s t h => ⟨yWp s h.2.1, yWp t h.2.2⟩)
  have encoded := (ct.op_ct 5 1 4 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) op4).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ (ExpInitReady base len w s ∧ Q s) ∧ (ExpInitReady base len w t ∧ Q t))
    (fun _ _ h => ⟨⟨h.2.1.1.ready, h.2.1.2, h.2.1.1.r2bound⟩, ⟨h.2.2.1.ready, h.2.2.2, h.2.2.1.r2bound⟩, h.1⟩)
    (fun _ _ h => h)
  unfold expInitWith
  exact init.seq (y.seq encoded)

theorem expPhase_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb : List Byte}
    (K : TwoExp.Montgomery base len w Q regions) (ct : TwoExp.MontgomeryTiming K) (positive : 0 < eb.length)
    (sepR : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    RelCT isa (fun s t => (ExpPhaseInput ok base ep len w M1 x1 eb s ∧ Q s) ∧
      (ExpPhaseInput ok base ep len w M2 x2 eb t ∧ Q t) ∧ s.sp = t.sp) (expPhaseWith K.op) (fun _ _ => True) := by
  let P := fun (s t : State) => (ExpPhaseInput ok base ep len w M1 x1 eb s ∧ Q s) ∧
    (ExpPhaseInput ok base ep len w M2 x2 eb t ∧ Q t) ∧ s.sp = t.sp
  have wpInit (s : State) {M x : Nat} (h : ExpPhaseInput ok base ep len w M x eb s ∧ Q s) :
      WP isa (expInitWith K.op) s fun t => ExpByteState ok base ep len w M x eb 0 t ∧ Q t :=
    WP.mono (expPhase_init_ready s K h.1 h.2 sepR) (fun _ h => h.1)
  have init := (relCT_keep_sp ((expInitWith_ct K ct).mono (P' := P)
    (fun _ _ h => ⟨⟨⟨h.1.1.ready, by rw [h.1.1.modulus]; exact h.1.1.r2bound⟩, h.1.2⟩,
      ⟨⟨h.2.1.1.ready, by rw [h.2.1.1.modulus]; exact h.2.1.1.r2bound⟩, h.2.1.2⟩, h.2.2⟩) (fun _ _ h => h))
    (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wpInit s h.1, wpInit t h.2.1⟩)
  have wpBytes (s : State) {M x : Nat} (h : ExpByteState ok base ep len w M x eb 0 s ∧ Q s) :
      WP isa (expBytesWith K.op) s fun t => ExpState ok base len w M x (Spec.Rsa.os2ip eb) t ∧ Q t :=
    WP.mono (expPhase_bytes_ready s K h.1 h.2 positive sepR) (fun _ h => ⟨h.1, h.2.1⟩)
  have bytes := (relCT_keep_sp ((expBytes_ct (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) K ct positive sepR).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ (ExpByteState ok base ep len w M1 x1 eb 0 s ∧ Q s) ∧
      (ExpByteState ok base ep len w M2 x2 eb 0 t ∧ Q t))
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨wpBytes s h.2.1, wpBytes t h.2.2⟩)
  have finish := (exp_finish_ct (base := base) (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2)
    (E := Spec.Rsa.os2ip eb) ct).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ (ExpState ok base len w M1 x1 (Spec.Rsa.os2ip eb) s ∧ Q s) ∧
      (ExpState ok base len w M2 x2 (Spec.Rsa.os2ip eb) t ∧ Q t))
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)
  unfold expPhaseWith
  exact init.seq (bytes.seq finish)

end VG.Proof.Bignum.Arm.ConditionalExp
