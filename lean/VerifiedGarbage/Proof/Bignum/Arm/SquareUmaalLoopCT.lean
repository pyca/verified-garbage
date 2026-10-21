module

public import VerifiedGarbage.Impl.Bignum.Arm.SquareUmaal
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.MacUmaal
import VerifiedGarbage.Proof.Bignum.Arm.SquareDiag
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Impl.Bignum.Arm.SquareUmaal
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! The diagonal loop leaks only its public pointers and positive word count. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (ofNat_beq_zero)

private def pubRegs : List Reg := [.r0, .r12, .lr]
private def DiagPublic (s t : State) : Prop := ∀ r ∈ pubRegs, s.gpr r = t.gpr r

private theorem keepRegs {code : Prog isa}
    (keep : ∀ r ∈ pubRegs, (instrs code).all (fun i => !(VG.Arm.clobbers i r)) = true)
    (noCalls : code.noCalls = true) {s t : State} {tr : List Leak} (run : Exec isa code s tr t)
    (r : Reg) (hr : r ∈ pubRegs) : t.gpr r = s.gpr r := by
  apply Exec.gpr (h := run) (hn := Or.inl noCalls)
  intro i hi
  have item := List.all_eq_true.mp (keep r hr) i hi
  cases hc : VG.Arm.clobbers i r <;> simp_all

private theorem keepPublic {code : Prog isa}
    (keep : ∀ r ∈ pubRegs, (instrs code).all (fun i => !(VG.Arm.clobbers i r)) = true)
    (noCalls : code.noCalls = true)
    (ct : RelCT isa DiagPublic code (fun _ _ => True)) : RelCT isa DiagPublic code DiagPublic := by
  intro s t tr1 tr2 u v h e1 e2
  refine ⟨(ct _ _ _ _ _ _ h e1 e2).1, ?_⟩
  intro r hr
  rw [keepRegs keep noCalls e1 r hr, keepRegs keep noCalls e2 r hr]
  exact h r hr

private theorem squareMacU_ct : ConstantTime isa (fun _ => True) (fun _ _ => True) (.block squareMacU) := by
  refine ConstantTime.of_silent fun s tr t _ h => ?_
  rw [Exec.block_iff] at h
  cases h
  rfl

private theorem diagStepU_public : RelCT isa DiagPublic diagStepU DiagPublic := by
  unfold diagStepU
  apply RelCT.seq
  · apply keepPublic (by decide +kernel) rfl
    apply RelCT.taint (A := taint) (Taint.ofRegs pubRegs) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs h
  apply RelCT.seq
  · apply keepPublic (by decide +kernel) rfl
    intro s t tr1 tr2 u v _ e1 e2
    exact ⟨squareMacU_ct s t tr1 tr2 u v trivial trivial trivial e1 e2, trivial⟩
  · apply keepPublic (by decide +kernel) rfl
    apply RelCT.taint (A := taint) (Taint.ofRegs pubRegs) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs h

private theorem diagAdvance_public : RelCT isa DiagPublic (.block diagAdvance) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs pubRegs) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs h

private theorem diagAdvance_post {s t : State} {tr : List Leak}
    (run : Exec isa (.block diagAdvance) s tr t) :
    t.gpr .r0 = s.gpr .r0 + 8 ∧ t.gpr .r12 = s.gpr .r12 + 4 ∧ t.gpr .lr = s.gpr .lr - 1 ∧
      t.z = (s.gpr .lr - 1 == 0) := by
  obtain ⟨tr', u, e, q⟩ := diagAdvance_ok s
  obtain ⟨_, rfl⟩ := Exec.det run e
  exact ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1⟩

theorem diagLoopU_ct {n : Nat} (positive : 0 < n) (fit : n < 2 ^ 32) :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12 ∧
      s.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .lr = BitVec.ofNat 32 n) diagLoopU (fun _ _ => True) := by
  let I := fun k s t => 0 < k ∧ k < 2 ^ 32 ∧ DiagPublic s t ∧
    s.gpr .lr = BitVec.ofNat 32 k ∧ t.gpr .lr = BitVec.ofNat 32 k
  have loop : RelCT isa (I n) diagLoopU (fun _ _ => True) := by
    unfold diagLoopU
    refine RelCT.loop (M := isa) I (fun k => ?_) n
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨pos, bound, pub, countS, countT⟩ := h
    cases e1 with
    | seq a1 b1 =>
      cases e2 with
      | seq a2 b2 =>
        obtain ⟨eq1, pubMid⟩ := diagStepU_public _ _ _ _ _ _ pub a1 a2
        obtain ⟨eq2, _⟩ := diagAdvance_public _ _ _ _ _ _ pubMid b1 b2
        have postU := diagAdvance_post b1
        have postV := diagAdvance_post b2
        have subCount : BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
          change BitVec.ofNat 32 k - BitVec.ofNat 32 1 = _
          exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
        have countU : u.gpr .lr = BitVec.ofNat 32 (k - 1) := by
          rw [postU.2.2.1, keepRegs (code := diagStepU) (by decide +kernel) rfl a1 .lr (by simp [pubRegs]), countS,
            subCount]
        have countV : v.gpr .lr = BitVec.ofNat 32 (k - 1) := by
          rw [postV.2.2.1, keepRegs (code := diagStepU) (by decide +kernel) rfl a2 .lr (by simp [pubRegs]), countT,
            subCount]
        have zeroU : u.z = decide (k = 1) := by
          rw [postU.2.2.2, keepRegs (code := diagStepU) (by decide +kernel) rfl a1 .lr (by simp [pubRegs]), countS,
            subCount, ofNat_beq_zero (by omega)]
          simp only [show k - 1 = 0 ↔ k = 1 by omega]
        have zeroV : v.z = decide (k = 1) := by
          rw [postV.2.2.2, keepRegs (code := diagStepU) (by decide +kernel) rfl a2 .lr (by simp [pubRegs]), countT,
            subCount, ofNat_beq_zero (by omega)]
          simp only [show k - 1 = 0 ↔ k = 1 by omega]
        refine ⟨by rw [eq1, eq2], ?_, fun _ => trivial, ?_⟩
        · change some (!u.z) = some (!v.z)
          rw [zeroU, zeroV]
        · intro again
          have next : 1 < k := by
            change some (!u.z) = some true at again
            rw [zeroU] at again
            by_cases one : k = 1
            · simp only [one, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
            · omega
          refine ⟨k - 1, by omega, by omega, by omega, ?_, countU, countV⟩
          intro r hr
          simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [postU.1, postV.1, pubMid .r0 (by simp [pubRegs])]
          · rw [postU.2.1, postV.2.1, pubMid .r12 (by simp [pubRegs])]
          · rw [countU, countV]
  exact loop.mono (fun s t h => ⟨positive, fit, by
    intro r hr
    simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1.trans h.2.2.2.symm, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm
