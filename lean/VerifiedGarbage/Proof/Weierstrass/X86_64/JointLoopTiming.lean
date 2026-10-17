module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline

/-! Paired countdown loops use the final `test rbx, rbx` in each step. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64

theorem joint_top_peel {c : Joint.Cfg} (h : c.peel=true) : Joint.top c=64*c.K.M.n := by
  simp only [Joint.top,h,ite_true]

theorem joint_top_guard {c : Joint.Cfg} (h : c.peel=false) : Joint.top c=64*c.K.M.n+1 := by
  simp only [Joint.top,h,Bool.false_eq_true,ite_false]

theorem joint_top_le (c : Joint.Cfg) : 64*c.K.M.n≤Joint.top c ∧ Joint.top c≤64*c.K.M.n+1 := by
  unfold Joint.top; split <;> omega

theorem jointLoop_relCT {c : Joint.Cfg} {double : Prog isa} (hn : 0<c.K.M.n)
    (R : Nat → State → State → Prop)
    (step : ∀ j,j<Joint.top c → RelCT isa (R (j+1)) (Joint.step c double).inline (fun s t =>
      R j s t ∧ s.zf=some (decide (j=0)) ∧ t.zf=some (decide (j=0)))) :
    RelCT isa (R (Joint.top c)) (Code.loop (Joint.step c double) .ne).inline (R 0) := by
  have ht := joint_top_le c
  let I := fun j s t => 1≤j ∧ j≤Joint.top c ∧ R j s t
  have hs : ∀ j,RelCT isa (I j) (Joint.step c double).inline (fun s t =>
      eval .ne s=eval .ne t ∧ (eval .ne s=some false → R 0 s t) ∧
      (eval .ne s=some true → ∃ n<j,I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hb : j≤Joint.top c
      · refine (step (j-1) (by omega)).mono
          (P':=I j) (fun _ _ h => by simpa only [Nat.sub_add_cancel hj] using h.2.2) ?_
        intro s t ⟨hp,sz,tz⟩
        have se : eval .ne s=some (!decide (j-1=0)) := by change s.zf.map (!·)=_; rw [sz]; rfl
        have te : eval .ne t=some (!decide (j-1=0)) := by change t.zf.map (!·)=_; rw [tz]; rfl
        refine ⟨se.trans te.symm,?_,?_⟩
        · intro he
          have hz : j-1=0 := by
            by_contra hz
            simp only [se,hz,decide_false,Bool.not_false] at he
            cases he
          exact hz ▸ hp
        · intro he
          have hz : j-1≠0 := by
            intro hz
            simp only [se,hz,decide_true,Bool.not_true] at he
            cases he
          exact ⟨j-1,by omega,by omega,by omega,hp⟩
      · exact RelCT.of_false (fun _ _ h => hb h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  exact (RelCT.loop I hs (Joint.top c)).mono (fun _ _ h => ⟨by omega,by omega,h⟩) (fun _ _ h => h)

/-- The loop, after the top digit's copy if `peel`. -/
theorem jointRun_relCT {c : Joint.Cfg} {double : Prog isa} (hn : 0<c.K.M.n)
    {Pre : State → State → Prop} (R : Nat → State → State → Prop)
    (seed : c.peel=true → RelCT isa Pre (Joint.digits c).inline (R (Joint.top c)))
    (pre : c.peel=false → ∀ s t,Pre s t → R (Joint.top c) s t)
    (step : ∀ j,j<Joint.top c → RelCT isa (R (j+1)) (Joint.step c double).inline (fun s t =>
      R j s t ∧ s.zf=some (decide (j=0)) ∧ t.zf=some (decide (j=0)))) :
    RelCT isa Pre (Joint.run c double).inline (R 0) := by
  rw [Joint.run]
  split
  · rename_i hp
    exact RelCT.seq (seed hp) (jointLoop_relCT hn R step)
  · rename_i hp
    exact (jointLoop_relCT hn R step).mono (pre (by simpa using hp)) (fun _ _ h => h)

end VG.Proof.Weierstrass.X86_64
