import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Omega

/-! Paired countdown loops use the final `test rbx, rbx` in each step. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64

theorem jointLoop_relCT {c : Joint.Cfg} {double : Prog isa} (hn : 0<c.K.M.n)
    (R : Nat → State → State → Prop)
    (step : ∀ j,j<64*c.K.M.n → RelCT isa (R (j+1)) (Joint.step c double) (fun s t =>
      R j s t ∧ s.zf=some (decide (j=0)) ∧ t.zf=some (decide (j=0)))) :
    RelCT isa (R (64*c.K.M.n)) (.loop (Joint.step c double) .ne) (R 0) := by
  let I := fun j s t => 1≤j ∧ j≤64*c.K.M.n ∧ R j s t
  have hs : ∀ j,RelCT isa (I j) (Joint.step c double) (fun s t =>
      eval .ne s=eval .ne t ∧ (eval .ne s=some false → R 0 s t) ∧
      (eval .ne s=some true → ∃ n<j,I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hb : j≤64*c.K.M.n
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
  exact (RelCT.loop I hs (64*c.K.M.n)).mono (fun _ _ h => ⟨by omega,by omega,h⟩) (fun _ _ h => h)

theorem jointRun_relCT {c : Joint.Cfg} {double : Prog isa} (hn : 0<c.K.M.n)
    {Pre : State → State → Prop} (R : Nat → State → State → Prop)
    (seed : RelCT isa Pre (Joint.digits c) (R (64*c.K.M.n)))
    (step : ∀ j,j<64*c.K.M.n → RelCT isa (R (j+1)) (Joint.step c double) (fun s t =>
      R j s t ∧ s.zf=some (decide (j=0)) ∧ t.zf=some (decide (j=0)))) :
    RelCT isa Pre (Joint.run c double) (R 0) :=
  RelCT.seq seed (jointLoop_relCT hn R step)

end VG.Proof.Weierstrass.X86_64
