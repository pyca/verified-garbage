import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoop
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (read_x)

/-- A paired invariant includes both public digit streams and a common field environment. -/
theorem jointLoop_relCT {c : Joint.Cfg} {o : Joint.Ops}
    (R : Nat → State → State → Prop)
    (counter : ∀ j s t, R j s t → s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
    (step : ∀ j, j<256 → RelCT isa (R (j+1)) (Joint.step c o) (R j)) :
    RelCT isa (R 256) (.loop (Joint.step c o) (.nonzero .x .x19)) (R 0) := by
  let I := fun j s t => 1≤j ∧ j≤256 ∧ R j s t
  have hs : ∀ j, RelCT isa (I j) (Joint.step c o) (fun s t =>
      eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s=some false → R 0 s t) ∧
      (eval (.nonzero .x .x19) s=some true → ∃ n<j,I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj256 : j≤256
      · refine (step (j-1) (by omega)).mono
          (P':=I j) (fun _ _ h => by simpa only [Nat.sub_add_cancel hj] using h.2.2) ?_
        intro s t hp
        obtain ⟨s19,t19⟩ := counter (j-1) s t hp
        refine ⟨by simp only [eval,State.read,s19,t19],fun he => ?_,fun he => ?_⟩
        · have hz : j-1=0 := by
            by_contra hn
            have hb : (BitVec.ofNat 64 (j-1) != 0)=true := by
              rw [bne_iff_ne]
              intro hh
              have hh' := congrArg BitVec.toNat hh
              simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j-1<2^64)] at hh'
              exact hn hh'
            have htrue : eval (.nonzero .x .x19) s=some true := by
              change some (s.read .x .x19 != 0)=some true
              rw [read_x,s19,hb]
            rw [htrue] at he; cases he
          exact hz ▸ hp
        · have hz : j-1≠0 := by
            intro hz; simp only [eval,State.read,s19,hz] at he; cases he
          exact ⟨j-1,by omega,by omega,by omega,hp⟩
      · exact RelCT.of_false (fun _ _ h => hj256 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  exact (RelCT.loop I hs 256).mono (fun _ _ h => ⟨by decide,by decide,h⟩) (fun _ _ h => h)

theorem jointRun_relCT {c : Joint.Cfg} {o : Joint.Ops}
    {Pre : State → State → Prop} (R : Nat → State → State → Prop)
    (counter : ∀ j s t, R j s t → s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
    (seed : RelCT isa Pre (Joint.digits c o) (R 256))
    (step : ∀ j, j<256 → RelCT isa (R (j+1)) (Joint.step c o) (R j)) :
    RelCT isa Pre (Joint.run c o) (R 0) :=
  RelCT.seq seed (jointLoop_relCT R counter step)

end VG.Proof.Weierstrass.AArch64
