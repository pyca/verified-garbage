module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.General
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved

/-! Every public length specialization uses the same caller contract and erasure proof. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous
open VG VG.AArch64 VG.AArch64.Scrub VG.Impl.Scrub.AArch64

def leafContract (extra : State → Prop) : Contract isa where
  pre s := Caller s ∧ Prepared.Powers s ∧ extra s
  post := result
  pub a b := onePub 3 a b ∧ a.dit=b.dit

theorem scrubLeaf {cl : Clear} {p : State → Prop} {code : Prog isa} {W : Nat}
    (sizes : 0<W ∧ W≤2640 ∧ W%16=0)
    (side : scrubSide code W 0 cl [] = true) (raw : Verified target code (leafContract p)) :
    VerifiedScrubbed target (scrubAll W 0 cl code) (leafContract p) 0 := by
  have hk : ScrubAllOk (leafContract p) W 0 := by
    refine ⟨fun s hs => Nat.le_trans sizes.2.1 hs.1.room,?_,fun _ _ hp => hp.1.2.2.2.2.2.2.2.2.1⟩
    intro s t u hs post mem _
    apply result_frame hs.1 sizes.2.1 post
    intro a ha
    exact mem a fun bad => ha _ (List.mem_singleton_self _) (by
      change (a-(s.sp-BitVec.ofNat 64 W)).toNat+1 ≤ W
      exact bad)
  obtain ⟨wf,kp,dit,rb⟩ := keeps_of_side side
  refine ⟨Verified.scrubAllOfV raw hk side,?_,fun ty _ h => by cases ty <;> cases h⟩
  simp only [scrubSide,Nat.ne_of_gt sizes.1,↓reduceIte,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at side
  refine noResidue_scrubAll wf kp raw ⟨sizes.1,by omega,sizes.2.2⟩ hk.sp side.1.1.1.1.1.2 dit ?_ rb
  intro _ _ _ n hn
  exact False.elim (List.not_mem_nil (of_decide_eq_true (List.all_eq_true.mp side.1.1.1.1.2 n hn)))

end VG.Proof.AesGcm.AArch64.Contiguous
