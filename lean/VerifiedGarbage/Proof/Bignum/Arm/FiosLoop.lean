module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Impl.Bignum.Arm.Fios
import VerifiedGarbage.Proof.Bignum.Arm.FiosPairInv
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The public pair count decreases to zero while the full quotient identity is preserved. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem loop_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n i : Nat}
    (ctx : Ctx s0 base size acc b mod n) (inv : Inv s0 x q base acc b mod n i s)
    (positive : i+1<n) (even : (n-(i+1))%2=0) :
    WP isa VG.Impl.Bignum.Arm.Fios.loop s (Inv s0 x q base acc b mod n (n-1)) := by
  let I := fun k t => ∃ j, j+1+2*k=n ∧ 0<k ∧ Inv s0 x q base acc b mod n j t
  unfold VG.Impl.Bignum.Arm.Fios.loop
  refine WP.loop (M:=isa) I ?_ ((n-(i+1))/2) s ?_
  · intro k t h
    obtain ⟨j,hjk,hk,hj⟩ := h
    refine WP.mono (pairBody_ok ctx hj (by omega)) ?_
    rintro u ⟨hu,hz⟩
    by_cases last : j+2+1=n
    · left
      refine ⟨?_,?_⟩
      · change some (!u.z)=some false
        simp only [hz,last,decide_true,Bool.not_true]
      · have index : j+2=n-1 := by omega
        simpa only [index] using hu
    · right
      refine ⟨?_,k-1,by omega,j+2,by omega,by omega,hu⟩
      change some (!u.z)=some true
      simp only [hz,last,decide_false,Bool.not_false]
  · exact ⟨i,by omega,by omega,inv⟩

end VG.Proof.Bignum.Arm.Fios
