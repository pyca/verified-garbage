module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BitMath
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs

/-! The public subtraction loop computes exactly ceil(N/5). -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem metadataRowStep (s : State) {L j : Nat} (positive : 5≤L) (fit : L<2^63)
 (remaining : s.gpr .x12=BitVec.ofNat 64 L) (count : s.gpr .x13=BitVec.ofNat 64 j) :
 WP isa (.block Policy.rowStep) s fun t =>
 (t.gpr .x12=BitVec.ofNat 64 (L-5) ∧ t.gpr .x13=BitVec.ofNat 64 (j+1) ∧
 t.gpr .x14=(if L-5<5 then 1#64 else 0#64) ∧ t.mem=s.mem) ∧ Keep [.x12,.x13,.x14] s t := by
 have sub : BitVec.ofNat 64 L-5#64=BitVec.ofNat 64 (L-5) :=
  BitVec.ofNat_sub_ofNat_of_le L 5 (by decide) positive
 refine WP.keep [.x12,.x13,.x14] ?_ rfl rfl rfl
 unfold Policy.rowStep
 brun [remaining,count,sub,sign_sub (a:=L-5) (b:=5) (by omega) (by decide)]
 constructor
 · exact (BitVec.ofNat_add _ _).symm
 · change ((BitVec.ofNat 64 (L-5)+ ~~~5#64+1#64) >>> 63)=_
   rw [BitVec.add_assoc,←BitVec.neg_eq_not_add,←BitVec.sub_eq_add_neg]
   exact sign_sub (by omega) (by decide)

theorem metadataRows_ok (s : State) {N : Nat} (positive : 0<N) (bound : N≤8192)
 (remaining : s.gpr .x12=BitVec.ofNat 64 (N+4)) (count : s.gpr .x13=0#64) :
 WP isa (.loop (.block Policy.rowStep) (.zero .x .x14)) s fun t =>
 t.gpr .x13=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N) ∧ t.mem=s.mem ∧ Keep [.x12,.x13,.x14] s t := by
 let d := (N+4)/5
 have dPositive : 0<d := by dsimp [d];omega
 let I := fun n t => ∃ j, n=d-j ∧ j<d ∧
  t.gpr .x12=BitVec.ofNat 64 (N+4-5*j) ∧ t.gpr .x13=BitVec.ofNat 64 j ∧
  t.mem=s.mem ∧ Keep [.x12,.x13,.x14] s t
 refine WP.loop (M:=isa) I ?_ d s ?_
 · intro n t h
   obtain ⟨j,rem,hj,left,countT,mem,keep⟩ := h
   have enough : 5≤N+4-5*j := by dsimp [d] at hj;omega
   refine WP.mono (metadataRowStep t enough (by omega) left countT) ?_
   rintro u ⟨⟨leftU,countU,flagU,memU⟩,keepU⟩
   have same : N+4-5*j-5=N+4-5*(j+1) := by omega
   have flag : (N+4-5*j-5<5) ↔ ¬j+1<d := by dsimp [d];omega
   by_cases more : j+1<d
   · right
     refine ⟨?_,d-(j+1),by omega,j+1,rfl,more,?_,countU,memU.trans mem,(keep.trans keepU).mono (by decide)⟩
     · rw [eval_zero,flagU,ite_eq_right (by rw [flag];exact not_not_intro more)]
       decide
     · rw [leftU,same]
   · left
     have last : j+1=d := by omega
     refine ⟨?_,?_,memU.trans mem,(keep.trans keepU).mono (by decide)⟩
     · rw [eval_zero,flagU,ite_eq_left (flag.mpr more)]
       decide
     · rw [countU,last]
       rfl
 · refine ⟨0,by omega,dPositive,?_,count,rfl,Keep.refl _ _⟩
   simpa using remaining

end VG.Proof.Ffdh.AArch64.Cached
