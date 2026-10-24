module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Step
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The complete fixed public row schedule reconstructs the unrevealed scalar. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)
open VG.Spec.Rsa.FixedBaseComb (rows exponent)
open VG.Proof.Rsa.FixedBaseComb (high high_step high_top high_zero rows_pos rows_small)

theorem comb_loop (M : Mont) {p : Parameters} {bs : List Byte} {s : State}
 (start : Running p bs 0 (rows p.N) s) (positive : 0<p.N) (width : p.N≤8192)
 (size : bs.length<2^31) (widthBound : p.N≤8*bs.length) (bound : Spec.Rsa.os2ip bs<2^p.N) :
 WP isa (.loop (Comb.step M.mm) (.nonzero .x .x3)) s fun t =>
 Running p bs (Spec.Rsa.os2ip bs) 0 t ∧ StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t := by
 let x := Spec.Rsa.os2ip bs
 let d := rows p.N
 have dPositive : 0<d := rows_pos positive
 have dBound : d≤1639 := (rows_small width).1
 let I := fun n t => 0<n ∧ n≤d ∧ Running p bs (high p.N x n) n t ∧
  StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t
 refine WP.loop (M:=isa) I ?_ d s ?_
 · intro n t h
   obtain ⟨nPositive,nBound,run,stable,keep⟩ := h
   have eq : n=(n-1)+1 := by omega
   have rowBound : n-1<rows p.N := by change n-1<d;omega
   have input : Running p bs (high p.N x ((n-1)+1)) ((n-1)+1) t := by rw [←eq];exact run
   refine WP.mono (running_step M input size widthBound (by change n-1+5*d<2^63;omega) bound) ?_
   rintro u ⟨runU,stableU,indexU,keepU⟩
   have powerEq := high_step p.N x (n-1) rowBound
   rw [←powerEq] at runU
   have totalStable := stable.trans stableU
   have totalKeep : Keep mmRegs s u := (keep.trans keepU).mono (by simp)
   by_cases last : n=1
   · left
     refine ⟨?_,?_,totalStable,totalKeep⟩
     · rw [eval_nonzero,indexU]
       change some (BitVec.ofNat 64 (n-1) != 0#64)=some false
       subst n;decide
     · simpa only [last,Nat.sub_self,high_zero p.N x bound] using runU
   · right
     refine ⟨?_,n-1,by omega,by omega,by omega,runU,totalStable,totalKeep⟩
     rw [eval_nonzero,indexU]
     change some (BitVec.ofNat 64 (n-1) != 0#64)=some true
     rw [ofNat_nonzero (by omega : n-1<2^64),decide_eq_true (by omega : 0<n-1)]
 · refine ⟨dPositive,Nat.le_refl _,?_,StableHeader.refl _ _,Keep.refl _ _⟩
   simpa only [d,high_top] using start

end VG.Proof.Ffdh.AArch64.Cached
