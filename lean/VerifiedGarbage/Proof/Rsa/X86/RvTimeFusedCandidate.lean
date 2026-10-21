module

import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedWindow
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedCandidate
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateData
import VerifiedGarbage.Proof.Rsa.X86.RvTimeCheck
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase
import VerifiedGarbage.Proof.Rsa.X86.RvFusedFinish
import VerifiedGarbage.Proof.Rsa.X86.RvFusedInit
import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedCheck

/-! A fused candidate's trace is independent of the exponent and saved root. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {n eLen dLen : Nat} (C D : CandidateData g n eLen dLen) (pg : PubG g)
include pg

theorem fusedCandStart_relCT :
    RelCT isa (fun s t => C.Start s ∧ D.Start t) fusedCandStart (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨hs,ht⟩ es et
  cases es with
  | @seq _ _ _ u3 _ _ _ e123 e4 =>
  cases et with
  | @seq _ _ _ v3 _ _ _ f123 f4 =>
  cases e123 with
  | @seq _ _ _ u2 _ _ _ e12 e3 =>
  cases f123 with
  | @seq _ _ _ v2 _ _ _ f12 f3 =>
  cases e12 with
  | @seq _ _ _ u1 _ _ _ e1 e2 =>
  cases f12 with
  | @seq _ _ _ v1 _ _ _ f1 f2 =>
  have eq1 := pub_trace pg alignStartCheck hs ht e1 f1
  have hu1 := wp_result (alignStart_ok hs C.zero C.candidate C.ae C.ad C.wide C.rb) e1
  have hv1 := wp_result (alignStart_ok ht D.zero D.candidate D.ae D.ad D.wide D.rb) f1
  have shifts : alignShifts g eLen dLen<2^32 := by
    have := geo_wide g hs.upper
    unfold alignShifts
    omega
  have eq2 := (fixedLoop_relCT (fun k s => C.Align k s) (fun k t => D.Align k t)
    (by unfold alignShifts; have := C.wide; omega)
    (fun _ _ _ _ _ _ _ _ ⟨h,j⟩ e f => ⟨pub_trace pg alignBodyCheck h j e f,trivial⟩)
    (fun _ _ hk h => alignBody_ok h hk shifts)
    (fun _ _ hk h => alignBody_ok h hk shifts)
    _ _ _ _ _ _ ⟨hu1,hv1⟩ e2 f2).1
  have hu2 := wp_result (alignLoop_ok hu1 (by unfold alignShifts; have := C.wide; omega) shifts) e2
  have hv2 := wp_result (alignLoop_ok hv1 (by unfold alignShifts; have := D.wide; omega) shifts) f2
  unfold AI at hu2 hv2
  rw [Nat.sub_self,upd_twice] at hu2 hv2
  have eq3 := pub_trace pg fusedInitCheck hu2 hv2 e3 f3
  have hu3 := wp_result (fusedInit_ok (n := n) hu2 (by have := C.large; omega) (by exact C.zero) (by exact C.one)) e3
  have hv3 := wp_result (fusedInit_ok (n := n) hv2 (by have := D.large; omega) (by exact D.zero) (by exact D.one)) f3
  have eq4 := hu3.trace pg windowCountCheck hv3 e4 f4
  exact ⟨by rw [eq1,eq2,eq3,eq4],trivial⟩

theorem fusedCand_relCT (modC : C.A aN=n) (modD : D.A aN=n) (cand : C.V sCand=D.V sCand) :
    RelCT isa (fun s t => C.Start s ∧ D.Start t) VG.Impl.Rsa.X86.RecoverRt.fusedCand
      (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedCand
  simp only [seqs]
  apply VG.RelCT.assoc
  apply VG.RelCT.assoc
  apply VG.RelCT.assoc
  refine VG.RelCT.seq (R := fun s t =>
    FWI g C.s0 C.A C.AW C.V n (alignedExp g (C.AW wR) eLen dLen) (2*(dLen+eLen)) 0 s ∧
    FWI g D.s0 D.A D.AW D.V n (alignedExp g (D.AW wR) eLen dLen) (2*(dLen+eLen)) 0 t)
    (stage_relCT
      (P' := FWI g C.s0 C.A C.AW C.V n (alignedExp g (C.AW wR) eLen dLen) (2*(dLen+eLen)) 0)
      (Q' := FWI g D.s0 D.A D.AW D.V n (alignedExp g (D.AW wR) eLen dLen) (2*(dLen+eLen)) 0)
      (fusedCandStart_relCT C D pg)
      (fun _ h => fusedCandStart_ok h C.zero (by have := C.large; omega) C.one C.candidate C.ae C.ad C.rb C.limit C.wide)
      (fun _ h => fusedCandStart_ok h D.zero (by have := D.large; omega) D.one D.candidate D.ae D.ad D.rb D.limit D.wide)) ?_
  refine VG.RelCT.seq (R := fun s t =>
    FWI g C.s0 C.A C.AW C.V n (alignedExp g (C.AW wR) eLen dLen) (2*(dLen+eLen)) (2*(dLen+eLen)) s ∧
    FWI g D.s0 D.A D.AW D.V n (alignedExp g (D.AW wR) eLen dLen) (2*(dLen+eLen)) (2*(dLen+eLen)) t)
    (fixedLoop_relCT (c := 2*(dLen+eLen))
      (fun k s => FWI g C.s0 C.A C.AW C.V n (alignedExp g (C.AW wR) eLen dLen) (2*(dLen+eLen)) k s)
      (fun k t => FWI g D.s0 D.A D.AW D.V n (alignedExp g (D.AW wR) eLen dLen) (2*(dLen+eLen)) k t)
      (by have := C.count; omega)
      (fun _ _ => fusedWindow_relCT pg C.value D.value modC modD C.zero D.zero C.bound C.inverse D.inverse
        C.odd (by have := C.large; omega) C.one D.one C.neg D.neg cand C.candidate)
      (fun _ _ hk h => fusedWindow_ok h C.value modC C.zero C.bound C.inverse C.odd
        (by have := C.large; omega) C.one C.neg C.candidate hk (by have := C.limit; omega))
      (fun _ _ hk h => fusedWindow_ok h D.value modD D.zero D.bound D.inverse D.odd
        (by have := D.large; omega) D.one D.neg D.candidate hk (by have := D.limit; omega))) ?_
  change RelCT isa (fun s t =>
    FWI g C.s0 C.A C.AW C.V n (alignedExp g (C.AW wR) eLen dLen) (2*(dLen+eLen)) (2*(dLen+eLen)) s ∧
    FWI g D.s0 D.A D.AW D.V n (alignedExp g (D.AW wR) eLen dLen) (2*(dLen+eLen)) (2*(dLen+eLen)) t)
    (.seq VG.Impl.Rsa.X86.RecoverRt.fusedFinish (.block candNext)) (fun _ _ => True)
  intro s t tr ur sf tf ⟨⟨w,hs⟩,⟨v,ht⟩⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
  cases et with
  | @seq _ _ _ v _ _ _ f1 f2 =>
  have eq1 := hs.trace pg fusedFinishCheck ht e1 f1
  obtain ⟨_,_,_,hu⟩ := wp_result (fusedFinish_ok hs (by change 2*(dLen+eLen)-2*(dLen+eLen)=0; omega)) e1
  obtain ⟨_,_,_,hv⟩ := wp_result (fusedFinish_ok ht (by change 2*(dLen+eLen)-2*(dLen+eLen)=0; omega)) f1
  exact ⟨by rw [eq1,pub_trace pg candNextCheck hu hv e2 f2],trivial⟩

end
end VG.Proof.Rsa.X86.Recover
