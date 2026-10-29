module

public import VerifiedGarbage.Proof.Rsa.X86.RvSearchState
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateData
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase

import VerifiedGarbage.Proof.Rsa.X86.RvFusedSearch
import VerifiedGarbage.Proof.Rsa.X86.RvTimeSearch
import VerifiedGarbage.Proof.Rsa.X86.RvTimeCheck
import VerifiedGarbage.Proof.Rsa.RecoverTries
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedWindow
import VerifiedGarbage.Proof.Rsa.X86.RvFusedCandidate
import VerifiedGarbage.Proof.Rsa.X86.RvFusedFinish
import VerifiedGarbage.Proof.Rsa.X86.RvFusedInit
import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedCheck
/-! The attempt count determines exactly when the fused search stops. -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvTimeFusedCandidate.lean`, which only this module imported.
section

/-! A fused candidate's trace is independent of the exponent and saved root. -/
section
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
  have eq1 := pub_trace pg alignStartCheck.choose_spec hs ht e1 f1
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
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (recoverPrimes splitTwos)

abbrev CandidateData.fusedTries {g : Geo} {n eLen dLen : Nat} (C : CandidateData g n eLen dLen) :=
  (recoverPrimes.go n (splitTwos (C.AW wR)).1 (splitTwos (C.AW wR)).2 100).2

def FusedSearchInvariant {g : Geo} {n eLen dLen : Nat}
    (C : CandidateData g n eLen dLen) (j : Nat) (s : State) : Prop :=
  CI g C.s0 C.A C.AW C.V j s ∧ j<C.fusedTries ∧
    recoverPrimes.go n (splitTwos (C.AW wR)).1 (splitTwos (C.AW wR)).2 100 =
    recoverPrimes.go n (splitTwos (C.AW wR)).1 (splitTwos (C.AW wR)).2 (100-j)

theorem fusedSearchBody_post {g : Geo} {n eLen dLen : Nat} (C : CandidateData g n eLen dLen)
    (modulus : C.A aN=n) (ep : 0<C.AW wR) (even : C.AW wR%2=0)
    {j : Nat} {s : State} (h : FusedSearchInvariant C j s) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedCand s fun t =>
      isa.eval .ne t=some (decide (j+1<C.fusedTries)) ∧
      (isa.eval .ne t=some true → FusedSearchInvariant C (j+1) t) := by
  have top := VG.Proof.Rsa.go_le n (splitTwos (C.AW wR)).1 (splitTwos (C.AW wR)).2 100 (by decide)
  change C.fusedTries≤100 at top
  have hj : j<100 := by have := h.2.1; omega
  refine WP.mono (fusedCand_index_ok C.value modulus C.zero C.bound C.inverse C.odd
    (by have := C.large; omega) C.one C.neg C.ae C.ad C.rb C.count C.limit C.wide h.1 hj)
    fun t ⟨z,zl,root,ht,zt⟩ => ?_
  have ref := VG.Proof.Rsa.Fused.eval_result n (j+2) (C.AW wR) (8*(dLen+eLen))
    (by have := C.large; omega) ep C.rb even
  have condition := VG.Proof.Rsa.cand_cond n (splitTwos (C.AW wR)).1 (splitTwos (C.AW wR)).2
    (show j<(recoverPrimes.go n (splitTwos (C.AW wR)).1 (splitTwos (C.AW wR)).2 Spec.Rsa.recoverTries).2 from h.2.1) h.2.2
  rw [←ref] at condition
  simp only [Bool.not_not,Spec.Rsa.recoverTries] at condition
  have flag : isa.eval .ne t=some (decide (j+1<C.fusedTries)) := by
    change t.zf.map (!·)=_
    rw [zt]
    simp only [Option.map_some,Bool.not_not]
    change some (decide (j+1<100) && !(VG.Proof.Rsa.Fused.eval n (j+2) (C.AW wR)).root.isSome) =
      some (decide (j+1<(recoverPrimes.go n (splitTwos (C.AW wR)).1 (splitTwos (C.AW wR)).2 100).2))
    exact congrArg some condition
  refine ⟨flag,?_⟩
  intro more
  have next : j+1<C.fusedTries := of_decide_eq_true (Option.some.inj (flag.symm.trans more))
  have continuing : (decide (j+1<100) && !(fusedModel n (C.AW wR) j).root.isSome)=true := by
    change (decide (j+1<100) && !(VG.Proof.Rsa.Fused.eval n (j+2) (C.AW wR)).root.isSome)=true
    rw [condition]
    exact decide_eq_true next
  have failed : (fusedModel n (C.AW wR) j).root=none := by
    cases found : (fusedModel n (C.AW wR) j).root with
    | none => rfl
    | some r => simp [found] at continuing
  refine ⟨ht.nextCandidate,next,?_⟩
  have step := VG.Proof.Rsa.go_eq n (splitTwos (C.AW wR)).1 (splitTwos (C.AW wR)).2 hj
  rw [←ref,failed] at step
  exact h.2.2.trans (by simpa only [Spec.Rsa.recoverTries] using step)

theorem fusedSearchLoop_relCT {g : Geo} (pg : PubG g) {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen)
    (modC : C.A aN=m) (modD : D.A aN=m)
    (epC : 0<C.AW wR) (epD : 0<D.AW wR) (evenC : C.AW wR%2=0) (evenD : D.AW wR%2=0)
    (tries : C.fusedTries=D.fusedTries) :
    RelCT isa (fun s t => CI g C.s0 C.A C.AW C.V 0 s ∧ CI g D.s0 D.A D.AW D.V 0 t)
      (.loop VG.Impl.Rsa.X86.RecoverRt.fusedCand .ne) (fun _ _ => True) := by
  have top := VG.Proof.Rsa.go_le m (splitTwos (C.AW wR)).1 (splitTwos (C.AW wR)).2 100 (by decide)
  change C.fusedTries ≤ 100 at top
  have low := VG.Proof.Rsa.go_ge1 m (splitTwos (C.AW wR)).1 (splitTwos (C.AW wR)).2 (k := 99) (by decide)
  change 1 ≤ C.fusedTries at low
  have loop := VG.RelCT.loop (M := isa) (body := VG.Impl.Rsa.X86.RecoverRt.fusedCand) (c := .ne)
    (Q := fun _ _ => True)
    (fun remaining s t => ∃ j, j + remaining = 100 ∧ 0 < remaining ∧
      FusedSearchInvariant C j s ∧ FusedSearchInvariant D j t)
    (fun remaining s t tr ur sf tf ⟨j, sum, pos, hs, ht⟩ es et => by
      have hj : j < 100 := by omega
      have trace := (fusedCand_relCT (C.atCandidate j hj) (D.atCandidate j hj) pg modC modD rfl
        _ _ _ _ _ _ ⟨hs.1, ht.1⟩ es et).1
      obtain ⟨cs, cn⟩ := wp_result (fusedSearchBody_post C modC epC evenC hs) es
      obtain ⟨ds, dn⟩ := wp_result (fusedSearchBody_post D modD epD evenD ht) et
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · rw [cs, ds, tries]
      · intro more
        have next : j + 1 < C.fusedTries := of_decide_eq_true (Option.some.inj (cs.symm.trans more))
        have moreD : isa.eval .ne tf = some true := ds.trans (by rw [← tries]; exact congrArg some (decide_eq_true next))
        exact ⟨remaining - 1, by omega, j + 1, by omega, by omega, cn more, dn moreD⟩) 100
  apply loop.mono
  · intro s t ⟨hs, ht⟩
    exact ⟨0, rfl, by decide, ⟨hs, by omega, rfl⟩, ⟨ht, by omega, rfl⟩⟩
  · intro s t h; exact h

theorem fusedLoop_relCT {g : Geo} (pg : PubG g) {n eLen dLen : Nat} (C D : CandidateData g n eLen dLen)
    (modC : C.A aN=n) (modD : D.A aN=n)
    (epC : 0<C.AW wR) (epD : 0<D.AW wR) (evenC : C.AW wR%2=0) (evenD : D.AW wR%2=0)
    (vcC : C.V sCnt=0) (vcD : D.V sCnt=0) (tries : C.fusedTries=D.fusedTries) :
    RelCT isa (fun s t =>
      KS g C.s0 C.A liveM C.AW [wR] C.V [sInv,sTc,sCnt] s ∧
      KS g D.s0 D.A liveM D.AW [wR] D.V [sInv,sTc,sCnt] t)
      VG.Impl.Rsa.X86.RecoverRt.fusedLoop (fun _ _ => True) :=
  VG.RelCT.seq (R := fun s t => CI g C.s0 C.A C.AW C.V 0 s ∧ CI g D.s0 D.A D.AW D.V 0 t)
    (pub_relCT pg candInitCheck (fun _ h => KS.stage h) (fun _ h => KS.stage h)
      (fun _ h => candInit_ok h vcC) (fun _ h => candInit_ok h vcD))
    (fusedSearchLoop_relCT pg C D modC modD epC epD evenC evenD tries)

end VG.Proof.Rsa.X86.Recover
