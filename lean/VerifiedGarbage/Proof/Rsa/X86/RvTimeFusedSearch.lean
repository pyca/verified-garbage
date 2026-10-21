module

import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedCandidate
import VerifiedGarbage.Proof.Rsa.X86.RvFusedSearch
import VerifiedGarbage.Proof.Rsa.X86.RvTimeSearch
import VerifiedGarbage.Proof.Rsa.X86.RvTimeCheck
import VerifiedGarbage.Proof.Rsa.RecoverTries
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Rsa.X86.RvSearchState
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateData
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase

/-! The attempt count determines exactly when the fused search stops. -/
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
