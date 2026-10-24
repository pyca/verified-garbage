module

public import VerifiedGarbage.Proof.Rsa.X86.RvFusedCandidate
public import VerifiedGarbage.Proof.Rsa.X86.RvSearchState

/-! The bounded candidate search using the fused pass. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (pqOf)
open VG.Spec.Rsa (recoverPrimes splitTwos)

def FusedSearchResult (g : Geo) (s0 : State) (A AW V : Nat → Nat) (n : Nat) (s : State) : Prop :=
  ∃ j st, j<100 ∧ SI g s0 A AW (VJ V (j+1)) n 0 0 st s ∧ st.1<n ∧
    (st.2.2=true → 1≤st.1) ∧
    ((if st.2.2 then some (pqOf n st.1) else none),j+1)=
      recoverPrimes.go n (splitTwos (AW wR)).1 (splitTwos (AW wR)).2 100

section
variable {g : Geo} {s0 : State} {A AW V : Nat → Nat} {n eLen dLen : Nat}
  (value : A mBase=n) (modulus : A aN=n) (zero : A aZ=0)
  (bound : n<2^(64*g.n)) (inverse : (n*V sInv+1)%2^32=0)
  (odd : n%2=1) (hn : 1<n) (one : A aO=2^(64*g.n)%n) (neg : A aNg=n-2^(64*g.n)%n)
  (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
  (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
  (ep : 0<AW wR) (even : AW wR%2=0) (rb : AW wR<2^(8*(dLen+eLen)))
  (lo : 0<8*(dLen+eLen)) (limit : 8*(dLen+eLen)≤16384) (wide : 8*(dLen+eLen)<32*g.W)

include value modulus zero bound inverse odd hn one neg ae ad ep even rb lo limit wide

 omit ep even in
 theorem fusedCand_index_ok {s : State} {j : Nat} (h : CI g s0 A AW V j s) (hj : j<100) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedCand s fun t =>
      let st := fusedModel n (AW wR) j
      ∃ z, z<n ∧ (∀ r,st.root=some r → z=r) ∧
        SI g s0 A AW (VJ V (j+1)) n 0 0 (z,st.done,st.root.isSome) t ∧
        t.zf=some (!(decide (j+1<100) && !st.root.isSome)) := by
  refine WP.mono (fusedCand_ok h value modulus zero bound (by exact inverse) odd hn one neg
    (by exact hj) ae ad rb lo limit wide) fun t result => ?_
  simpa only [VJ,upd_self,upd_twice] using result

 theorem fusedSearchLoop_ok {s : State} (h : CI g s0 A AW V 0 s) :
    WP isa (.loop VG.Impl.Rsa.X86.RecoverRt.fusedCand .ne) s (FusedSearchResult g s0 A AW V n) := by
  refine WP.loop (M := isa)
    (fun left u => ∃ j, j+left=100 ∧ 0<left ∧ CI g s0 A AW V j u ∧
      recoverPrimes.go n (splitTwos (AW wR)).1 (splitTwos (AW wR)).2 100 =
      recoverPrimes.go n (splitTwos (AW wR)).1 (splitTwos (AW wR)).2 (100-j))
    ?_ 100 s ⟨0,rfl,by decide,h,rfl⟩
  intro left u ⟨j,total,pos,hu,go⟩
  have hj : j<100 := by omega
  refine WP.mono (fusedCand_index_ok value modulus zero bound inverse odd hn one neg ae ad rb
    lo limit wide hu hj) fun t ⟨z,zl,root,hs,zt⟩ => ?_
  have ref := VG.Proof.Rsa.Fused.eval_result n (j+2) (AW wR) (8*(dLen+eLen)) hn ep rb even
  have step := go.trans (VG.Proof.Rsa.go_eq n (splitTwos (AW wR)).1 (splitTwos (AW wR)).2 hj)
  rw [←ref] at step
  cases found : (fusedModel n (AW wR) j).root with
  | some r =>
    have zr : z=r := root r found
    have square := VG.Proof.Rsa.recoverStep_some (ref.symm.trans found)
    have positive : 1≤z := by
      by_contra h
      have rz : r=0 := by omega
      simp only [rz,Nat.zero_mul,Nat.zero_mod] at square
      omega
    left
    refine ⟨?_,j,(z,(fusedModel n (AW wR) j).done,true),hj,?_,zl,(by intro _; exact positive),?_⟩
    · change t.zf.map (!·)=some false
      simp [zt,found]
    · simpa only [found,Option.isSome_some] using hs
    · simpa only [found,Option.isSome_some,ite_true,zr,pqOf] using step.symm
  | none =>
    have hs' : SI g s0 A AW (VJ V (j+1)) n 0 0 (z,(fusedModel n (AW wR) j).done,false) t := by
      simpa only [found,Option.isSome_none] using hs
    have stepNone : recoverPrimes.go n (splitTwos (AW wR)).1 (splitTwos (AW wR)).2 100 =
        recoverPrimes.go n (splitTwos (AW wR)).1 (splitTwos (AW wR)).2 (100-(j+1)) := by
      simpa only [found,Spec.Rsa.recoverTries] using step
    by_cases last : j+1=100
    · left
      refine ⟨?_,j,(z,(fusedModel n (AW wR) j).done,false),hj,hs',zl,(by intro h; cases h),?_⟩
      · change t.zf.map (!·)=some false
        simp [zt,found,last]
      · rw [last,Nat.sub_self] at stepNone
        change recoverPrimes.go n (splitTwos (AW wR)).1 (splitTwos (AW wR)).2 100=(none,100) at stepNone
        simpa only [last,Bool.false_eq_true,ite_false] using stepNone.symm
    · right
      refine ⟨?_,left-1,by omega,j+1,by omega,by omega,hs'.nextCandidate,?_⟩
      · change t.zf.map (!·)=some true
        simp [zt,found,show j+1<100 by omega]
      · exact stepNone

 theorem fusedLoop_ok {s : State}
    (h : KS g s0 A liveM AW [wR] V [sInv,sTc,sCnt] s) (vc : V sCnt=0) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedLoop s (FusedSearchResult g s0 A AW V n) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedLoop
  refine WP.seq (wp_movS rfl fun u U _ => ?_)
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine WP.mono (hu.storeSlot (d := sCand) (by decide) .eax) fun v ⟨hv,_,_⟩ => ?_
  rw [U.gpr] at hv
  have initial : CI g s0 A AW V 0 v := by
    refine hv.mono (fun j hj => ⟨hj,rfl⟩) (fun j hj => ⟨hj,rfl⟩) fun d hd => ⟨by revert d; decide,?_⟩
    simp only [slotsExp,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl <;> first | rfl | exact vc
  exact fusedSearchLoop_ok value modulus zero bound inverse odd hn one neg ae ad ep even rb lo limit wide initial

end
end VG.Proof.Rsa.X86.Recover
