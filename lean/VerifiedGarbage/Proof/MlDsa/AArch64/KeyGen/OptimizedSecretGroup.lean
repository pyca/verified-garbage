import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCall
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretGood

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.KeyGen (Small)
open VG.Proof.MlDsa.AArch64.Optimized

/-- This form covers both four fresh lanes and the three-lane duplicated tail. -/
def groupCode (c : Impl.Sha3.AArch64.Callee) (p : Params) (r n : Nat) : Prog isa :=
 .seq (.block (secretSeedsCode (fun i=>r+secretLane n i))) <|
 .seq (callAt (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.boundedFourSymbol c p.η)
   (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler c.pairedSha3 true p.η)
   (BoundedFour.samplerArgs (sc 1408) (sP p r) (sc (oR4 p)))) (.block and24)

theorem secretPoly_add (s : State) (p : Params) (r i : Nat) :
    pa s (sP p r)+BitVec.ofNat 64 (1024*i)=pa s (sP p (r+i)) := by
  rw [sc_add]
  congr 2
  unfold oP
  omega

theorem group_ok (c : Impl.Sha3.AArch64.Callee) {p : Params} (hF : PFacts p)
    {S : Nat} {σ : State} (hp : kgPre p S σ) {r n : Nat} (hn : n=3∨n=4)
    (hr : r+n≤p.ℓ+p.k) {s : State} (h : KSamp p σ (p.k*p.ℓ) r s) :
    WP isa (groupCode c p r n) s (KSamp p σ (p.k*p.ℓ) (r+n)) := by
  classical
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have hη : p.η≤4 := by rcases hF.eta with h|h <;> omega
  unfold groupCode
  refine WP.seq (WP.mono (secretSeeds_ok hF hp (by omega)
    (fun i hi=>by have:=secretLane_lt (i := i) hn; omega) h) fun s1 h1=>?_)
  have L1:=h1.ks.k1.kc.lay hF hp
  refine WP.seq (WP.mono (boundedAt_layout hF L1 (by omega) c) fun s2 ⟨hP2,h24,hred,hsmall,hout⟩=>?_)
  have h2:=h1.ks.keep hF hp hP2 (by unfold k1Chk kcChk; lay)
    (fun k hk=>by lay) (fun k hk=>by lay) h24
  have L2:=h2.k1.kc.lay hF hp
  let fresh : Nat→IPoly := fun i=>if hi : i<n then
    (hsmall i (by omega)).choose else Vector.replicate 256 0
  have freshSpec : ∀i<n,toRq (fresh i)=polyAt s2.mem (pa s1 (sP p r)+BitVec.ofNat 64 (1024*i)) ∧
      Small p.η (fresh i) := by
    intro i hi
    dsimp only [fresh]
    rw [dite_eq_left hi]
    exact ⟨(hsmall i (by omega)).choose_spec.1.symm,(hsmall i (by omega)).choose_spec.2⟩
  have ho : GroupOutcome p σ r n fresh ((s2.gpr .x0).setWidth 32) :=
    groupOutcome_of_four hη hn (fun i hi=>by rw [sc_add]; exact h1.done i hi)
      (fun i hi=>(freshSpec i hi).2) (fun i hi=>(freshSpec i hi).1) hout
  refine WP.mono (and24_ok s2) fun t ⟨ht,hval⟩=>?_
  have hP3 : PPostB S s2 t [] := postB_of_keep ht.keep (by decide)
    (by rw [ht.mem]; exact Frame.refl _ _)
  obtain ⟨A,old,hA,hS,hG⟩:=h2.ex
  refine ⟨h2.k1.step hF hp hP3 (by unfold k1Chk kcChk; layd),A,secretUpdate r n old fresh,
    fun i hi=>L2.keepPoly hP3 (by layd) (hA i hi),fun i hi=>?_,?_⟩
  · unfold secretUpdate
    by_cases hir : r≤i
    · rw [ite_eq_left ⟨hir,hi⟩]
      have hei : r+(i-r)=i := by omega
      have hp' := freshSpec (i-r) (by omega)
      refine ⟨⟨?_,?_⟩,hp'.2⟩
      · rw [ht.mem,sc_pa hP3,sc_pa hP2]
        simpa only [secretPoly_add,hei] using hred (i-r) (by omega)
      · rw [ht.mem,sc_pa hP3,sc_pa hP2]
        simpa only [secretPoly_add,hei] using hp'.1.symm
    · rw [ite_eq_right (fun hh=>hir hh.1)]
      exact ⟨L2.keepPoly hP3 (by lay) (hS i (by omega)).1,(hS i (by omega)).2⟩
  · rw [hval,VG.Proof.MlDsa.KeyGen.and01 (good_01 hG)
      (VG.Proof.MlDsa.KeyGen.outcome_01 hout)]
    exact good_group hr hG ho

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
