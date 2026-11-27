module

public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCall
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedSecrets
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCopy
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.BoundedFourContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretMath
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-! ### `MlDsa.AArch64.KeyGen.OptimizedSecretGroup`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.KeyGen.OptimizedSecretSeeds`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.KeyGen (seedS)
open VG.Spec.Sha3 (bytesAt)

structure SecretSeeds (p : Params) (σ : State) (r : Nat) (nonce : Nat→Nat) (j : Nat) (s : State) : Prop where
 ks : KSamp p σ (p.k*p.ℓ) r s
 done : ∀k<j,bytesAt s.mem (pa s (sc (1408+66*k))) 66=seedS (rho'Of p σ) (nonce k)

def secretSlotCode (j n : Nat) : Prog isa := .block
 (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretSeedCopy j ++
   setB (sc (1408+66*j+64)) n ++ setB (sc (1408+66*j+65)) 0)

theorem secretSlot_ok {p : Params} (hF : PFacts p) {S : Nat} {σ : State} (hp : kgPre p S σ)
    {r j : Nat} (hr : r≤p.ℓ+p.k) (hj : j<4) {nonce : Nat→Nat} (hn : nonce j<256)
    {s : State} (h : SecretSeeds p σ r nonce j s) :
    WP isa (secretSlotCode j (nonce j)) s (SecretSeeds p σ r nonce (j+1)) := by
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have L:=h.ks.k1.kc.lay hF hp
  unfold secretSlotCode
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (secretSeedCopy_ok hF L hj) fun s1 ⟨hP1,hk1,hb1⟩=>?_
  have h1:=h.ks.keep hF hp hP1 (by unfold k1Chk kcChk; layd)
    (fun k hk=>by layd) (fun k hk=>by layd) (hk1.get .x24)
  have L1:=h1.k1.kc.lay hF hp
  refine WP.mono (setTwo_ok L1 (o := 1408+66*j+64) (a := nonce j) (b := 0)
    (by omega_using [hj]) (by layd) (by layd)) fun t ⟨hP2,hk2,hb2⟩=>?_
  refine ⟨h1.keep hF hp hP2 (by unfold k1Chk kcChk; layd)
    (fun k hk=>by layd) (fun k hk=>by layd) (hk2.get .x24),fun k hk=>?_⟩
  by_cases he : k=j
  · subst k
    rw [VG.Proof.MlKem.bytesAt_add t.mem _ 64 2,L1.keepBytes hP2 (by layd),
      sc_pa hP2,sc_pa hP1,hb1,h.ks.k1.sb,
      sc_add,←sc_pa hP1,hb2,VG.Proof.MlDsa.KeyGen.seedS_eq _ hn]
    rfl
  · rw [L1.keepBytes hP2 (by layd),L.keepBytes hP1 (by layd)]
    exact h.done k (by omega_using [hk, he])


def secretSeedsCode (nonce : Nat→Nat) : List Instr :=
 (List.range 4).flatMap fun j=>VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretSeedCopy j ++
   setB (sc (1408+66*j+64)) (nonce j) ++ setB (sc (1408+66*j+65)) 0

theorem secretSeeds_ok {p : Params} (hF : PFacts p) {S : Nat} {σ : State} (hp : kgPre p S σ)
    {r : Nat} (hr : r≤p.ℓ+p.k) {nonce : Nat→Nat} (hn : ∀j<4,nonce j<256)
    {s : State} (h : KSamp p σ (p.k*p.ℓ) r s) :
    WP isa (.block (secretSeedsCode nonce)) s (SecretSeeds p σ r nonce 4) := by
  exact wp_range_flatMap (M := isa) (N := 4) (fun j t=>SecretSeeds p σ r nonce j t)
    (fun j t hj ht=>secretSlot_ok hF hp hr hj (hn j hj) ht) 4 (by omega_using []) s
    ⟨h,fun _ hi=>False.elim (Nat.not_lt_zero _ hi)⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end


-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedSecretGood.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.KeyGen (Small seedS bmax)

theorem small_toRq_inj {η : Nat} (hη : η≤4) {a b : IPoly}
    (ha : Small η a) (hb : Small η b) (he : toRq a=toRq b) : a=b := by
  have ea:=VG.Proof.MlDsa.KeyGen.modPm_toRq (f := a) (fun c hc=>by have:=ha c hc; omega_arith)
  have eb:=VG.Proof.MlDsa.KeyGen.modPm_toRq (f := b) (fun c hc=>by have:=hb c hc; omega_arith)
  rw [←ea,←eb,he]

def secretUpdate (r n : Nat) (old fresh : Nat→IPoly) (i : Nat) : IPoly :=
 if r≤i ∧ i<r+n then fresh (i-r) else old i

def GroupOutcome (p : Params) (σ : State) (r n : Nat) (fresh : Nat→IPoly) (ret : BitVec 32) : Prop :=
 (ret=1 ∧ ∃B : Bounds,∀i<n,rejBoundedPoly p.η B.rejBounded (seedS (rho'Of p σ) (r+i))=some (fresh i)) ∨
 (ret=0 ∧ ∃i<n,rejBoundedPoly p.η minBounds.rejBounded (seedS (rho'Of p σ) (r+i))=none)

theorem good_group {p : Params} {σ : State} {r n : Nat} (hr : r+n≤p.ℓ+p.k)
    {A : Nat→Poly} {old fresh : Nat→IPoly} {v : BitVec 64} {ret : BitVec 32}
    (hg : Good p σ (p.k*p.ℓ) r A old v) (ho : GroupOutcome p σ r n fresh ret) :
    Good p σ (p.k*p.ℓ) (r+n) A (secretUpdate r n old fresh)
      (if v=1 ∧ ret=1 then 1 else 0) := by
  rcases ho with ⟨hret,B,hB⟩|⟨hret,i,hi,hfail⟩
  · rcases hg with ⟨hv,C,hA,hS⟩|⟨hv,hfail⟩
    · refine Or.inl ⟨by rw [ite_eq_left ⟨hv,hret⟩],bmax C B,?_,?_⟩
      · intro j hj
        exact VG.Proof.MlDsa.KeyGen.rejNTTPoly_mono
          (VG.Proof.MlDsa.KeyGen.Bounds.le_max_left C B).rejNTT (hA j hj)
      · intro j hj
        unfold secretUpdate
        by_cases h : r≤j
        · rw [ite_eq_left ⟨h,hj⟩]
          have he : r+(j-r)=j := by omega_using [h]
          have hh:=VG.Proof.MlDsa.KeyGen.rejBoundedPoly_mono
            (VG.Proof.MlDsa.KeyGen.Bounds.le_max_right C B).rejBounded (hB (j-r) (by omega_using [hj, h]))
          simpa only [he] using hh
        · rw [ite_eq_right (fun hh=>h hh.1)]
          exact VG.Proof.MlDsa.KeyGen.rejBoundedPoly_mono
            (VG.Proof.MlDsa.KeyGen.Bounds.le_max_left C B).rejBounded (hS j (by omega_using [h]))
    · exact Or.inr ⟨by rw [ite_eq_right (by simp [hv])],hfail⟩
  · exact Or.inr ⟨by rw [ite_eq_right (by simp [hret])],
      VG.Proof.MlDsa.KeyGen.keyGenInternal_none_S (by omega_using [hr, hi]) hfail⟩


/-- The fourth tail lane repeats lane zero; ordinary groups use all four. -/
def secretLane (n i : Nat) : Nat := if i<n then i else 0

theorem secretLane_lt {n i : Nat} (hn : n=3∨n=4) : secretLane n i<n := by
  unfold secretLane
  split <;> omega_arith

theorem groupOutcome_of_four {p : Params} (hη : p.η≤4) {σ : State}
    {r n : Nat} (hn : n=3∨n=4) {m : Mem} {seed : Addr} {out : Nat→Poly}
    {fresh : Nat→IPoly} {ret : BitVec 32}
    (hseed : ∀i<4,Spec.Sha3.bytesAt m (seed+BitVec.ofNat 64 (66*i)) 66=
      seedS (rho'Of p σ) (r+secretLane n i))
    (hsmall : ∀i<n,Small p.η (fresh i)) (hpoly : ∀i<n,toRq (fresh i)=out i)
    (ho : Outcome (fun B=>(rejBoundedFour p.η B.rejBounded m seed).map (List.map toRq))
      ret ((List.range 4).map out)) : GroupOutcome p σ r n fresh ret := by
  rcases ho with ⟨hret,B,hB⟩|⟨hret,hB⟩
  · refine Or.inl ⟨hret,B,fun i hi=>?_⟩
    have hh:=(boundedFour_some_iff p.η B.rejBounded m seed out).mp hB i (by omega_using [hn, hi])
    rw [hseed i (by omega_using [hn, hi]),secretLane,ite_eq_left hi] at hh
    obtain ⟨x,hx,he⟩:=Option.map_eq_some_iff.mp hh
    have ex : x=fresh i := small_toRq_inj hη
      (VG.Proof.MlDsa.KeyGen.rejBoundedPoly_range hx) (hsmall i hi) (he.trans (hpoly i hi).symm)
    simpa only [ex] using hx
  · obtain ⟨i,hi,hfail⟩:=(boundedFour_none_iff p.η minBounds.rejBounded m seed).mp hB
    rw [hseed i hi] at hfail
    exact Or.inr ⟨hret,secretLane n i,secretLane_lt hn,hfail⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

@[expose] public section

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
  omega_using []

theorem group_ok (c : Impl.Sha3.AArch64.Callee) {p : Params} (hF : PFacts p)
    {S : Nat} {σ : State} (hp : kgPre p S σ) {r n : Nat} (hn : n=3∨n=4)
    (hr : r+n≤p.ℓ+p.k) {s : State} (h : KSamp p σ (p.k*p.ℓ) r s) :
    WP isa (groupCode c p r n) s (KSamp p σ (p.k*p.ℓ) (r+n)) := by
  classical
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have hη : p.η≤4 := by rcases hF.eta with h|h <;> omega_using [h]
  unfold groupCode
  refine WP.seq (WP.mono (secretSeeds_ok hF hp (by omega_using [hr])
    (fun i hi=>by have:=secretLane_lt (i := i) hn; omega_using [hr, hl, hk, this]) h) fun s1 h1=>?_)
  have L1:=h1.ks.k1.kc.lay hF hp
  refine WP.seq (WP.mono (boundedAt_layout hF L1 (by omega_using [hn, hr]) c) fun s2 ⟨hP2,h24,hred,hsmall,hout⟩=>?_)
  have h2:=h1.ks.keep hF hp hP2 (by unfold k1Chk kcChk; lay)
    (fun k hk=>by lay) (fun k hk=>by lay) h24
  have L2:=h2.k1.kc.lay hF hp
  let fresh : Nat→IPoly := fun i=>if hi : i<n then
    (hsmall i (by omega_using [hn, hi])).choose else Vector.replicate 256 0
  have freshSpec : ∀i<n,toRq (fresh i)=polyAt s2.mem (pa s1 (sP p r)+BitVec.ofNat 64 (1024*i)) ∧
      Small p.η (fresh i) := by
    intro i hi
    dsimp only [fresh]
    rw [dite_eq_left hi]
    exact ⟨(hsmall i (by omega_using [hn, hi])).choose_spec.1.symm,(hsmall i (by omega_using [hn, hi])).choose_spec.2⟩
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
      have hei : r+(i-r)=i := by omega_using [hir]
      have hp' := freshSpec (i-r) (by omega_using [hn, hi])
      refine ⟨⟨?_,?_⟩,hp'.2⟩
      · rw [ht.mem,sc_pa hP3,sc_pa hP2]
        simpa only [secretPoly_add,hei] using hred (i-r) (by omega_using [hn, hi])
      · rw [ht.mem,sc_pa hP3,sc_pa hP2]
        simpa only [secretPoly_add,hei] using hp'.1.symm
    · rw [ite_eq_right (fun hh=>hir hh.1)]
      exact ⟨L2.keepPoly hP3 (by lay) (hS i (by omega_using [hir])).1,(hS i (by omega_using [hir])).2⟩
  · rw [hval,VG.Proof.MlDsa.KeyGen.and01 (good_01 hG)
      (VG.Proof.MlDsa.KeyGen.outcome_01 hout)]
    exact good_group hr hG ho

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.Optimized

theorem secretSeeds_taint (nonce : Nat→Nat) : ∃h,
    (taint.check (Taint.ofRegs [.x28]) (.block (secretSeedsCode nonce)) h).isSome=true :=
  ⟨.block [],by with_unfolding_all rfl⟩

theorem secretSeeds_tr {p : Params} (hF : PFacts p) {S r : Nat} (nonce : Nat→Nat) :
    RelCT isa (R p S (KSamp p · (p.k*p.ℓ) r)) (.block (secretSeedsCode nonce)) (fun _ _=>True) := by
  obtain ⟨_,hc⟩:=secretSeeds_taint nonce
  exact rel_of (taintRel [.x28] (fun _ _ h=>Two.x28 h) hc)
    (fun _ _ _ _ hp hq pub hs ht=>kc_two hF hp hq pub hs.k1.kc ht.k1.kc)

theorem seeds_leak {p : Params} {S r n : Nat} (hn : n=3∨n=4) (hr : r+n≤p.ℓ+p.k)
    {σ τ s t : State} (pub : kgPub p S σ τ)
    (hs : SecretSeeds p σ r (fun i=>r+secretLane n i) 4 s)
    (ht : SecretSeeds p τ r (fun i=>r+secretLane n i) 4 t) :
    rejBoundedFourLeak p.η s.mem (pa s (sc 1408))=rejBoundedFourLeak p.η t.mem (pa t (sc 1408)) := by
  unfold rejBoundedFourLeak
  rw [List.flatMap_def,List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i hi
  have hi4:=List.mem_range.mp hi
  rw [sc_add,sc_add,hs.done i hi4,ht.done i hi4]
  exact rej_pub pub (by have:=secretLane_lt (i := i) hn; omega_using [hr, this])

theorem group_tr (c : Impl.Sha3.AArch64.Callee) {p : Params} (hF : PFacts p)
    {S r n : Nat} (hn : n=3∨n=4) (hr : r+n≤p.ℓ+p.k) :
    RelCT isa (R p S (KSamp p · (p.k*p.ℓ) r)) (groupCode c p r n) (fun _ _=>True) := by
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have hη : p.η=2∨p.η=4 := by rcases hF.eta with h|h; exact Or.inl h.1; exact Or.inr h.1
  unfold groupCode
  refine RelCT.seq (relInv
    (fun _ _ hp hs=>secretSeeds_ok hF hp (by omega_using [hr])
      (fun i hi=>by have:=secretLane_lt (i := i) hn; omega_using [hr, hl, hk, this]) hs)
    (secretSeeds_tr hF _)) ?_
  have hseed : inB (kgR++kgW p) (sc 1408) 264=true := by layd
  have hout : inB (kgR++kgW p) (sP p r) 4096=true := by lay
  have hwork : inB (kgR++kgW p) (sc (oR4 p)) 8192=true := by layd
  have hb0 := ptr_bs (kgOk p) hseed
  have hb1 := ptr_bs (kgOk p) hout
  have hb2 := ptr_bs (kgOk p) hwork
  refine RelCT.seq (BoundedFour.samplerAt_tr (S := S) c.pairedSha3 hη
    (ptr_ok (ptr_kept (kgOk p) hseed)) (ptr_ok (ptr_kept (kgOk p) hout))
    (ptr_ok (ptr_kept (kgOk p) hwork)) ?_) ?_
  · intro s t ⟨σ,τ,hp,hq,pub,hs,ht⟩
    have H:=kc_two hF hp hq pub hs.ks.k1.kc ht.ks.k1.kc
    exact ⟨boundedReady hF H.lx (by omega_using [hn, hr]),boundedReady hF H.ly (by omega_using [hn, hr]),
      H.same.pa hb0,H.same.pa hb1,H.same.pa hb2,H.same.2,seeds_leak hn hr pub hs ht⟩
  · exact block_nomem_tr (fun i hi _=>by
      simp only [and24,List.mem_singleton] at hi; subst i; rfl)

theorem group_piece (c : Impl.Sha3.AArch64.Callee) {p : Params} (hF : PFacts p)
    {S r n : Nat} (hn : n=3∨n=4) (hr : r+n≤p.ℓ+p.k) :
    Piece p S (KSamp p · (p.k*p.ℓ) r) (KSamp p · (p.k*p.ℓ) (r+n)) (groupCode c p r n) :=
  ⟨fun _ _ hp hs=>group_ok c hF hp hn hr hs,group_tr c hF hn hr⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
