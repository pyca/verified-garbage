import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretMath
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.KeyGen (Small seedS bmax)

theorem small_toRq_inj {η : Nat} (hη : η≤4) {a b : IPoly}
    (ha : Small η a) (hb : Small η b) (he : toRq a=toRq b) : a=b := by
  have ea:=VG.Proof.MlDsa.KeyGen.modPm_toRq (f := a) (fun c hc=>by have:=ha c hc; omega)
  have eb:=VG.Proof.MlDsa.KeyGen.modPm_toRq (f := b) (fun c hc=>by have:=hb c hc; omega)
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
          have he : r+(j-r)=j := by omega
          have hh:=VG.Proof.MlDsa.KeyGen.rejBoundedPoly_mono
            (VG.Proof.MlDsa.KeyGen.Bounds.le_max_right C B).rejBounded (hB (j-r) (by omega))
          simpa only [he] using hh
        · rw [ite_eq_right (fun hh=>h hh.1)]
          exact VG.Proof.MlDsa.KeyGen.rejBoundedPoly_mono
            (VG.Proof.MlDsa.KeyGen.Bounds.le_max_left C B).rejBounded (hS j (by omega))
    · exact Or.inr ⟨by rw [ite_eq_right (by simp [hv])],hfail⟩
  · exact Or.inr ⟨by rw [ite_eq_right (by simp [hret])],
      VG.Proof.MlDsa.KeyGen.keyGenInternal_none_S (by omega) hfail⟩


/-- The fourth tail lane repeats lane zero; ordinary groups use all four. -/
def secretLane (n i : Nat) : Nat := if i<n then i else 0

theorem secretLane_lt {n i : Nat} (hn : n=3∨n=4) : secretLane n i<n := by
  unfold secretLane
  split <;> omega

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
    have hh:=(boundedFour_some_iff p.η B.rejBounded m seed out).mp hB i (by omega)
    rw [hseed i (by omega),secretLane,ite_eq_left hi] at hh
    obtain ⟨x,hx,he⟩:=Option.map_eq_some_iff.mp hh
    have ex : x=fresh i := small_toRq_inj hη
      (VG.Proof.MlDsa.KeyGen.rejBoundedPoly_range hx) (hsmall i hi) (he.trans (hpoly i hi).symm)
    simpa only [ex] using hx
  · obtain ⟨i,hi,hfail⟩:=(boundedFour_none_iff p.η minBounds.rejBounded m seed).mp hB
    rw [hseed i hi] at hfail
    exact Or.inr ⟨hret,secretLane n i,secretLane_lt hn,hfail⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
