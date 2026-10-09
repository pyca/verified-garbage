import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCanonicalize

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.Optimized

def canonicalizeZKeepChk (p : Params) : Bool :=
  (List.range p.ℓ).all fun r => (List.range p.ℓ).all fun j =>
    if j=r then true else keepB (sgR p) (sgW p) [(yP p r,1024)] (yP p j) 1024

theorem canonicalizeZKeepChk_ok {p : Params} (hp : Ok3 p) : canonicalizeZKeepChk p=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

theorem canonicalizeZ_keep {p : Params} (hc : canonicalizeZKeepChk p=true)
    {r j : Nat} (hr : r<p.ℓ) (hj : j<p.ℓ) (hne : j≠r) :
    keepB (sgR p) (sgW p) [(yP p r,1024)] (yP p j) 1024=true := by
  simp only [canonicalizeZKeepChk,List.all_eq_true,List.mem_range] at hc
  simpa only [ite_eq_right hne] using hc r hr j hj

structure CanonicalizeZState (p : Params) (S : Nat) (σ : State) (f : Nat → Poly)
    (lo hi : Int) (done : Nat) (s : State) : Prop where
  rooted : RootedSt p S σ s
  converted : ∀j<done,PolyIs s.mem (pa s (yP p j)) (f j)
  pending : ∀j,done≤j → j<p.ℓ → SignedPolyIs s.mem (pa s (yP p j)) (f j) lo hi
  flag : s.gpr .x24=1

theorem canonicalizeZ_step_post {p : Params} {S : Nat} {σ s : State} {f : Nat → Poly}
    {lo hi : Int} {r : Nat} (hr : r<p.ℓ)
    (hc : canonicalizeZChk p r=true) (hk : canonicalizeZKeepChk p=true)
    (hl : -(q:Int)<lo) (hh : hi<(q:Int))
    (h : CanonicalizeZState p S σ f lo hi r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.canonicalizeZ p r) s
      (fun t => CanonicalizeZState p S σ f lo hi (r+1) t ∧ PPostB S s t [(yP p r,1024)]) := by
  simp only [canonicalizeZChk,Bool.and_eq_true] at hc
  obtain ⟨⟨hread,hwrite⟩,hst⟩ := hc
  refine WP.mono_syms (canonicalizeAt_layout h.rooted.1.lay hread hwrite
    (h.pending r (by omega) hr) hl hh) fun t ⟨hp,h24,hval⟩ hy => ?_
  refine ⟨?_,hp⟩
  refine ⟨h.rooted.step hp hy hst (by simpa using hwrite),?_,?_,h24.trans h.flag⟩
  · intro j hj
    by_cases he : j=r
    · subst j
      rw [hp.pa (h.rooted.1.lay.ptrBs hread)]
      exact hval
    · exact h.rooted.1.lay.keepPoly hp (canonicalizeZ_keep hk hr (by omega) he)
        (h.converted j (by omega))
  · intro j hj hjl
    exact keepSignedPoly h.rooted.1.lay hp (canonicalizeZ_keep hk hr hjl (by omega))
      (h.pending j (by omega) hjl)

theorem canonicalizeZ_step {p : Params} {S : Nat} {σ s : State} {f : Nat → Poly}
    {lo hi : Int} {r : Nat} (hr : r<p.ℓ)
    (hc : canonicalizeZChk p r=true) (hk : canonicalizeZKeepChk p=true)
    (hl : -(q:Int)<lo) (hh : hi<(q:Int))
    (h : CanonicalizeZState p S σ f lo hi r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.canonicalizeZ p r) s
      (CanonicalizeZState p S σ f lo hi (r+1)) := by
  exact WP.mono (canonicalizeZ_step_post hr hc hk hl hh h) fun _ ht => ht.1

theorem canonicalizeZ_vector {p : Params} {S : Nat} {σ s : State} {f : Nat → Poly}
    {lo hi : Int} (hc : ∀r<p.ℓ,canonicalizeZChk p r=true)
    (hk : canonicalizeZKeepChk p=true) (hl : -(q:Int)<lo) (hh : hi<(q:Int))
    (h : CanonicalizeZState p S σ f lo hi 0 s) :
    WP isa (seqR (Impl.MlDsa.AArch64.Sign.Optimized.canonicalizeZ p) 0 p.ℓ) s
      (CanonicalizeZState p S σ f lo hi p.ℓ) := by
  simpa only [Nat.zero_add] using seqR_ok
    (I := fun r s => CanonicalizeZState p S σ f lo hi r s) p.ℓ 0
    (fun r _ hr s h => canonicalizeZ_step (by omega) (hc r (by omega)) hk hl hh h) s h

/-- The complete accepted response vector reaches the canonical representation
required by BitPack, with the acceptance flag and root tables intact. -/
theorem canonicalizeZ_all {p : Params} {S : Nat} {σ s : State} {f : Nat → Poly}
    {lo hi : Int} (hp : Ok3 p) (hs : RootedSt p S σ s)
    (hf : ∀j<p.ℓ,SignedPolyIs s.mem (pa s (yP p j)) (f j) lo hi)
    (hl : -(q:Int)<lo) (hh : hi<(q:Int)) (hflag : s.gpr .x24=1) :
    WP isa (seqR (Impl.MlDsa.AArch64.Sign.Optimized.canonicalizeZ p) 0 p.ℓ) s fun t =>
      RootedSt p S σ t ∧ Fam t (5+p.k) p.ℓ f ∧ t.gpr .x24=1 := by
  have hinit : CanonicalizeZState p S σ f lo hi 0 s :=
    ⟨hs,by intro j hj; omega,fun j _ hj => hf j hj,hflag⟩
  refine WP.mono (canonicalizeZ_vector (canonicalizeZChk_ok hp)
    (canonicalizeZKeepChk_ok hp) hl hh hinit) fun t ht => ?_
  exact ⟨ht.rooted,ht.converted,ht.flag⟩

end VG.Proof.MlDsa.AArch64.Sign
