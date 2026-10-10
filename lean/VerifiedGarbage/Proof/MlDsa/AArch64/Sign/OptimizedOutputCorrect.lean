import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.LazyInv
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedOutput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputPack

/-! ## From `OptimizedCanonicalize.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- Accepted norm bounds supply the strictly centered conversion precondition. -/
theorem centered_of_signed {m : Mem} {p : Addr} {f : Poly} {lo hi : Int}
    (h : SignedPolyIs m p f lo hi) (hl : -(q:Int)<lo) (hh : hi<(q:Int)) :
    CenteredReduced m p := by
  intro i hn
  have := h.bound i hn
  omega

theorem value_of_signed {m : Mem} {p : Addr} {f : Poly} {lo hi : Int}
    (h : SignedPolyIs m p f lo hi) : signedPolyAt m p=f := by
  apply Vector.ext
  intro i hi
  simp only [signedPolyAt,Vector.getElem_ofFn]
  simpa only [getElem!_pos f i hi] using h.value i hi

/-- Convert an accepted signed polynomial in its existing writable slot;
all surrounding signer state is retained by the call frame. -/
theorem canonicalizeAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {p : Ptr} {f : Poly} {lo hi : Int}
    (hr : inB (rbs++wbs) p 1024=true) (hw : inB wbs p 1024=true)
    (hf : SignedPolyIs s.mem (pa s p) f lo hi) (hl : -(q:Int)<lo) (hh : hi<(q:Int)) :
    WP isa (callAt "vg_mldsa_canonicalize_signed"
      VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize (Response.canonicalizeArgs p)) s fun t =>
      PPostB S s t [(p,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧ PolyIs t.mem (pa s p) f := by
  refine WP.mono (Response.canonicalizeAt_ok L.s64 (ptr_ok (L.ptrBs hr)) (L.nwp hr)
    (centered_of_signed hf hl hh) (L.cR hr) (L.cW hw)) fun t ⟨hp,hv⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),by simpa only [value_of_signed hf] using hv⟩

open VG.Impl.MlDsa.AArch64.Sign

def canonicalizeZChk (p : Params) (r : Nat) : Bool :=
  inB (sgR p++sgW p) (yP p r) 1024 && inB (sgW p) (yP p r) 1024 &&
  stChk p [(yP p r,1024)]

theorem canonicalizeZChk_ok {p : Params} (hp : Ok3 p) :
    ∀r<p.ℓ,canonicalizeZChk p r=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

theorem canonicalizeZ_rooted {p : Params} {S : Nat} {σ s : State} {r : Nat} {f : Poly}
    {lo hi : Int} (hc : canonicalizeZChk p r=true) (hs : RootedSt p S σ s)
    (hf : SignedPolyIs s.mem (pa s (yP p r)) f lo hi)
    (hl : -(q:Int)<lo) (hh : hi<(q:Int)) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.canonicalizeZ p r) s fun t =>
      RootedSt p S σ t ∧ t.gpr .x24=s.gpr .x24 ∧ PolyIs t.mem (pa t (yP p r)) f := by
  simp only [canonicalizeZChk,Bool.and_eq_true] at hc
  obtain ⟨⟨hr,hw⟩,hst⟩ := hc
  refine WP.mono_syms (canonicalizeAt_layout hs.1.lay hr hw hf hl hh) fun t ⟨hp,h24,hv⟩ hy => ?_
  refine ⟨hs.step hp hy hst (by simpa using hw),h24,?_⟩
  rw [hp.pa (hs.1.lay.ptrBs hr)]
  exact hv

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedCanonicalizeVector.lean` -/

section

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

end

/-! ## From `OptimizedOutputCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc seqR)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.Sha3 (bytesAt)

def conversionOutputChk (p : Params) : Bool :=
  (List.range p.ℓ).all fun r =>
    keepB (sgR p) (sgW p) [(yP p r,1024)] (sc oCT) (cLen p) &&
    famChk (sgR p) (sgW p) [(yP p r,1024)] 5 p.k

theorem conversionOutputChk_ok {p : Params} (hp : Ok3 p) : conversionOutputChk p=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

structure AcceptedConversion (p : Params) (S : Nat) (σ : State) (κ : Nat)
    (lo hi : Int) (done : Nat) (s : State) : Prop where
  z : CanonicalizeZState p S σ (Zv p σ κ) lo hi done s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p)=CTv p σ κ
  hints : HFam s 5 p.k (Hv p σ κ)

theorem acceptedConversion_step {p : Params} {S : Nat} {σ s : State} {κ r : Nat} {lo hi : Int}
    (hp : Ok3 p) (hr : r<p.ℓ) (hl : -(q:Int)<lo) (hh : hi<(q:Int))
    (h : AcceptedConversion p S σ κ lo hi r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.canonicalizeZ p r) s
      (AcceptedConversion p S σ κ lo hi (r+1)) := by
  have hc := conversionOutputChk_ok hp
  simp only [conversionOutputChk,List.all_eq_true,List.mem_range,Bool.and_eq_true] at hc
  refine WP.mono (canonicalizeZ_step_post hr (canonicalizeZChk_ok hp r hr)
    (canonicalizeZKeepChk_ok hp) hl hh h.z) fun t ⟨hz,hpost⟩ => ?_
  exact ⟨hz,(h.z.rooted.1.lay.keepBytes hpost (hc r hr).1).trans h.ct,
    HFam.keep h.z.rooted.1.lay hpost (hc r hr).2 h.hints⟩

/-- Accepted signed responses are converted once and packed to the exact
signature bytes of the passing iteration. -/
theorem optimizedOutput_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {σ s : State} {κ : Nat} {lo hi : Int}
    (h : AcceptedConversion p S σ κ lo hi 0 s)
    (hl : -(q:Int)<lo) (hh : hi<(q:Int)) (hpass : PassV p σ κ) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.output P p) s fun t =>
      St p S σ t ∧ bytesAt t.mem (pa t (.x23,0)) p.sigLen=sigV p σ κ ∧ t.gpr .x24=1 := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.output
  refine WP.seq (WP.mono (seqR_ok (I := fun r s => AcceptedConversion p S σ κ lo hi r s)
    p.ℓ 0 (fun r _ hr s h => acceptedConversion_step hp (by omega) hl hh h) s h)
    fun t ht => ?_)
  simp only [Nat.zero_add] at ht
  exact Output.output_ok hP (Output.oChk_ok hp) ht.z.rooted.1 ht.ct ht.z.converted ht.hints hpass ht.z.flag

end VG.Proof.MlDsa.AArch64.Sign

end
