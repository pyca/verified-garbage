import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductCallTiming
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedResponse
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChallenge
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopInit

/-! ## From `OptimizedProduct.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- The response-product call uses two positive NTT inputs and writes only
its result and the existing scratch slot. Static roots stay explicit. -/
theorem productReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {out a b scratch : Ptr}
    (ho : inB (rbs++wbs) out 1024=true) (ha : inB (rbs++wbs) a 1024=true)
    (hb : inB (rbs++wbs) b 1024=true) (hs : inB (rbs++wbs) scratch 1024=true)
    (hwo : inB wbs out 1024=true) (hws : inB wbs scratch 1024=true)
    (hoa : sepB rbs wbs out 1024 a 1024=true)
    (hob : sepB rbs wbs out 1024 b 1024=true)
    (hos : sepB rbs wbs out 1024 scratch 1024=true)
    (has : sepB rbs wbs a 1024 scratch 1024=true)
    (hbs : sepB rbs wbs b 1024 scratch 1024=true)
    (held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=
      VG.Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64)
    (hsep : ∀ r∈[Inverse.outputRegion (pa s out),Inverse.outputRegion (pa s scratch)],
      (Inverse.tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint r)
    (ht : Covers [Inverse.tableRegion (s.syms "VG_MLDSA_INV_FOLDED")] (s.rd++s.wr))
    (hpa : PositiveReduced s.mem (pa s a)) (hpb : PositiveReduced s.mem (pa s b)) :
    Inverse.ProductCallReady out a b scratch s := by
  refine ⟨L.nwp ho,L.nwp ha,L.nwp hb,L.nwp hs,held,hfit,hsep,
    L.disj hoa,L.disj hob,L.disj hos,L.disj has,L.disj hbs,hpa,hpb,?_,?_⟩
  · exact Covers.cons (L.cR ha) (Covers.cons (L.cR hb)
      (Covers.cons ht (Covers.cons (L.cR ho) (L.cR hs))))
  · exact Covers.cons (L.cW hwo) (L.cW hws)

/-- Fused challenge multiplication and inverse transform for z/r0/h. The
signed result is intentionally not coerced to the canonical PolyIs contract. -/
theorem productAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {out a b scratch : Ptr}
    (ho : inB (rbs++wbs) out 1024=true) (ha : inB (rbs++wbs) a 1024=true)
    (hb : inB (rbs++wbs) b 1024=true) (hs : inB (rbs++wbs) scratch 1024=true)
    (h : Inverse.ProductCallReady out a b scratch s) :
    WP isa (callAt "vg_mldsa_multiply_inverse_raw"
      (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true)
      (Inverse.productArgs out a b scratch)) s fun t =>
      PPostB S s t [(out,1024),(scratch,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      RawPolyIs t.mem (pa s out) (nttInv (multiplyNTT (polyAt s.mem (pa s a)) (polyAt s.mem (pa s b)))) := by
  refine WP.mono (Inverse.productAt_ok L.s64 (ptr_ok (L.ptrBs ho)) (ptr_ok (L.ptrBs ha))
    (ptr_ok (L.ptrBs hb)) (ptr_ok (L.ptrBs hs)) h) fun t ⟨hp,hv⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),hv⟩

/-- Field-valued response boundary for a transformed challenge and secret. -/
theorem productAt_field_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {out a b scratch : Ptr} {f g : Poly}
    (ho : inB (rbs++wbs) out 1024=true) (ha : inB (rbs++wbs) a 1024=true)
    (hb : inB (rbs++wbs) b 1024=true) (hs : inB (rbs++wbs) scratch 1024=true)
    (h : Inverse.ProductCallReady out a b scratch s)
    (hf : PosPolyIs s.mem (pa s a) f) (hg : PosPolyIs s.mem (pa s b) g) :
    WP isa (callAt "vg_mldsa_multiply_inverse_raw"
      (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true)
      (Inverse.productArgs out a b scratch)) s fun t =>
      PPostB S s t [(out,1024),(scratch,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      RawPolyIs t.mem (pa s out) (nttInv (multiplyNTT f g)) := by
  refine WP.mono (productAt_layout L ho ha hb hs h) fun t ⟨hp,h24,hv⟩ => ?_
  exact ⟨hp,h24,by simpa only [hf.value,hg.value] using hv⟩

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedResponseProduct.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

def responseProductChk (p : Params) (out secret : Ptr) : Bool :=
  inB (sgB p) out 1024 && inB (sgB p) cP 1024 && inB (sgB p) secret 1024 &&
  inB (sgB p) (sc oPS) 1024 && inB (sgW p) out 1024 && inB (sgW p) (sc oPS) 1024 &&
  sepB (sgR p) (sgW p) out 1024 cP 1024 && sepB (sgR p) (sgW p) out 1024 secret 1024 &&
  sepB (sgR p) (sgW p) out 1024 (sc oPS) 1024 &&
  sepB (sgR p) (sgW p) cP 1024 (sc oPS) 1024 &&
  sepB (sgR p) (sgW p) secret 1024 (sc oPS) 1024

theorem responseProductChk_z {p : Params} (hp : Ok3 p) :
    ∀r<p.ℓ,responseProductChk p t1P (s1P p r)=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem responseProductChk_r0 {p : Params} (hp : Ok3 p) :
    ∀r<p.k,responseProductChk p t1P (s2P p r)=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem responseProductChk_h {p : Params} (hp : Ok3 p) :
    ∀r<p.k,responseProductChk p t3P (t0P p r)=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem responseProductChk_hint {p : Params} (hp : Ok3 p) :
    ∀r<p.k,responseProductChk p t1P (t0P p r)=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem responseProduct_ok {p : Params} {S : Nat} {σ s : State} {out secret : Ptr} {f g : Poly}
    (hs : RootedSt p S σ s) (hc : responseProductChk p out secret=true)
    (hf : PosPolyIs s.mem (pa s cP) f) (hg : PosPolyIs s.mem (pa s secret) g) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.responseProduct out secret) s fun t =>
      PPostB S s t [(out,1024),(sc oPS,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      RawPolyIs t.mem (pa s out) (nttInv (multiplyNTT f g)) := by
  simp only [responseProductChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ho,ha⟩,hb⟩,hsc⟩,hwo⟩,hws⟩,hoa⟩,hob⟩,hos⟩,has⟩,hbs⟩ := hc
  refine productAt_field_layout hs.1.lay ho ha hb hsc ?_ hf hg
  refine productReady_layout hs.1.lay ho ha hb hsc hwo hws hoa hob hos has hbs
    hs.2.inverse.held hs.2.inverse.fit ?_ hs.2.inverse.readable hf.bound hg.bound
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.2.inverse.apart_write (hs.1.lay.inW hwo)
  · exact hs.2.inverse.apart_write (hs.1.lay.inW hws)

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedResponseState.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.Sha3 (bytesAt)

/-- Signed response storage remains explicit until accepted output. -/
def SignedFam (s : State) (b m : Nat) (f : Nat → Poly) (lo hi : Int) : Prop :=
  ∀j<m,SignedPl s (b+j) (f j) lo hi

theorem SignedFam.keep {S : Nat} {rbs wbs : List (Reg × Nat)} {s u : State}
    (L : Lay S rbs wbs s) {ws : List (Ptr × Nat)} {b m : Nat} {f : Nat → Poly} {lo hi : Int}
    (hP : PPostB S s u ws) (hc : famChk rbs wbs ws b m=true)
    (h : SignedFam s b m f lo hi) : SignedFam u b m f lo hi :=
  fun j hj => keepSignedPoly L hP (famChk_one hc hj) (h j hj)

theorem SignedFam.snoc {s : State} {b m : Nat} {f : Nat → Poly} {lo hi : Int}
    (h : SignedFam s b m f lo hi) (ht : SignedPl s (b+m) (f m) lo hi) :
    SignedFam s b (m+1) f lo hi := by
  intro j hj
  rcases (by omega : j<m ∨ j=m) with hj | rfl
  · exact h j hj
  · exact ht

structure PositiveKB (p : Params) (S : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  l : PositiveIL p S σ t s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p)=CTv p σ (p.ℓ*t)
  c : PosPl s 0 (VG.Proof.MlDsa.Sign.chF (cV p σ (p.ℓ*t)))
  sampled : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ*t))).isSome

theorem PositiveKB.step {p : Params} {S : Nat} {σ s u : State} {t : Nat}
    (h : PositiveKB p S σ t s) {ws : List (Ptr × Nat)}
    (hP : PPostB S s u ws) (hy : u.syms=s.syms) (hc : kbChk p ws=true)
    (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true) : PositiveKB p S σ t u := by
  simp only [kbChk,Bool.and_eq_true] at hc
  exact ⟨h.l.step hP hy hc.1.1 hw,(h.l.st.lay.keepBytes hP hc.1.2).trans h.ct,
    h.c.keep h.l.st.lay hP hc.2,h.sampled⟩

structure PositiveIZb (p : Params) (S : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  b : PositiveKB p S σ t s
  z : SignedFam s (yBase p) r (Zv p σ (p.ℓ*t)) (-(q:Int)+1) ((q:Int)-1)
  y : Fam s (yBase p+r) (p.ℓ-r) fun j => Yv p σ (p.ℓ*t) (r+j)
  w : Fam s (wBase p) p.k (Wv p σ (p.ℓ*t))
  ones : s.mem.readW (pa s (sc oONES)) 64=0

def PositiveIZ (p : Params) (S : Nat) (σ : State) (t r : Nat) (s : State) : Prop :=
  PositiveIZb p S σ t r s ∧
    s.gpr .x24=bit (∀j<r,normRq [Zv p σ (p.ℓ*t) j]<p.γ₁-p.β)

theorem PositiveIZb.step {p : Params} {S : Nat} {σ s u : State} {t r : Nat}
    (h : PositiveIZb p S σ t r s) {ws : List (Ptr × Nat)}
    (hP : PPostB S s u ws) (hy : u.syms=s.syms) (hc : zfam p ws r=true)
    (hys : famChk (sgR p) (sgW p) ws (yBase p+r) (p.ℓ-r)=true)
    (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true) : PositiveIZb p S σ t r u := by
  simp only [zfam,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP hy h1 hw,h.z.keep L hP h2,h.y.keep L hP hys,h.w.keep L hP h3,
    (L.keepW hP h4).trans h.ones⟩

end VG.Proof.MlDsa.AArch64.Sign

end
