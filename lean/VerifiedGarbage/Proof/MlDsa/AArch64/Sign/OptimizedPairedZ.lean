import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZLayout
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZ
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedZ

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

def pairedZWrites (p : Params) (r : Nat) : List (Ptr × Nat) := [(yP p r,2048),(t1P,2176)]

def pairedZChk (p : Params) (r : Nat) : Bool :=
  let ws := pairedZWrites p r
  inB (sgB p) cP 1024 && inB (sgB p) (s1P p r) 2048 &&
  inB (sgB p) (yP p r) 2048 && inB (sgB p) t1P 2176 &&
  inB (sgW p) (yP p r) 2048 && inB (sgW p) t1P 2176 &&
  sepB (sgR p) (sgW p) cP 1024 (yP p r) 2048 &&
  sepB (sgR p) (sgW p) cP 1024 t1P 2176 &&
  sepB (sgR p) (sgW p) (s1P p r) 2048 (yP p r) 2048 &&
  sepB (sgR p) (sgW p) (s1P p r) 2048 t1P 2176 &&
  sepB (sgR p) (sgW p) (yP p r) 2048 t1P 2176 &&
  decide (1≤p.γ₁-p.β ∧ p.γ₁-p.β≤524288) && zfam p ws r &&
  famChk (sgR p) (sgW p) ws (yBase p+(r+2)) (p.ℓ-(r+2)) &&
  zfam p [] (r+2) && famChk (sgR p) (sgW p) [] (yBase p+(r+2)) (p.ℓ-(r+2)) &&
  ws.all (fun w => inB (sgW p) w.1 w.2)

theorem pairedZChk_ok {p : Params} (hp : Ok3 p) : ∀r<p.ℓ,r+1<p.ℓ → pairedZChk p r=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem paired_pS_addr (s : State) (b j : Nat) :
    pairPolyPtr (pa s (pS b)) j=pa s (pS (b+j)) := by
  simp only [pairPolyPtr,pa,oP,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

theorem pairedZ_norm {f : Nat → Poly} {r B : Nat} (hB : 0<B) :
    normRq ((List.range 2).map fun j => f (r+j))<B ↔ ∀j<2,normRq [f (r+j)]<B := by
  rw [VG.Proof.MlDsa.Sign.normRq_lt_iff _ hB]
  simp only [List.mem_map,List.mem_range,forall_exists_index,and_imp]
  constructor
  · intro h j hj; exact h _ j hj rfl
  · intro h f j hj he; subst f; exact h j hj

theorem pairedZ_prefix {P : Nat → Prop} {r : Nat} :
    ((∀j<r,P j) ∧ ∀j<2,P (r+j)) ↔ ∀j<r+2,P j := by
  constructor
  · rintro ⟨h,t⟩ j hj
    by_cases h0 : j<r
    · exact h j h0
    · have := t (j-r) (by omega); simpa only [Nat.add_sub_of_le (by omega : r≤j)] using this
  · intro h; exact ⟨fun j hj => h j (by omega),fun j hj => h (r+j) (by omega)⟩

theorem optimizedZ_pair_ok {p : Params} {S : Nat} {σ s : State} {t r : Nat}
    (hp : Ok3 p) (hr : r+1<p.ℓ) (roots : PairedRoots S s) (h : PositiveIZ p S σ t r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.zPair p r) s fun u =>
      PositiveIZ p S σ t (r+2) u ∧ PairedRoots S u := by
  have checks := pairedZChk_ok hp r (by omega) hr
  simp only [pairedZChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checks
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,hy⟩,hw⟩,hwy⟩,hww⟩,hcy⟩,hcw⟩,hsy⟩,hsw⟩,hyw⟩,hB⟩,hz⟩,hys⟩,he⟩,hye⟩,hws⟩ := checks
  obtain ⟨h,hflag⟩ := h
  have hdata : ∀j<2,PolyIs s.mem (pairPolyPtr (pa s (yP p r)) j) (Yv p σ (p.ℓ*t) (r+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.y j (by omega)
  have hsecret : ∀j<2,PosPolyIs s.mem (pairPolyPtr (pa s (s1P p r)) j) (S1v p σ (r+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.b.l.k.d.s1 (r+j) (by omega)
  have hprod : pairedProductsReduced s.mem (pa s cP) (pa s (s1P p r)) :=
    ⟨h.b.c.bound,fun j hj => (hsecret j hj).bound⟩
  have hsum : ∀j<2,add (polyAt s.mem (pairPolyPtr (pa s (yP p r)) j))
      (pairedProduct s.mem (pa s cP) (pa s (s1P p r)) j)=Zv p σ (p.ℓ*t) (r+j) := by
    intro j hj
    rw [(hdata j hj).2]
    simp only [pairedProduct,h.b.c.value,(hsecret j hj).value]
    rfl
  have ready := pairedZReady_layout h.b.l.st.lay roots hc hs hy hw hwy hww hcy hcw hsy hsw hyw
    hprod (fun j hj => (hdata j hj).1) hB.1 hB.2
  unfold Impl.MlDsa.AArch64.Sign.Optimized.zPair
  refine WP.seq (WP.mono_syms (pairedZAt_layout (gamma:=p.γ₁) h.b.l.st.lay hc hs hy hw ready)
    fun a ⟨hpa,h24,hfields,hret⟩ hsa => ?_)
  have ra := roots.step_layout h.b.l.st.lay hpa hsa hws
  have hznew : ∀j<2,SignedPl a (yBase p+(r+j)) (Zv p σ (p.ℓ*t) (r+j)) (-(q:Int)+1) ((q:Int)-1) := by
    intro j hj
    have hv := hfields j hj
    rw [hsum j hj,paired_pS_addr] at hv
    change SignedPolyIs a.mem (pa a (pS (yBase p+(r+j)))) _ _ _
    rw [hpa.pa (by simp)]
    simpa only [Nat.add_assoc] using hv
  simp only [zfam,Bool.and_eq_true] at hz
  have zold := h.z.keep h.b.l.st.lay hpa hz.1.1.2
  have zall : SignedFam a (yBase p) (r+2) (Zv p σ (p.ℓ*t)) (-(q:Int)+1) ((q:Int)-1) := by
    have h0 := hznew 0 (by decide)
    have h1 := hznew 1 (by decide)
    simpa only [Nat.add_zero,Nat.add_assoc] using (zold.snoc (by simpa only [Nat.add_zero] using h0)).snoc h1
  have yshift : Fam s (yBase p+(r+2)) (p.ℓ-(r+2)) (fun j => Yv p σ (p.ℓ*t) (r+2+j)) := by
    simpa only [show r+1+1=r+2 by omega] using ((h.y.shift (by omega)).shift (by omega))
  have ytail := yshift.keep h.b.l.st.lay hpa hys
  have ha : PositiveIZb p S σ t (r+2) a :=
    ⟨h.b.step hpa hsa hz.1.1.1 hws,zall,ytail,
      h.w.keep h.b.l.st.lay hpa hz.1.2,(h.b.l.st.lay.keepW hpa hz.2).trans h.ones⟩
  have ret : (a.gpr .x0).setWidth 32=if normRq ((List.range 2).map fun j => Zv p σ (p.ℓ*t) (r+j))<p.γ₁-p.β then 1 else 0 := by
    have heq : ((List.range 2).map fun j =>
        add (polyAt s.mem (pairPolyPtr (pa s (yP p r)) j)) (pairedProduct s.mem (pa s cP) (pa s (s1P p r)) j))
        = (List.range 2).map (fun j => Zv p σ (p.ℓ*t) (r+j)) := by
      apply List.map_congr_left
      intro j hj
      exact hsum j (List.mem_range.mp hj)
    rw [heq] at hret
    exact hret
  refine WP.mono_syms (and24_ok a) fun u ⟨hku,hfu⟩ hsu => ?_
  have hpu : PPostB S a u [] := postB24 hku []
  refine ⟨⟨ha.step hpu hsu he hye (by simp),?_⟩,ra.step_layout ha.b.l.st.lay hpu hsu (by simp)⟩
  rw [hfu,bit_and (h24.trans hflag) ret]
  apply bit_congr
  rw [pairedZ_norm (by omega : 0<p.γ₁-p.β)]
  exact pairedZ_prefix

end VG.Proof.MlDsa.AArch64.Sign
