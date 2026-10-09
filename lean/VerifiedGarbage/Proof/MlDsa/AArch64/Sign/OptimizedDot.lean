import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Optimized
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.LazyInv

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg sc)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.AArch64.Optimized.Inverse

abbrev dotWrites (p : Params) (i : Nat) : List (Ptr × Nat) := [(wP p i,1024),(sc oPS,1024)]

def optimizedDotChk (p : Params) (i : Nat) : Bool :=
  let o := wP p i; let a := aP p i 0; let b := yhP p 0; let z := sc oPS
  inB (sgR p++sgW p) o 1024 && inB (sgR p++sgW p) a (1024*p.ℓ) &&
  inB (sgR p++sgW p) b (1024*p.ℓ) && inB (sgR p++sgW p) z 1024 &&
  inB (sgW p) o 1024 && inB (sgW p) z 1024 &&
  sepB (sgR p) (sgW p) o 1024 a (1024*p.ℓ) &&
  sepB (sgR p) (sgW p) o 1024 b (1024*p.ℓ) &&
  sepB (sgR p) (sgW p) o 1024 z 1024 &&
  sepB (sgR p) (sgW p) a (1024*p.ℓ) z 1024 &&
  sepB (sgR p) (sgW p) b (1024*p.ℓ) z 1024 && stChk p (dotWrites p i)

theorem optimizedDotChk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,optimizedDotChk p i=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem optimizedDotReady {p : Params} {S : Nat} {σ s : State} {i : Nat}
    (hc : optimizedDotChk p i=true) (hs : RootedSt p S σ s)
    (ha : ∀j<p.ℓ,PositiveReduced s.mem (pa s (aP p i 0)+BitVec.ofNat 64 (1024*j)))
    (hb : ∀j<p.ℓ,PositiveReduced s.mem (pa s (yhP p 0)+BitVec.ofNat 64 (1024*j))) :
    DotCallReady p.ℓ (wP p i) (aP p i 0) (yhP p 0) (sc oPS) s := by
  simp only [optimizedDotChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ro,ra⟩,rb⟩,rz⟩,wo⟩,wz⟩,oa⟩,ob⟩,oz⟩,az⟩,bz⟩,_⟩ := hc
  have L := hs.1.lay
  refine ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.nwp rz,hs.2.inverse.held,hs.2.inverse.fit,?_,
    L.disj oa,L.disj ob,L.disj oz,L.disj az,L.disj bz,ha,hb,?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.inverse.apart_write (L.inW wo)
    · exact hs.2.inverse.apart_write (L.inW wz)
  · exact Covers.cons (L.cR ra) (Covers.cons (L.cR rb)
      (Covers.cons hs.2.inverse.readable (Covers.cons (L.cR ro) (L.cR rz))))
  · exact Covers.cons (L.cW wo) (L.cW wz)

/-- Fused row arithmetic preserves all polynomial families outside its two
write slots. The returned frame can be applied directly to Fam/PosFam. -/
theorem optimizedDot_ok {p : Params} {S : Nat} {σ s : State} {i : Nat}
    (hp : Ok3 p) (hc : optimizedDotChk p i=true) (hs : RootedSt p S σ s)
    (ha : ∀j<p.ℓ,PositiveReduced s.mem (pa s (aP p i 0)+BitVec.ofNat 64 (1024*j)))
    (hb : ∀j<p.ℓ,PositiveReduced s.mem (pa s (yhP p 0)+BitVec.ofNat 64 (1024*j))) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.rowW p i) s fun t =>
      RootedSt p S σ t ∧ t.gpr .x24=s.gpr .x24 ∧ PPostB S s t (dotWrites p i) ∧
      PolyIs t.mem (pa t (wP p i)) (nttInv (dotNTT
        (fun j => polyAt s.mem (pa s (aP p i 0)+BitVec.ofNat 64 (1024*j)))
        (fun j => polyAt s.mem (pa s (yhP p 0)+BitVec.ofNat 64 (1024*j))) p.ℓ)) := by
  have ready := optimizedDotReady hc hs ha hb
  simp only [optimizedDotChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ro,ra⟩,rb⟩,rz⟩,wo⟩,wz⟩,_⟩,_⟩,_⟩,_⟩,_⟩,st⟩ := hc
  have hn : p.ℓ=4 ∨ p.ℓ=5 ∨ p.ℓ=7 := by rcases hp with rfl | rfl | rfl <;> decide
  have L := hs.1.lay
  refine WP.mono_syms (dotAt_ok L.s64 hn (ptr_ok (L.ptrBs ro)) (ptr_ok (L.ptrBs ra))
    (ptr_ok (L.ptrBs rb)) (ptr_ok (L.ptrBs rz)) ready) fun t ⟨hP,hv⟩ hy => ?_
  have hpB : PPostB S s t (dotWrites p i) := hP.b
  refine ⟨hs.step hpB hy st ?_,hP.cs .x24 (by decide) (by decide),hpB,?_⟩
  · intro w hw
    simp only [dotWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact wo
    · exact wz
  · rw [hpB.pa (L.ptrBs ro)]; exact hv

theorem dot_pS_addr (s : State) (b j : Nat) :
    pa s (pS (b+j))=pa s (pS b)+BitVec.ofNat 64 (1024*j) := by
  simp only [pa,oP, Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

private theorem dotNTT_congr {f g f' g' : Nat → Poly} {count : Nat}
    (hf : ∀j<count,f j=f' j) (hg : ∀j<count,g j=g' j) : dotNTT f g count=dotNTT f' g' count := by
  unfold dotNTT
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [hf j hj,hg j hj]

/-- Canonical matrix rows and lazy mask transforms feed the fused dot directly.
Both input families survive the call unchanged. -/
theorem optimizedDot_families {p : Params} {S : Nat} {σ s : State} {i : Nat} {f g : Nat → Poly}
    (hp : Ok3 p) (hc : optimizedDotChk p i=true) (hs : RootedSt p S σ s)
    (ha : Fam s (5+4*p.k+3*p.ℓ+p.ℓ*i) p.ℓ f)
    (hb : PosFam s (5+p.k+p.ℓ) p.ℓ g)
    (hka : famChk (sgR p) (sgW p) (dotWrites p i) (5+4*p.k+3*p.ℓ+p.ℓ*i) p.ℓ=true)
    (hkb : famChk (sgR p) (sgW p) (dotWrites p i) (5+p.k+p.ℓ) p.ℓ=true) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.rowW p i) s fun t =>
      RootedSt p S σ t ∧ t.gpr .x24=s.gpr .x24 ∧
      Fam t (5+4*p.k+3*p.ℓ+p.ℓ*i) p.ℓ f ∧ PosFam t (5+p.k+p.ℓ) p.ℓ g ∧
      PolyIs t.mem (pa t (wP p i)) (nttInv (dotNTT f g p.ℓ)) := by
  have hA j (hj : j<p.ℓ) : PolyIs s.mem
      (pa s (aP p i 0)+BitVec.ofNat 64 (1024*j)) (f j) := by
    have h := ha j hj
    change PolyIs s.mem (pa s (pS ((5+4*p.k+3*p.ℓ+p.ℓ*i)+j))) (f j) at h
    rw [dot_pS_addr] at h
    simpa only [aP,Nat.add_zero] using h
  have hB j (hj : j<p.ℓ) : PosPolyIs s.mem
      (pa s (yhP p 0)+BitVec.ofNat 64 (1024*j)) (g j) := by
    have h := hb j hj
    change PosPolyIs s.mem (pa s (pS ((5+p.k+p.ℓ)+j))) (g j) at h
    rw [dot_pS_addr] at h
    simpa only [yhP,Nat.add_zero] using h
  refine WP.mono (optimizedDot_ok hp hc hs
    (fun j hj => (PosPolyIs.of_canonical (hA j hj)).bound)
    (fun j hj => (hB j hj).bound)) fun t ⟨hst,h24,hP,hv⟩ => ?_
  refine ⟨hst,h24,ha.keep hs.1.lay hP hka,hb.keep hs.1.lay hP hkb,?_⟩
  have he := dotNTT_congr (fun j hj => (hA j hj).2) (fun j hj => (hB j hj).value)
  rw [he] at hv
  exact hv

theorem optimizedDot_preserves {p : Params} (hp : Ok3 p) : ∀i<p.k,
    famChk (sgR p) (sgW p) (dotWrites p i) (5+4*p.k+3*p.ℓ+p.ℓ*i) p.ℓ=true ∧
    famChk (sgR p) (sgW p) (dotWrites p i) (5+p.k+p.ℓ) p.ℓ=true := by
  rcases hp with rfl | rfl | rfl <;> decide

/-- Only public addresses and static table identity enter the call trace. -/
theorem optimizedDot_tr {p : Params} {S : Nat} {i : Nat} (hp : Ok3 p)
    (hc : optimizedDotChk p i=true) {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → (∃σ,RootedSt p S σ x) ∧ (∃σ,RootedSt p S σ y) ∧
      (∀j<p.ℓ,PositiveReduced x.mem (pa x (aP p i 0)+BitVec.ofNat 64 (1024*j))) ∧
      (∀j<p.ℓ,PositiveReduced x.mem (pa x (yhP p 0)+BitVec.ofNat 64 (1024*j))) ∧
      (∀j<p.ℓ,PositiveReduced y.mem (pa y (aP p i 0)+BitVec.ofNat 64 (1024*j))) ∧
      (∀j<p.ℓ,PositiveReduced y.mem (pa y (yhP p 0)+BitVec.ofNat 64 (1024*j))) ∧
      x.gpr .x28=y.gpr .x28 ∧ x.sp=y.sp ∧
      x.syms "VG_MLDSA_INV_FOLDED"=y.syms "VG_MLDSA_INV_FOLDED") :
    RelCT isa Q (Impl.MlDsa.AArch64.Sign.Optimized.rowW p i) fun _ _ => True := by
  have hn : p.ℓ=4 ∨ p.ℓ=5 ∨ p.ℓ=7 := by rcases hp with rfl | rfl | rfl <;> decide
  apply dotAt_tr (S:=S) hn
    (ptr_ok (by change Reg.x28∈keptRegs; decide))
    (ptr_ok (by change Reg.x28∈keptRegs; decide))
    (ptr_ok (by change Reg.x28∈keptRegs; decide))
    (ptr_ok (by change Reg.x28∈keptRegs; decide))
  intro x y hxy
  obtain ⟨⟨σx,hx⟩,⟨σy,hy⟩,ax,bx,ay,by',h28,hsp,ht⟩ := hQ x y hxy
  exact ⟨optimizedDotReady hc hx ax bx,optimizedDotReady hc hy ay by',
    by simp only [pa,h28],by simp only [pa,h28],by simp only [pa,h28],
    by simp only [pa,h28],hsp,ht⟩

end VG.Proof.MlDsa.AArch64.Sign
