import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedDot
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRestState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotCallTiming

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.AArch64.Optimized.Inverse

abbrev dotWrites (p : Params) (_i : Nat) : List (Ptr × Nat) := [(tP p,1024),(sc oSS,1024)]

def optimizedDotChk (p : Params) (i : Nat) : Bool :=
  let o := tP p; let a := aP (p.ℓ*i); let b := sP p 0; let z := sc oSS
  inB (kgR++kgW p) o 1024 && inB (kgR++kgW p) a (1024*p.ℓ) &&
  inB (kgR++kgW p) b (1024*p.ℓ) && inB (kgR++kgW p) z 1024 &&
  inB (kgW p) o 1024 && inB (kgW p) z 1024 &&
  sepB (kgR) (kgW p) o 1024 a (1024*p.ℓ) &&
  sepB (kgR) (kgW p) o 1024 b (1024*p.ℓ) &&
  sepB (kgR) (kgW p) o 1024 z 1024 &&
  sepB (kgR) (kgW p) a (1024*p.ℓ) z 1024 &&
  sepB (kgR) (kgW p) b (1024*p.ℓ) z 1024 && kcChk p (dotWrites p i)

theorem optimizedDotChk_ok {p : Params} (hp : PFacts p) : ∀i<p.k,optimizedDotChk p i=true := by
  rcases hp.mem with rfl | rfl | rfl <;> decide

theorem optimizedDotReady {p : Params} (hp : PFacts p) {S : Nat} {σ s : State} {i : Nat}
    (hc : optimizedDotChk p i=true) (hpre : kgPre p S σ) (hs : KC p σ s) (roots : Sign.StaticRoots S s)
    (ha : ∀j<p.ℓ,PositiveReduced s.mem (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)))
    (hb : ∀j<p.ℓ,PositiveReduced s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j))) :
    DotCallReady p.ℓ (tP p) (aP (p.ℓ*i)) (sP p 0) (sc oSS) s := by
  simp only [optimizedDotChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ro,ra⟩,rb⟩,rz⟩,wo⟩,wz⟩,oa⟩,ob⟩,oz⟩,az⟩,bz⟩,_⟩ := hc
  have L := hs.lay hp hpre
  refine ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.nwp rz,roots.inverse.held,roots.inverse.fit,?_,
    L.disj oa,L.disj ob,L.disj oz,L.disj az,L.disj bz,ha,hb,?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact roots.inverse.apart_write (L.inW wo)
    · exact roots.inverse.apart_write (L.inW wz)
  · exact Covers.cons (L.cR ra) (Covers.cons (L.cR rb)
      (Covers.cons roots.inverse.readable (Covers.cons (L.cR ro) (L.cR rz))))
  · exact Covers.cons (L.cW wo) (L.cW wz)

/-- Fused row arithmetic preserves all polynomial families outside its two
write slots. The returned frame can be applied directly to Fam/PosFam. -/
theorem optimizedDot_ok {p : Params} {S : Nat} {σ s : State} {i : Nat}
    (hp : PFacts p) (hc : optimizedDotChk p i=true) (hpre : kgPre p S σ) (hs : KC p σ s) (roots : Sign.StaticRoots S s)
    (ha : ∀j<p.ℓ,PositiveReduced s.mem (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)))
    (hb : ∀j<p.ℓ,PositiveReduced s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j))) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.dotRow p i) s fun t =>
      KC p σ t ∧ Sign.StaticRoots S t ∧ t.gpr .x24=s.gpr .x24 ∧ PPostB S s t (dotWrites p i) ∧
      PolyIs t.mem (pa t (tP p)) (nttInv (dotNTT
        (fun j => polyAt s.mem (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)))
        (fun j => polyAt s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j))) p.ℓ)) := by
  have ready := optimizedDotReady hp hc hpre hs roots ha hb
  simp only [optimizedDotChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ro,ra⟩,rb⟩,rz⟩,wo⟩,wz⟩,_⟩,_⟩,_⟩,_⟩,_⟩,st⟩ := hc
  have hn : p.ℓ=4 ∨ p.ℓ=5 ∨ p.ℓ=7 := by rcases hp.mem with rfl | rfl | rfl <;> decide
  have L := hs.lay hp hpre
  refine WP.mono_syms (dotAt_ok L.s64 hn (ptr_ok (L.ptrBs ro)) (ptr_ok (L.ptrBs ra))
    (ptr_ok (L.ptrBs rb)) (ptr_ok (L.ptrBs rz)) ready) fun t ⟨hP,hv⟩ hy => ?_
  have hpB : PPostB S s t (dotWrites p i) := hP.b
  refine ⟨hs.step hp hpre hpB st,roots.step_layout L hpB hy ?_,hP.cs .x24 (by decide) (by decide),hpB,?_⟩
  · intro w hw
    simp only [dotWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact wo
    · exact wz
  · rw [hpB.pa (L.ptrBs ro)]; exact hv


end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
