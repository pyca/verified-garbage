module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Optimized
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotCallTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.LazyInv
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.Arith

@[expose] public section

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

theorem optimizedDotReady {p : Params} {S : Nat} {σ s : State} {i : Nat}
    (hc : optimizedDotChk p i=true) (hs : RootedSt p S σ s)
    (ha : ∀j<p.ℓ,PositiveReduced s.mem (pa s (aP p i 0)+BitVec.ofNat 64 (1024*j)))
    (hb : ∀j<p.ℓ,PositiveReduced s.mem (pa s (yhP p 0)+BitVec.ofNat 64 (1024*j))) :
    DotCallReady p.ℓ (wP p i) (aP p i 0) (yhP p 0) (sc oPS) s := by
  simp only [optimizedDotChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ro,ra⟩,rb⟩,rz⟩,wo⟩,wz⟩,oa⟩,ob⟩,oz⟩,az⟩,bz⟩,_⟩ := hc
  have L := hs.1.lay
  refine ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.nwp rz,hs.2.inverse.held,hs.2.inverse.fit,?_,
    L.disj oa,L.disj ob,L.disj oz,L.disj az,L.disj bz,ha,hb,?_,?_,hs.2.inverse.aligned⟩
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
