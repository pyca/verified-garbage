import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

def PositiveEntry (p : Params) (D : Nat) (x y : State) : Prop :=
  (signK p D).pre x ∧ (signK p D).pre y ∧ (signK p D).pub x y ∧
  StaticRoots D x ∧ StaticRoots D y ∧ RootSymbolsEq x y

theorem positivePro_tr {p : Params} {D : Nat} (hp : Ok3 p) :
    RelCT isa (PositiveEntry p D) (.block pro)
      (RR p D (fun σ s=>RootedSt p D σ s ∧ s.gpr .x24=1) RootSymbolsEq) := by
  have trace : RelCT isa (PositiveEntry p D) (.block pro) fun _ _=>True :=
    taintRel [.x0,.x1,.x2,.x3,.x4] (fun x y ⟨_,_,pub,_,_,_⟩=>by
      obtain ⟨e0,e1,e2,e3,e4,e5,_⟩ := pub
      refine ⟨e5,fun r hr=>?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl
      exacts [e0,e1,e2,e3,e4]) (by taint_decide)
  intro x y tx ty x' y' h ex ey
  obtain ⟨tr,_⟩ := trace _ _ _ _ _ _ h ex ey
  obtain ⟨px,py,pub,rx,ry,re⟩ := h
  obtain ⟨_,u,eu,hu⟩ := rooted_prologue hp px rx
  obtain ⟨_,v,ev,hv⟩ := rooted_prologue hp py ry
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨tr,⟨x,y,px,py,pub,hu,hv⟩,by
    simpa only [RootSymbolsEq,VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using re⟩

def PositiveRA (p : Params) (D : Nat) (x y : State) : Prop :=
  RA p D (p.k*p.ℓ) x y ∧ StaticRoots D x ∧ StaticRoots D y ∧ RootSymbolsEq x y

theorem positiveExpand_tr {P : Prims} {p : Params} {D : Nat} (hP : PrimsOk P D) (hp : Ok3 p) :
    RelCT isa (RR p D (fun σ s=>RootedSt p D σ s ∧ s.gpr .x24=1) RootSymbolsEq)
      (Impl.MlDsa.AArch64.Sign.expandA P p) (PositiveRA p D) := by
  have ha := aChk_ok hp
  intro x y tx ty x' y' h ex ey
  have old : RR p D (fun σ s=>St p D σ s ∧ s.gpr .x24=1) (fun _ _=>True) x y := h.mono (fun _ _ h=>⟨h.1.1,h.2⟩) (fun _=>trivial)
  obtain ⟨tr,out⟩ := expandA_tr hP hp ha _ _ _ _ _ _ old ex ey
  obtain ⟨⟨σ,τ,_,_,_,hx,hy⟩,re⟩ := h
  obtain ⟨_,u,eu,_,ru⟩ := rooted_expandA_ok hP hp ha hx.1 hx.2
  obtain ⟨_,v,ev,_,rv⟩ := rooted_expandA_ok hP hp ha hy.1 hy.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨tr,out,ru,rv,by
    simpa only [RootSymbolsEq,VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using re⟩

/-- The optimized signer adds only immutable artifact addresses to the public
layout relation; the original signing leakage remains unchanged. -/
theorem positiveSign_ct {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : Ok3 p)
    {checks : Prog isa}
    (hchecks : ∀σ s t,PositiveIB p D σ t s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u=>PositiveEP p D σ t u ∨ PositiveEF p D σ t u)
    (hct : PositiveChecksCT p D checks) :
    ConstantTime isa (fun s=>(signK p D).pre s ∧ StaticRoots D s)
      (fun x y=>(signK p D).pub x y ∧ RootSymbolsEq x y)
      (Impl.MlDsa.AArch64.Sign.Optimized.signWith keccak.callee P p checks) := by
  have trace : RelCT isa (PositiveEntry p D)
      (Impl.MlDsa.AArch64.Sign.Optimized.signWith keccak.callee P p checks) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Optimized.signWith
    refine RelCT.seq (positivePro_tr hp) (RelCT.seq (positiveExpand_tr hP hp) ?_)
    refine RelCT.seq (R := LRel D (sgR p) (sgW p)) ?_
      (lrel_tr (fun _ _ h=>h) (by taint_decide))
    unfold ifOk
    refine ifOkElse_tr (P := PositiveRA p D) (fun _ _ h=>by rw [h.1.2])
      (RelCT.mono (positiveRest_tr hP hp hchecks hct) ?_ (fun _ _ h=>h.1.lrel (fun _ _ h=>h.st)))
      (RelCT.mono nil_tr (fun _ _ h=>h) (fun _ _ h=>h.1.1.lrel (fun _ _ h=>h.st)))
    rintro x y ⟨⟨⟨⟨σ,τ,ps,pt,pub,hx,hy⟩,eq⟩,rx,ry,re⟩,hne⟩
    have ex := x24_one hx.r01 hne
    have ey : y.gpr .x24=1 := eq ▸ ex
    obtain ⟨ox,fx⟩ := hx.ok ex
    obtain ⟨oy,fy⟩ := hy.ok ey
    exact ⟨⟨σ,τ,ps,pt,pub,pub_leq pub (expandA_max ox) (expandA_max oy),
      ⟨⟨hx.st,ox,fx⟩,rx⟩,⟨⟨hy.st,oy,fy⟩,ry⟩⟩,re⟩
  intro x y tx ty x' y' hx hy pub ex ey
  exact (trace _ _ _ _ _ _ ⟨hx.1,hy.1,pub.1,hx.2,hy.2,pub.2⟩ ex ey).1

end VG.Proof.MlDsa.AArch64.Sign
