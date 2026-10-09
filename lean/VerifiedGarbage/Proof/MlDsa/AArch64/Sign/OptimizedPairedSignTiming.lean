import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedRestTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : Proof.Sha3.AArch64.Permutation}

def WithPaired (S : Nat) (R : State → State → Prop) (x y : State) : Prop :=
  R x y ∧ PairedRoots S x ∧ PairedRoots S y ∧
    x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR"

theorem withPaired_tr {S : Nat} {R Q : State → State → Prop} {code : Prog isa}
    (hd : 16*code.aarch64Depth≤S) (hS : S<2^64) (ht : RelCT isa R code Q) :
    RelCT isa (WithPaired S R) code (WithPaired S Q) := by
  intro x y tx ty x' y' h ex ey
  have res := ht _ _ _ _ _ _ h.1 ex ey
  exact ⟨res.1,res.2,h.2.1.exec ex hd hS,h.2.2.1.exec ey hd hS,by
    simpa only [VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using h.2.2.2⟩

theorem pairedSign_ct {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : Ok3 p)
    {checks : Prog isa}
    (hinit : 16*(positiveDecodeWith keccak.callee P p).aarch64Depth≤D)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤D)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤D)
    (hchecks : ∀σ s t,PositiveIB p D σ t s → PairedRoots D s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u=>(PositiveEP p D σ t u ∨ PositiveEF p D σ t u) ∧ PairedRoots D u)
    (hct : PairedChecksCT p D checks) :
    ConstantTime isa (fun s=>(signK p D).pre s ∧ StaticRoots D s ∧ PairedRoots D s)
      (fun x y=>(signK p D).pub x y ∧ RootSymbolsEq x y ∧
        x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR")
      (Impl.MlDsa.AArch64.Sign.Optimized.signWith keccak.callee P p checks) := by
  have trace : RelCT isa (WithPaired D (PositiveEntry p D))
      (Impl.MlDsa.AArch64.Sign.Optimized.signWith keccak.callee P p checks) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Optimized.signWith
    refine RelCT.seq (withPaired_tr (Nat.zero_le _) hP.s64 (positivePro_tr hp))
      (RelCT.seq (withPaired_tr (expandA_depth hP p) hP.s64 (positiveExpand_tr hP hp)) ?_)
    refine RelCT.seq (R:=LRel D (sgR p) (sgW p)) ?_
      (lrel_tr (fun _ _ h=>h) (by taint_decide))
    unfold ifOk
    refine ifOkElse_tr (P:=WithPaired D (PositiveRA p D)) (fun _ _ h=>by rw [h.1.1.2])
      (RelCT.mono (pairedRest_tr hP hp hinit hcommit hball hchecks hct) ?_
        (fun _ _ h=>h.1.lrel (fun _ _ h=>h.st)))
      (RelCT.mono nil_tr (fun _ _ h=>h) (fun _ _ h=>h.1.1.1.lrel (fun _ _ h=>h.st)))
    rintro x y ⟨⟨⟨⟨⟨σ,τ,ps,pt,pub,hx,hy⟩,eq⟩,rx,ry,re⟩,px,py,pe⟩,hne⟩
    have ex := x24_one hx.r01 hne
    have ey : y.gpr .x24=1 := eq ▸ ex
    obtain ⟨ox,fx⟩ := hx.ok ex
    obtain ⟨oy,fy⟩ := hy.ok ey
    exact ⟨⟨⟨σ,τ,ps,pt,pub,pub_leq pub (expandA_max ox) (expandA_max oy),
      ⟨⟨⟨hx.st,ox,fx⟩,rx⟩,px⟩,⟨⟨⟨hy.st,oy,fy⟩,ry⟩,py⟩⟩,re⟩,pe⟩
  intro x y tx ty x' y' hx hy pub ex ey
  exact (trace _ _ _ _ _ _ ⟨⟨hx.1,hy.1,pub.1,hx.2.1,hy.2.1,pub.2.1⟩,
    hx.2.2,hy.2.2,pub.2.2⟩ ex ey).1

end VG.Proof.MlDsa.AArch64.Sign
