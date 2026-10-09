import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedRestTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedSignTiming

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem sign_ct {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : Ok3 p)
    {checks : Prog isa}
    (hinit : 16*(positiveDecodeWith keccak.callee P p).aarch64Depth≤D)
    (hloop : ∀σ s, PositiveIK p D σ s → PairedRoots D s →
      WP isa (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p checks) s
        (fun u=>PositiveXS p D σ u ∧ PairedRoots D u))
    (htloop : RelCT isa (PairedRS p D (LeakEq p 0) (PositiveIK p D))
      (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p checks) (PositiveOX p D)) :
    ConstantTime isa (fun s=>(signK p D).pre s ∧ StaticRoots D s ∧ PairedRoots D s)
      (fun x y=>(signK p D).pub x y ∧ RootSymbolsEq x y ∧
        x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR")
      (Impl.MlDsa.AArch64.Sign.Cached.signWith keccak.callee P p checks) := by
  have trace : RelCT isa (WithPaired D (PositiveEntry p D))
      (Impl.MlDsa.AArch64.Sign.Cached.signWith keccak.callee P p checks) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Cached.signWith
    refine RelCT.seq (withPaired_tr (Nat.zero_le _) hP.s64 (positivePro_tr hp))
      (RelCT.seq (withPaired_tr (CachedMatrix.expandA_depth hP p) hP.s64 (CachedMatrix.positiveExpand_tr hP hp)) ?_)
    refine RelCT.seq (R:=LRel D (sgR p) (sgW p)) ?_
      (lrel_tr (fun _ _ h=>h) (by taint_decide))
    unfold ifOk
    refine ifOkElse_tr (P:=WithPaired D (PositiveRA p D)) (fun _ _ h=>by rw [h.1.1.2])
      (RelCT.mono (rest_tr hP hp hinit hloop htloop) ?_
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

end VG.Proof.MlDsa.AArch64.Sign.Cached
