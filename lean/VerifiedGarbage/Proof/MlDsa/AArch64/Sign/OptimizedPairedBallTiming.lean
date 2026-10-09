import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTrace

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem positiveBall_step_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (h3 : Ok3 p) {t : Nat} (ht : t<814) :
    RelCT isa (RootRS p D (LeakEq p t) (PositiveIC p D · t))
      (ballAt P (cLen p) p.τ cP) fun x y=>RootRS p D (LeakEq p t) (PositiveIB p D · t) x y ∧
        (x.gpr .x0).setWidth 32=(y.gpr .x0).setWidth 32 := by
  have hc2 := bChk_ok h3
  have hc2' := hc2
  simp only [bChk,Bool.and_eq_true,decide_eq_true_eq] at hc2'
  obtain ⟨⟨⟨c1,_⟩,_⟩,hbp⟩ := hc2'
  refine RelCT.mono (liftRootQ (G := fun _ _=>True) (J := fun σ s=>PositiveIB p D σ t s) (F := fun _ _=>True)
    (fun _ _ _ h=>WP.mono (positiveBall_ok hP h3 hc2 h) fun _ h=>⟨h,trivial⟩)
    (RelCT.mono (ballCall_tr hP hbp c1) (fun x y ⟨h,_⟩=>⟨h.1.lrel (fun _ _ h=>h.c.masks.l.st),by
      obtain ⟨σ,τ,_,_,_,he,hx,hy⟩ := h.1
      rw [hx.ct,hy.ct]; exact leq_ct he ht⟩) (fun _ _ h=>h))
    (fun σ τ x y x' y' ps pt pub he _ _ _ jx jy _ _ eq roots=>
      ⟨⟨⟨σ,τ,ps,pt,pub,he,jx,jy⟩,roots⟩,eq⟩))
    (fun _ _ h=>⟨h,trivial⟩) (fun _ _ h=>h)

theorem pairedBall_step_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {t : Nat} (ht : t<814)
    (hd : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S) :
    RelCT isa (PairedRS p S (LeakEq p t) (PositiveIC p S · t))
      (ballAt P (cLen p) p.τ cP) fun x y=>PairedRS p S (LeakEq p t) (PositiveIB p S · t) x y ∧
        (x.gpr .x0).setWidth 32=(y.gpr .x0).setWidth 32 :=
  RelCT.mono (paired_trace_frame hd hP.s64 (positiveBall_step_tr hP hp ht)) (fun _ _ h=>h)
    (fun _ _ h=>⟨PairedRS.of_root h.1.1 h.2.1 h.2.2.1 h.2.2.2,h.1.2⟩)

theorem pairedCommit_tr {keccak : Proof.Sha3.AArch64.Permutation}
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hp : Ok3 p)
    (hd : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤S)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIL p S · t))
      (Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p)
      (PairedRS p S E (PositiveIC p S · t)) :=
  RelCT.mono (paired_trace_frame hd hP.s64 (positiveCommit_tr hP hp)) (fun _ _ h=>h)
    (fun _ _ h=>PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2)

end VG.Proof.MlDsa.AArch64.Sign
