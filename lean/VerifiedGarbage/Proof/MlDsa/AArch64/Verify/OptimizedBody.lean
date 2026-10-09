import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedCompute
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesRoots
import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.OptimizedTop

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.KeyGen (ifn)
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem hint_depth {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params) :
    16*(hint P p).aarch64Depth≤S := by
  have hh : DLe (S/16) P.hintUnpack := ⟨by have:=hP.hintUnpack.fd;omega⟩
  have hd : DLe (S/16) (hint P p) := by unfold hint;dle_tac
  have := hd.le;omega

theorem zOne_depth {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params) (i : Nat) :
    16*(zOne P p i).aarch64Depth≤S := by
  have hb : DLe (S/16) P.bitUnpack := ⟨by have:=hP.bitUnpack.fd;omega⟩
  have hn : DLe (S/16) P.normLt := ⟨by have:=hP.normLt.fd;omega⟩
  have hd : DLe (S/16) (zOne P p i) := by unfold zOne;dle_tac
  have := hd.le;omega

theorem body_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    Piece p S (fun σ s=>(VC p σ s ∧ s.gpr .x24=1) ∧ Sign.StaticRoots S s) (VFin p)
      (Impl.MlDsa.AArch64.Verify.Optimized.bodyWith keccak.callee P p) := by
  unfold Impl.MlDsa.AArch64.Verify.Optimized.bodyWith
  refine (Piece.of_vpiece (OptimizedSamples.rooted_piece (hint_vpiece hP hF) (hint_depth hP p) hP.s64)).seq
    (Piece.ifOk (T:=fun σ=>(hintOf p σ).isSome=true) (fun _ _ _ h=>h.1.2.1)
      (fun _ _ _ _ pub=>by rw [hintOf,hintOf,(vPub_eq pub).2.2.2.1]) ?_ ?_)
  · refine Piece.seq (J:=fun σ s=>Z0 p p.ℓ σ s ∧ Sign.StaticRoots S s) ?_
      (Piece.ifOk (T:=fun σ=>normOk p σ p.ℓ) (fun _ _ _ h=>h.1.2)
        (fun _ _ _ _ pub=>by simp only [normOk,zOf,(vPub_eq pub).2.2.2.1]) ?_ ?_)
    · refine Piece.mono (Piece.seqR (I:=fun j σ s=>Z0 p j σ s ∧ Sign.StaticRoots S s) p.ℓ 0
        fun j _ hj=>Piece.of_vpiece (OptimizedSamples.rooted_piece (zOne_vpiece hP hF (by omega))
          (zOne_depth hP p j) hP.s64)) ?_ ?_
      · intro σ s _ ⟨⟨⟨hv,hx,hH⟩,roots⟩,ht⟩
        refine ⟨⟨⟨hv,?_,fun _ h=>absurd h (Nat.not_lt_zero _)⟩,?_⟩,roots⟩
        · obtain ⟨hh,e⟩:=Option.isSome_iff_exists.mp ht
          exact ⟨hh,e,hH hh e⟩
        · rw [hx];exact flag_congr (iff_of_true ht (normOk_zero p σ))
      · intro _ _ _ h;simpa only [Nat.zero_add] using h
    · refine (Piece.of_vpiece (OptimizedSamples.samples_rooted_vpiece hP hF)).seq (compute_piece hP hF) |>.mono ?_ (fun _ _ _ h=>h)
      intro _ _ _ ⟨⟨hz,roots⟩,hn⟩
      exact ⟨⟨hz,hn⟩,roots⟩
    · intro σ s _ ⟨h,roots⟩ hn
      refine ⟨h.1.vc,.inr ⟨by rw [h.2];exact ifn hn _ _,?_⟩⟩
      obtain ⟨hh,e,_⟩:=h.1.hint
      exact Proof.MlDsa.Verify.verifyMu_norm minBounds _ _ e
        (by rw [Proof.MlDsa.Verify.normR_vZ_iff hF.g1.2.1 p hF.g1.1];exact hn)
  · intro σ s _ ⟨h,roots⟩ hn
    refine ⟨h.1,.inr ⟨by rw [h.2.1];exact ifn hn _ _,?_⟩⟩
    show verifyMu p minBounds _ _ _ ≠ some true
    rw [Proof.MlDsa.Verify.verifyMu_hint_none minBounds _ _ (Option.not_isSome_iff_eq_none.mp hn)]
    nofun

end VG.Proof.MlDsa.AArch64.Verify.Optimized
