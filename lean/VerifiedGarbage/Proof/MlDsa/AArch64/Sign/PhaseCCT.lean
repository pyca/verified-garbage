import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairTiming

namespace VG.Proof.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem commit_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) (hc : cChk p = true)
    {E : State → State → Prop} {t : Nat} :
    RelCT isa (RS p D E fun σ s => IL p D σ t s) (commitWith keccak.callee P p) (RS p D E fun σ s => IC p D σ t s) := by
  have hc' := hc
  simp only [cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc'
  obtain ⟨⟨⟨⟨hm, hw⟩, hh⟩, hs⟩, _⟩ := hc'
  unfold commitWith
  refine RelCT.seq (R := RS p D E fun σ s => ICw p D σ t 0 s) ?_ (RelCT.seq (R := RS p D E fun σ s => ICh p D σ t 0 s)
    ?_ (RelCT.seq (R := RS p D E fun σ s => ICh p D σ t p.k s) ?_ ?_))
  · exact RelCT.mono (masks_tr hP hm) (fun _ _ h => h)
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h.l,h.y,h.yh,fun _ h => by omega⟩)
  · refine RelCT.mono (seqR_tr (Q := fun i => RS p D E fun σ s => ICw p D σ t i s) p.k 0 fun i _ hi =>
      liftL (T := fun s => ∃ σ, ICw p D σ t i s) (fun σ s h => ⟨h.l.st, σ, h⟩)
        (fun _ _ _ h => rowW_ok hP (hw i (by omega)) (by omega) h) (rowW_trL hP (hw i (by omega)) (by omega)))
      (fun x y h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, by simp [w1Enc]; rfl⟩
  · refine RelCT.mono (seqR_tr (Q := fun i => RS p D E fun σ s => ICh p D σ t i s) p.k 0 fun i _ hi =>
      liftL (T := fun s => ∃ σ, ICh p D σ t i s) (fun σ s h => ⟨h.c.l.st, σ, h⟩)
        (fun _ _ _ h => w1R_ok hP (hh i (by omega)) (by omega) h) (w1R_trL hP (hh i (by omega)) (by omega)))
      (fun x y h => h) fun x y h => by rwa [Nat.zero_add] at h
  · refine liftT (fun _ _ h => h.c.l.st) (fun _ _ _ h => ctShake_ok hP hc h) ?_
    obtain ⟨hint, hh⟩ := keccak.mldsaSignCommitTaint p h3
    exact vector_lrel_tr (fun _ _ h => h) hh

end VG.Proof.MlDsa.AArch64.Sign
