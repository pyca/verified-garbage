import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixBatchTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.Sign

theorem tail_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) :
    RelCT isa (RA mlDsa65 D 28) (Impl.MlDsa.AArch64.Sign.CachedMatrix.tail mlDsa65)
      (RA mlDsa65 D 30) := by
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.tail
  rw [show 4*(mlDsa65.k*mlDsa65.ℓ/4)=28 by decide]
  refine RelCT.seq (RelCT.mono (seqR_tr
    (Q:=fun j=>RR mlDsa65 D (AS mlDsa65 D · 28 j) fun x y=>x.gpr .x24=y.gpr .x24) 2 0
    (fun j _ hj=>slot4_tr (by omega)
      (slotChk_ok mlDsa65 (by simp) 28 (by decide) j (by omega)))) ?_ (fun _ _ h=>by simpa using h))
    (twoBatch_tr hP (show twoChk mlDsa65 28=true by decide))
  exact fun x y h=>h.mono (fun _ _ h=>⟨h,fun _ h=>False.elim (Nat.not_lt_zero _ h)⟩) (fun h=>h)

theorem expandA65_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) (hc : aChk mlDsa65 = true) :
    RelCT isa (RR mlDsa65 D (fun σ s => St mlDsa65 D σ s ∧ s.gpr .x24 = 1) fun _ _ => True)
      (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P mlDsa65) (RA mlDsa65 D (mlDsa65.k * mlDsa65.ℓ)) := by
  have hp : mlDsa65 ∈ [mlDsa44,mlDsa65,mlDsa87] := by simp
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA
  rw [ite_eq_left (by decide)]
  refine RelCT.seq (R := RA mlDsa65 D 0) (stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (J := fun σ s => IA mlDsa65 D σ 0 s)
    (E' := fun x y => x.gpr .x24 = y.gpr .x24)
    (fun σ s _ h => ?_) (lrel_tr (fun x y h => h.lrel fun _ _ h => h.1) (by taint_decide))
    fun x y x' y' h fx fy _ => ?_) ?_
  · refine WP.mono (copyP_ok h.1.lay hcp) fun s1 ⟨hP1, hcs1, hb⟩ => ⟨?_, hcs1.get .x24⟩
    have S1 := h.1.step hP1 hst
    have e15 : s1.gpr .x24 = 1 := by rw [hcs1.get .x24, h.2]
    exact ⟨S1, by rw [hP1.pa (by decide), hb, rhoOf, ← h.1.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk],
      .inr e15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      fun h0 => absurd (h0.symm.trans e15) (by decide)⟩
  · obtain ⟨⟨σ₁, σ₂, _, _, _, ⟨_, h₁⟩, ⟨_, h₂⟩⟩, _⟩ := h
    rw [fx, fy, h₁, h₂]
  · have hB : RelCT isa (RA mlDsa65 D 0) (seqR (sample4 P mlDsa65) 0 7) (RA mlDsa65 D 28) := by
      simpa only [Nat.zero_add,Nat.mul_zero] using
        (seqR_tr (Q:=fun g=>RA mlDsa65 D (4*g)) 7 0 (fun g _ hg=>
          sample4_tr hP (batchChk_ok mlDsa65 hp g (by change g<7; omega))
            (fun j hj=>slotChk_ok mlDsa65 hp (4*g) (by change 4*g<30; omega) j hj)))
    exact RelCT.seq hB (tail_tr hP)

theorem expandA_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (hp : Ok3 p) (hc : aChk p=true) :
    RelCT isa (RR p D (fun σ s=>St p D σ s ∧ s.gpr .x24=1) fun _ _=>True)
      (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) (RA p D (p.k*p.ℓ)) := by
  rcases hp with rfl|rfl|rfl
  · exact Sign.expandA_tr hP (.inl rfl) hc
  · exact expandA65_tr hP hc
  · exact Sign.expandA_tr hP (.inr (.inr rfl)) hc

theorem positiveExpand_tr {P : Prims} {p : Params} {D : Nat} (hP : PrimsOk P D) (hp : Ok3 p) :
    RelCT isa (RR p D (fun σ s=>RootedSt p D σ s ∧ s.gpr .x24=1) RootSymbolsEq)
      (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) (PositiveRA p D) := by
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


end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
