import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentHash
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedMasksTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.Optimized
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem liftRootR {p : Params} {S : Nat} {E I J : State → State → Prop} {code : Prog isa}
    (hw : ∀ σ s,(signK p S).pre σ → I σ s → WP isa code s (J σ))
    (ht : RelCT isa (RootRS p S E I) code fun _ _ => True) :
    RelCT isa (RootRS p S E I) code (RootRS p S E J) := by
  intro x y tx ty x' y' h ex ey
  have heq := (ht _ _ _ _ _ _ h ex ey).1
  obtain ⟨σ,τ,hσ,hτ,hpub,he,hx,hy⟩ := h.1
  obtain ⟨_,u,eu,hu⟩ := hw σ x hσ hx
  obtain ⟨_,v,ev,hv⟩ := hw τ y hτ hy
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨heq,⟨σ,τ,hσ,hτ,hpub,he,hu,hv⟩,
    by simpa only [RootSymbolsEq,VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using h.2⟩

theorem RootRS.mono {p : Params} {S : Nat} {E I J : State → State → Prop} {x y : State}
    (h : RootRS p S E I x y) (hi : ∀σ s,I σ s → J σ s) : RootRS p S E J x y :=
  ⟨h.1.mono (fun _ _ h => h) hi,h.2⟩

theorem PositiveICw.inputs {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (h : PositiveICw p S σ t i s) (hi : i<p.k) :
    (∀j<p.ℓ,PositiveReduced s.mem (pa s (aP p i 0)+BitVec.ofNat 64 (1024*j))) ∧
    (∀j<p.ℓ,PositiveReduced s.mem (pa s (yhP p 0)+BitVec.ofNat 64 (1024*j))) := by
  constructor
  · intro j hj
    have he : p.ℓ*i+j<p.k*p.ℓ := by
      have hl := Nat.mul_le_mul_left p.ℓ (show i+1≤p.k by omega)
      simp only [Nat.mul_add,Nat.mul_one] at hl
      rw [Nat.mul_comm p.k p.ℓ]; omega
    have hv := h.masks.l.k.d.im.A (p.ℓ*i+j) he
    rw [aVal_ij hj] at hv
    change PolyIs s.mem (pa s (pS (aBase p+(p.ℓ*i+j)))) _ at hv
    rw [← Nat.add_assoc,dot_pS_addr] at hv
    simpa only [PositiveReduced,aP,aBase,Nat.add_zero] using (PosPolyIs.of_canonical hv).bound
  · intro j hj
    have hv := h.masks.yh j hj
    change PosPolyIs s.mem (pa s (pS (yhBase p+j))) _ at hv
    rw [dot_pS_addr] at hv
    simpa only [PositiveReduced,yhP,yhBase,Nat.add_zero] using hv.bound

theorem positiveRows_tr {p : Params} {S : Nat} (hp : Ok3 p) {E : State → State → Prop} {t : Nat} :
    RelCT isa (RootRS p S E (PositiveICm p S · t p.ℓ))
      (seqR (Impl.MlDsa.AArch64.Sign.Optimized.rowW p) 0 p.k)
      (RootRS p S E (PositiveICw p S · t p.k)) := by
  refine RelCT.mono (seqR_tr (Q := fun i => RootRS p S E (PositiveICw p S · t i)) p.k 0
    (fun i _ hi => ?_)) (fun _ _ h => h.mono (fun _ _ h => ⟨h,by simp [Fam]⟩))
    (fun _ _ h => by simpa only [Nat.zero_add] using h)
  refine liftRootR (fun _ _ _ h => positiveRowW_ok hp (by omega) h) ?_
  have hc := positiveRowChk_ok hp i (by omega)
  simp only [positiveRowChk,Bool.and_eq_true] at hc
  apply optimizedDot_tr hp hc.1.1
  intro x y h
  have L := h.1.lrel (fun _ _ h => h.masks.l.st)
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1
  have ix := hx.inputs (by omega)
  have iy := hy.inputs (by omega)
  exact ⟨⟨σ,hx.masks.l.st,hx.masks.l.k.d.roots⟩,⟨τ,hy.masks.l.st,hy.masks.l.k.d.roots⟩,
    ix.1,ix.2,iy.1,iy.2,L.regs .x28 (by decide),L.sp,h.2.2⟩

theorem positivePackRows_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {E : State → State → Prop} {t : Nat} :
    RelCT isa (RootRS p S E (PositiveICw p S · t p.k))
      (seqR (w1R P p) 0 p.k) (RootRS p S E (PositiveICh p S · t p.k)) := by
  have hc := cChk_ok hp
  simp only [cChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  obtain ⟨⟨⟨⟨_,_⟩,hh⟩,_⟩,_⟩ := hc
  refine RelCT.mono (seqR_tr (Q := fun i => RootRS p S E (PositiveICh p S · t i)) p.k 0
    (fun i _ hi => ?_)) (fun _ _ h => h.mono (fun _ _ h => ⟨h,by simp [w1Enc]; rfl⟩))
    (fun _ _ h => by simpa only [Nat.zero_add] using h)
  have hc := hh i (by omega)
  refine liftRootR (fun _ _ _ h => positiveW1R_ok hP hp (by omega) hc h) ?_
  simp only [hChk,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨cr,_⟩,_⟩,hg⟩ := hc
  unfold w1R
  apply highPackAt_tr (hP.highPack p.γ₂ hg) (B := bases)
    (fun b hb => ⟨sgB_bases p b hb,bases_kept _ (sgB_bases p b hb)⟩) cr
  intro x y h
  have L := h.1.lrel (fun _ _ h => h.c.masks.l.st)
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1
  exact ⟨L.lx,L.ly,(hx.c.w i (by omega)).1,(hy.c.w i (by omega)).1,L.same⟩

theorem positiveMasks_root_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {E : State → State → Prop} {t : Nat} :
    RelCT isa (RootRS p S E (PositiveIL p S · t)) (Impl.MlDsa.AArch64.Sign.Optimized.masks P p)
      (RootRS p S E (PositiveICm p S · t p.ℓ)) := by
  intro x y tx ty x' y' h ex ey
  have hm := positiveMasks_tr hP (positiveMasksChk_ok hp) _ _ _ _ _ _ ⟨h.1,h.2.1⟩ ex ey
  exact ⟨hm.1,hm.2.1,by simpa only [RootSymbolsEq,VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using h.2⟩

theorem positiveCommit_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {E : State → State → Prop} {t : Nat} :
    RelCT isa (RootRS p S E (PositiveIL p S · t))
      (Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p)
      (RootRS p S E (PositiveIC p S · t)) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.commitWith
  refine RelCT.seq (positiveMasks_root_tr hP hp) (RelCT.seq (positiveRows_tr hp)
    (RelCT.seq (positivePackRows_tr hP hp) ?_))
  apply liftRootT (fun _ _ h => ⟨h.c.masks.l.st,h.c.masks.l.k.d.roots⟩)
    (fun _ _ _ h => positiveCommitmentHash_ok hP hp h)
  obtain ⟨hint,hh⟩ := keccak.mldsaSignCommitTaint p hp
  exact vector_lrel_tr (fun _ _ h => h.1) hh

end VG.Proof.MlDsa.AArch64.Sign
