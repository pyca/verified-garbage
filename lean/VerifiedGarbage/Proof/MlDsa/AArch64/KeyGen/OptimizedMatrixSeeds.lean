import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Seed4

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-- The four copies of the public matrix seed survive all row samplers. -/
def MatrixPrefixes (p : Params) (σ : State) (n : Nat) (s : State) : Prop :=
  ∀k<n,bytesAt s.mem (pa s (sc (oSA4+34*k))) 32=rhoOf p σ

theorem MatrixPrefixes.keep {p : Params} {S : Nat} {σ s t : State} {n : Nat}
    (L : Lay S kgR (kgW p) s) (h : MatrixPrefixes p σ n s)
    {ws : List (Ptr × Nat)} (hp : PPostB S s t ws)
    (hc : ∀k<n,keepB kgR (kgW p) ws (sc (oSA4+34*k)) 32=true) : MatrixPrefixes p σ n t := by
  intro k hk
  rw [L.keepBytes hp (hc k hk)]
  exact h k hk

theorem matrixCopy_ok {p : Params} (hF : PFacts p) {S : Nat} {σ s : State}
    (hp : kgPre p S σ) {e j : Nat} (he : e≤p.k*p.ℓ) (hj : j<4)
    (hs : KSamp p σ e 0 s) (hr : MatrixPrefixes p σ j s) :
    WP isa (.block (copySeed4 j)) s fun t => KSamp p σ e 0 t ∧ MatrixPrefixes p σ (j+1) t := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := hs.k1.kc.lay hF hp
  refine WP.mono (copySeed4_ok hF L hj) fun t ⟨ht,hkeep,hbytes⟩ => ?_
  refine ⟨hs.keep hF hp ht (by unfold k1Chk kcChk; lay) (fun k hk => by lay)
    (fun _ h => False.elim (Nat.not_lt_zero _ h)) (hkeep.get .x24),?_⟩
  intro k hk
  by_cases hkj : k=j
  · subst k
    rw [sc_pa ht,hbytes,hs.k1.sa]
  · rw [L.keepBytes ht (by lay)]
    exact hr k (by omega)

theorem matrixPrefixes_ok {p : Params} (hF : PFacts p) {S : Nat} {σ s : State}
    (hp : kgPre p S σ) (hs : KSamp p σ 0 0 s) :
    WP isa (.block ((List.range 4).flatMap copySeed4)) s fun t =>
      KSamp p σ 0 0 t ∧ MatrixPrefixes p σ 4 t := by
  exact wp_range_flatMap (M := isa) (N := 4)
    (fun j t => KSamp p σ 0 0 t ∧ MatrixPrefixes p σ j t)
    (fun j t hj ht => matrixCopy_ok hF hp (Nat.zero_le _) hj ht.1 ht.2)
    4 (by omega) s ⟨hs,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

/-- Updating the two row/column bytes leaves the hoisted seed prefix intact. -/
theorem matrixNonce_ok {p : Params} (hF : PFacts p) {S : Nat} {σ s : State}
    (hp : kgPre p S σ) {e j : Nat} (he : e+j<p.k*p.ℓ) (hj : j<4)
    (hs : GS p σ e j s) (hr : MatrixPrefixes p σ 4 s) :
    WP isa (.block (setSR p e j)) s fun t => GS p σ e (j+1) t ∧ MatrixPrefixes p σ 4 t := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := hs.ks.k1.kc.lay hF hp
  unfold setSR
  refine WP.mono (setTwo_ok L (o := oSA4+34*j+32) (a := (e+j)%p.ℓ) (b := (e+j)/p.ℓ)
    (by dsimp only [oSA4]; omega) (by lay) (by lay)) fun t ⟨ht,hkeep,hbytes⟩ => ?_
  refine ⟨⟨hs.ks.keep hF hp ht (by unfold k1Chk kcChk; lay) (fun k hk => by lay)
    (fun _ h => False.elim (Nat.not_lt_zero _ h)) (hkeep.get .x24),?_⟩,
    hr.keep L ht (fun k hk => by lay)⟩
  intro k hk
  by_cases hkj : k=j
  · subst k
    rw [bytes34,L.keepBytes ht (by lay),hr j hj,sc_add,sc_pa ht,hbytes,
      Proof.MlDsa.KeyGen.seedA_eq]
  · rw [L.keepBytes ht (by lay)]
    exact hs.done k (by omega)

/-- Both full groups and the two-stream tail reuse the same prepared prefixes. -/
theorem matrixNonces_ok {p : Params} (hF : PFacts p) {S : Nat} {σ s : State}
    (hp : kgPre p S σ) {e n : Nat} (he : e+n≤p.k*p.ℓ) (hn : n≤4)
    (hs : KSamp p σ e 0 s) (hr : MatrixPrefixes p σ 4 s) :
    WP isa (seqR (fun j => .block (setSR p e j)) 0 n) s fun t =>
      GS p σ e n t ∧ MatrixPrefixes p σ 4 t := by
  simpa only [Nat.zero_add] using seqR_ok
    (I := fun j t => GS p σ e j t ∧ MatrixPrefixes p σ 4 t)
    n 0 (fun j _ hj t ht => matrixNonce_ok hF hp (by omega) (by omega) ht.1 ht.2)
    s ⟨⟨hs,fun _ hj => False.elim (Nat.not_lt_zero _ hj)⟩,hr⟩

theorem matrixPrefixes_tr {Q : State → State → Prop}
    (hq : ∀x y,Q x y → x.sp=y.sp ∧ x.gpr .x28=y.gpr .x28) :
    RelCT isa Q (.block ((List.range 4).flatMap copySeed4)) fun _ _ => True := by
  apply taintRel [.x28] (fun x y h => ⟨(hq x y h).1,?_⟩)
    (by taint_decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact (hq x y h).2

theorem matrixNonce_tr (p : Params) (e j : Nat) {Q : State → State → Prop}
    (hq : ∀x y,Q x y → x.sp=y.sp ∧ x.gpr .x28=y.gpr .x28) :
    RelCT isa Q (.block (setSR p e j)) fun _ _ => True := by
  apply taintRel [.x28] (fun x y h => ⟨(hq x y h).1,?_⟩)
    (show (taint.check (Taint.ofRegs [.x28]) (.block (setSR p e j)) (.block [])).isSome=true from by
      with_unfolding_all rfl)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact (hq x y h).2

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
