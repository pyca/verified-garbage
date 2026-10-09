import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedMatrix

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Optimized.MatrixMask
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

theorem matrixMask_taint : ∀j<80,∀n∈[512,1024],
    (taint.check (Taint.ofRegs [.x28]) (code (sc (oP j)) n)
      (VG.Taint.hintOf taint (Taint.ofRegs [.x28]) (code (sc 0) n))).isSome=true := by
  decide +kernel

theorem matrixTail_tr {p : Params} {S j n : Nat} (hj : j<80) (hn : n∈[512,1024]) :
    RelCT isa (Two p S) (.seq (.block and24) (code (aP j) n)) fun _ _ => True :=
  RelCT.seq (Two.step (block_nomem_tr fun i hi _ => by
    simp only [and24,List.mem_singleton] at hi; subst hi; rfl)
    fun x _ => WP.mono (and24_ok x) fun _ ⟨o,_⟩ =>
      ⟨[],postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩)
    (taintRel [.x28] (fun _ _ h => Two.x28 h) (matrixMask_taint j hj n hn))

theorem matrixFour_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) : Piece p S (fun σ s => GS p σ (4*g) 4 s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => KSamp p σ (4*g+4) 0 s ∧ MatrixPrefixes p σ 4 s)
      (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g)))
        (.seq (.block and24) (code (aP (4*g)) 1024))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine ⟨fun _ _ hp h => matrixFour_ok hP hF hp hg h.1 h.2,
    rel_of (Q := fun x y => Two p S x y ∧
      bytesAt x.mem (pa x (sc oSA4)) 136 = bytesAt y.mem (pa y (sc oSA4)) 136) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨kc_two hF hp hp' hq h.1.ks.k1.kc h'.1.ks.k1.kc,by
        rw [h.1.seeds,h'.1.seeds,rho_pub hq]⟩)⟩
  have hc : rej4Chk kgR (kgW p) (sc oSA4) (aP (4*g)) (sc (oR4 p)) = true := by
    unfold rej4Chk; lay
  have ok := fun x (L : Lay S kgR (kgW p) x) => WP.mono (rej4At_ok hP.s64 hP.rej4 L hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1)
    (rej4At_tr hP.rej4 (kgOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) (matrixTail_tr (by omega) (by simp))

theorem matrixTwo_seeds {p : Params} {σ : State} {e : Nat} {s : State} (h : GS p σ e 2 s) :
    bytesAt s.mem (pa s (sc oSA4)) 68=
      VG.Proof.MlDsa.KeyGen.seedA (rhoOf p σ) (e/p.ℓ) (e%p.ℓ) ++
      VG.Proof.MlDsa.KeyGen.seedA (rhoOf p σ) ((e+1)/p.ℓ) ((e+1)%p.ℓ) := by
  rw [show 68=34+34 from rfl,Proof.MlKem.bytesAt_add]
  have h0 := seed2_eq h (k := 0) (by decide)
  have h1 := seed2_eq h (k := 1) (by decide)
  simp only [Spec.MlDsa.seed4,Nat.mul_zero,Nat.add_zero,Nat.mul_one,
    VG.Proof.MlKem.AArch64.ptr_zero] at h0 h1
  rw [h0,h1]


theorem matrixTwo_piece {S : Nat} (hS : S<2^64) {cd : Prog isa} {nm : String}
    (C : CalleeOk S cd (VG.Spec.MlDsa.rejNTT2Contract AArch64.abi S)) {p : Params} (hF : PFacts p)
    {e : Nat} (he : e+2≤p.k*p.ℓ) : Piece p S (fun σ s => GS p σ e 2 s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => KSamp p σ (e+2) 0 s ∧ MatrixPrefixes p σ 4 s)
      (.seq (callAt nm cd (rej2Args (sc oSA4) (aP e) (sc (oR4 p))))
        (.seq (.block and24) (code (aP (e)) 512))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine ⟨fun _ _ hp h => matrixTwo_ok hS C hF hp he h.1 h.2,
    rel_of (Q := fun x y => Two p S x y ∧
      bytesAt x.mem (pa x (sc oSA4)) 68 = bytesAt y.mem (pa y (sc oSA4)) 68) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨kc_two hF hp hp' hq h.1.ks.k1.kc h'.1.ks.k1.kc,by
        rw [matrixTwo_seeds h.1,matrixTwo_seeds h'.1,rho_pub hq]⟩)⟩
  have hc : rej2Chk kgR (kgW p) (sc oSA4) (aP (e)) (sc (oR4 p)) = true := by
    unfold rej2Chk; lay
  have ok := fun x (L : Lay S kgR (kgW p) x) => WP.mono (rej2At_ok hS C L (nm := nm) hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1)
    (rej2At_tr C (kgOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) (matrixTail_tr (by omega) (by simp))

theorem matrixPrefixes_piece {p : Params} (hF : PFacts p) {S : Nat} :
    Piece p S (KSamp p · 0 0) (fun σ s => KSamp p σ 0 0 s ∧ MatrixPrefixes p σ 4 s)
      (.block ((List.range 4).flatMap copySeed4)) := by
  refine ⟨fun _ _ hp h => matrixPrefixes_ok hF hp h,rel_of (Q := Two p S) ?_ ?_⟩
  · exact matrixPrefixes_tr fun x y h => ⟨h.same.2,h.same.1 .x28 (by decide)⟩
  · intro σ τ x y hp hq pub hx hy
    exact kc_two hF hp hq pub hx.k1.kc hy.k1.kc

theorem matrixNonce_piece {p : Params} (hF : PFacts p) {S e j : Nat}
    (he : e+j<p.k*p.ℓ) (hj : j<4) :
    Piece p S (fun σ s => GS p σ e j s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => GS p σ e (j+1) s ∧ MatrixPrefixes p σ 4 s) (.block (setSR p e j)) := by
  refine ⟨fun _ _ hp h => matrixNonce_ok hF hp he hj h.1 h.2,rel_of (Q := Two p S) ?_ ?_⟩
  · exact matrixNonce_tr p e j fun x y h => ⟨h.same.2,h.same.1 .x28 (by decide)⟩
  · intro σ τ x y hp hq pub hx hy
    exact kc_two hF hp hq pub hx.1.ks.k1.kc hy.1.ks.k1.kc

theorem matrixNonces_piece {p : Params} (hF : PFacts p) {S e n : Nat}
    (he : e+n≤p.k*p.ℓ) (hn : n≤4) :
    Piece p S (fun σ s => KSamp p σ e 0 s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => GS p σ e n s ∧ MatrixPrefixes p σ 4 s)
      (seqR (fun j => .block (setSR p e j)) 0 n) := by
  exact Piece.mono (Piece.seqR (I := fun j σ s => GS p σ e j s ∧ MatrixPrefixes p σ 4 s)
    n 0 (fun j _ hj => matrixNonce_piece hF (by omega) (by omega)))
    (fun _ _ _ h => ⟨⟨h.1,fun _ hj => False.elim (Nat.not_lt_zero _ hj)⟩,h.2⟩)
    (fun _ _ _ h => by simpa only [Nat.zero_add] using h)

theorem matrixGroup_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    {g : Nat} (hg : 4*g+4≤p.k*p.ℓ) :
    Piece p S (fun σ s => KSamp p σ (4*g) 0 s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => KSamp p σ (4*g+4) 0 s ∧ MatrixPrefixes p σ 4 s)
      (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.matrixGroup P p g) :=
  Piece.seq (matrixNonces_piece hF hg (by decide)) (matrixFour_piece hP hF hg)

theorem matrixTwoPhase_piece {S : Nat} (hS : S<2^64) {cd : Prog isa}
    (C : CalleeOk S cd (Spec.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p) {e : Nat} (he : e+2≤p.k*p.ℓ) :
    Piece p S (fun σ s => KSamp p σ e 0 s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => KSamp p σ (e+2) 0 s ∧ MatrixPrefixes p σ 4 s)
      (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.matrixTwo cd p e) :=
  Piece.seq (matrixNonces_piece hF he (by decide)) (matrixTwo_piece hS C hF he)

theorem matrixWith_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {cd : Prog isa}
    (C : CalleeOk S cd (Spec.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p) (hm : p.k*p.ℓ%4=0 ∨ p.k*p.ℓ%4=2) :
    Piece p S (fun σ s => K1 p σ s ∧ s.gpr .x24=1) (KSamp p · (p.k*p.ℓ) 0)
      (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.matrixWith cd P p) := by
  have groups : Piece p S (fun σ s => KSamp p σ 0 0 s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => KSamp p σ (4*(p.k*p.ℓ/4)) 0 s ∧ MatrixPrefixes p σ 4 s)
      (seqR (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.matrixGroup P p) 0 (p.k*p.ℓ/4)) := by
    simpa only [Nat.zero_add,Nat.mul_zero,Nat.mul_add,Nat.mul_one] using
      Piece.seqR (I := fun g σ s => KSamp p σ (4*g) 0 s ∧ MatrixPrefixes p σ 4 s)
        (p.k*p.ℓ/4) 0 (fun g _ hg => matrixGroup_piece hP hF (by omega))
  have tail : Piece p S
      (fun σ s => KSamp p σ (4*(p.k*p.ℓ/4)) 0 s ∧ MatrixPrefixes p σ 4 s)
      (KSamp p · (p.k*p.ℓ) 0)
      (if p.k*p.ℓ%4=2 then VG.Impl.MlDsa.AArch64.KeyGen.Optimized.matrixTwo cd p (4*(p.k*p.ℓ/4))
        else seqR (expA P p) (4*(p.k*p.ℓ/4)) (p.k*p.ℓ%4)) := by
    rcases hm with hm | hm
    · rw [VG.Proof.MlDsa.KeyGen.ifn (by omega),hm]
      refine ⟨fun _ _ _ h => WP.block_nil ?_,RelCT.block_nil (fun _ _ _ => True.intro)⟩
      simpa only [show 4*(p.k*p.ℓ/4)=p.k*p.ℓ by omega] using h.1
    · rw [VG.Proof.MlDsa.KeyGen.ifp hm]
      exact Piece.mono (matrixTwoPhase_piece hP.s64 C hF (by omega))
        (fun _ _ _ h => h) (fun _ _ _ h => by
          simpa only [show 4*(p.k*p.ℓ/4)+2=p.k*p.ℓ by omega] using h.1)
  exact Piece.mono (Piece.seq (matrixPrefixes_piece hF) (Piece.seq groups tail))
    (fun _ _ _ h => KSamp.zero h.1 h.2) (fun _ _ _ h => h)

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
