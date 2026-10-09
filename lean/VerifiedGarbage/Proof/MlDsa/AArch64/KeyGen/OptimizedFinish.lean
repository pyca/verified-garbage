import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRow
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Main

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK)
open VG.Spec.Sha3 (bytesAt)

abbrev KRx (p : Params) (np nj nr : Nat) (σ s : State) : Prop :=
  ∃ A S R, PositiveKR p σ A S R np nj nr s

theorem pk_bytes {p : Params} (hF : PFacts p) {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {np nj : Nat} {s : State} (h : PositiveKR p σ A S R np nj p.k s) :
    bytesAt s.mem (pa s (.x26, 0)) p.pkLen = pkK p A S (rhoOf p σ) := by
  have h0 : bytesAt s.mem (s.gpr .x26) 32 = rhoOf p σ := by rw [← pa_zero]; exact h.pk0
  rw [hF.pk, pa_zero, Proof.MlKem.bytesAt_add, h0,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x26) 32 320 p.k, pkK, t1Max_eq]
  exact congrArg _ (flatMap_congr_mem fun i hi => (h.rows i (List.mem_range.mp hi)).1)

theorem sk_bytes {p : Params} (hF : PFacts p) {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {nj : Nat} {s : State} (h : PositiveKR p σ A S R (p.ℓ + p.k) nj p.k s)
    (htr : bytesAt s.mem (pa s (.x27, 64)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64) :
    bytesAt s.mem (pa s (.x27, 0)) p.skLen = skK p A S (rhoOf p σ) (kOf p σ) := by
  have h0 : bytesAt s.mem (s.gpr .x27) 32 = rhoOf p σ := by rw [← pa_zero]; exact h.sk0
  have h1 : bytesAt s.mem (s.gpr .x27 + BitVec.ofNat 64 32) 32 = kOf p σ := h.sk1
  have h2 : bytesAt s.mem (s.gpr .x27 + BitVec.ofNat 64 (32 + 32)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64 :=
    htr
  rw [hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, pa_zero, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x27) (32 + 32 + 64) (lenS p) (p.ℓ + p.k),
    ← oT0, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x27) (oT0 p) 416 p.k, skK]
  rw [flatMap_congr_mem (g := fun r => bitPack (S r) p.η p.η) fun r hr => h.packs r (List.mem_range.mp hr),
    flatMap_congr_mem (g := fun i => bitPack (t0K p A S i) 4095 4096) fun i hi => (h.rows i (List.mem_range.mp hi)).2]
  rfl

/-! ## `tr = H(pk, 64)` -/

/-- At the end: the keys, but for the return. -/
abbrev KFin (p : Params) (σ s : State) : Prop :=
  ∃ A S R, PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ p.k s ∧
    bytesAt s.mem (pa s (.x27, 64)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64

theorem trHash_piece {p : Params} (hF : PFacts p) {S' : Nat} (h16 : 16 ≤ S') (hSl : S' < 2 ^ 64) :
    Piece p S' (KRx p (p.ℓ + p.k) p.ℓ p.k) (KFin p) ((trHashWith keccak.callee) p) := by
  refine ⟨fun σ s hp ⟨A, S, R, h⟩ => ?_, rel_of (Q := Two p S') (trHash_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  unfold trHashWith
  refine WP.mono (shake_ok h16 hSl L (by simp) (trHash_chk hF)) fun s' ⟨hP', x', ho⟩ => ⟨A, S, R, ?_, ?_⟩
  · have hc : KRChk p (p.ℓ + p.k) p.ℓ p.k [((.x28, 0), 200), ((.x28, 200), 640), ((.x27, 64), 64)] :=
      (KRChk.x28 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
        (by rw [hF.scr]; omega)).append (ws₁ := [_])
      ((KRChk.x28 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
        (by rw [hF.scr]; omega)).append (ws₁ := [_])
      (KRChk.x27 hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide))
        (.inl (by simp only [oT0]; omega)) (by rw [hF.sk, oT0]; omega)))
    exact h.keep hF hp hP' x' hc
  · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at ho
    rw [hP'.pa (show Reg.x27 ∈ keptRegs by decide), ho]
    exact congrArg (Spec.MlDsa.H · 64) (pk_bytes hF h)

theorem epi_piece {p : Params} (hF : PFacts p) {S' : Nat} :
    Piece p S' (KFin p) (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p AArch64.abi S').post σ s)
      (.block epi) := by
  refine ⟨fun σ s hp ⟨A, S, R, h, htr⟩ => ?_, rel_of (Q := Two p S') (taintRel [.x28] (fun x y h => h.x28)
    (by taint_decide)) fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ => kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  have hin : InRegions (s.rd ++ s.wr) (σ.gpr .x3 + BitVec.ofNat 64 SV) 48 := by
    have := L.inR (p := svP) (l := 48) (by have := scr_ge hF; lay)
    rwa [pa, h.kc.top.x28] at this
  refine WP.mono (epi_ok h.kc.top hin) fun s' ⟨ha, hr, hm⟩ => ⟨ha, ?_⟩
  sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]
  have e26 : pa s (.x26, 0) = σ.gpr .x1 := by rw [pa_zero, h.kc.top.x26]
  have e27 : pa s (.x27, 0) = σ.gpr .x2 := by rw [pa_zero, h.kc.top.x27]
  rw [hr, h.x24, hm, ← e26, ← e27, pk_bytes hF h, sk_bytes hF h htr]
  exact outcome_of (by have := hF.l; omega) h.good


end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
