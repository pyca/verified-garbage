import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedRow
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestPack

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Proof.MlDsa.KeyGen

theorem packSecret_ok {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {σ : State}
    (hp : kgPre p S' σ) {r : Nat} (hr : r < p.ℓ + p.k) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R r 0 0 s) : WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p r) s (KR p σ A S R (r + 1) 0 0) := by
  have L := h.kc.lay hF hp
  have hS := h.sPoly hr
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret Impl.MlDsa.AArch64.KeyGen.Optimized.bitPackAt
  refine WP.mono (bpAt_ok hP.s64 hP.bitPack L (packS_chk hF hr) (bpOk_eta hF) hS.1
    (range_of (eta_le hF) hS (h.small r hr))) fun s' ⟨hP', x', hb⟩ => ?_
  have hle : 128 + lenS p * r + lenS p ≤ oT0 p := by
    simp only [oT0]; rw [Nat.add_assoc, ← Nat.mul_succ]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
  have hk' := h.keep hF hp hP' x' (KRChk.x27 (o := 128 + lenS p * r) (n := lenS p) hF (Nat.le_of_lt hr)
    (Nat.zero_le _) (by omega) (.inr (Nat.le_refl _)) (.inl hle) (by rw [hF.sk]; omega))
  refine ⟨hk'.kc, hk'.x24, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1,
    fun r' hr' => ?_, hk'.rows⟩
  rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
  · exact hk'.packs r' hr'
  · rw [hP'.pa (show Reg.x27 ∈ keptRegs by decide), hb, hS.2,
      Proof.MlDsa.KeyGen.modPm_toRq (small_big (eta_le hF) (h.small r' hr))]

theorem packSecret_tr {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {r : Nat}
    (hr : r < p.ℓ + p.k) : RelCT isa (R p S' (KRx p r 0 0)) (Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p r) fun _ _ => True := by
  refine rel_of (Q := fun x y => Two p S' x y ∧ (Reduced x.mem (pa x (sP p r)) ∧ BpRange x.mem (pa x (sP p r)) p.η p.η) ∧
    (Reduced y.mem (pa y (sP p r)) ∧ BpRange y.mem (pa y (sP p r)) p.η p.η)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨(h₁.sPoly hr).1, range_of (eta_le hF) (h₁.sPoly hr) (h₁.small r hr)⟩,
        ⟨(h₂.sPoly hr).1, range_of (eta_le hF) (h₂.sPoly hr) (h₂.small r hr)⟩⟩
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret Impl.MlDsa.AArch64.KeyGen.Optimized.bitPackAt
  exact bpAt_tr hP.bitPack (kgOk p) (packS_chk hF hr) (bpOk_eta hF) fun x y h =>
    ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem packSecret_piece {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {r : Nat}
    (hr : r < p.ℓ + p.k) : Piece p S' (KRx p r 0 0) (KRx p (r + 1) 0 0) (Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p r) :=
  ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (packSecret_ok hP hF hp hr h) fun _ h => ⟨A, S, R, h⟩, packSecret_tr hP hF hr⟩


end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
