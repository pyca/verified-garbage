import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRow
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRoundTiming

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K)

abbrev RowI (p : Params) (i : Nat) (f : (Nat → Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ i s ∧ f A S s

section
variable {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {i : Nat} (hi : i<p.k)
include hP hF hi

theorem addS2_piece : Piece p S' (RowI p i (tIs p fun A S => nttInv (dotK p A S i p.ℓ)))
    (RowI p i (tIs p fun A S => tK p A S i)) (Impl.MlDsa.AArch64.KeyGen.Optimized.addAt P (tP p) (sP p (p.ℓ + i))) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (addS2_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧
    (Reduced x.mem (pa x (tP p)) ∧ Reduced x.mem (pa x (sP p (p.ℓ + i)))) ∧
    (Reduced y.mem (pa y (tP p)) ∧ Reduced y.mem (pa y (sP p (p.ℓ + i))))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.s2 i hi).1⟩, ⟨t₂.1, (h₂.s2 i hi).1⟩⟩
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.addAt
  exact accAt_tr (op := add) hP.add (kgOk p) (add_chk hF hi) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i) ∧
    PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)

theorem p2r_piece : Piece p S' (RowI p i (tIs p fun A S => tK p A S i)) (RowI p i (p2rIs p i))
    (Impl.MlDsa.AArch64.KeyGen.Optimized.power2RoundAt P (tP p) (t1P p) (t0P p)) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (p2r_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h.1, h.2⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧ Reduced x.mem (pa x (tP p)) ∧ Reduced y.mem (pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  exact p2rAt_tr hP.power2Round (kgOk p) (p2r_chk hF hi) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

/-- After `t₁[i]` to `pk`. -/
abbrev sbpIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
    bytesAt s.mem (pa s (.x26, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023

theorem sbp_piece : Piece p S' (RowI p i (p2rIs p i)) (RowI p i (sbpIs p i))
    (Impl.MlDsa.AArch64.KeyGen.Optimized.simpleBitPackAt P (t1P p) 1023 (.x26, 32 + 320 * i) 320) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, h1, h0⟩ => WP.mono (sbp_ok hP hF hp hi h h1 h0) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧ (∀ j < 256, (coeffAt x.mem (pa x (t1P p)) j).toNat ≤ 1023) ∧
    (∀ j < 256, (coeffAt y.mem (pa y (t1P p)) j).toNat ≤ 1023)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t1_bound t₁.1, t1_bound t₂.1⟩
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.simpleBitPackAt
  exact sbpAt_tr hP.simpleBitPack (kgOk p) (sbp_chk hF hi) sbpOk_t1 fun x y h =>
    ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem bp_piece : Piece p S' (RowI p i (sbpIs p i)) (KRx p (p.ℓ + p.k) p.ℓ (i + 1))
    (Impl.MlDsa.AArch64.KeyGen.Optimized.bitPackAt P (t0P p) 4095 4096 (.x27, oT0 p + 416 * i) 416) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, h0, h1⟩ => WP.mono (bp_ok hP hF hp hi h h0 h1) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧
    (Reduced x.mem (pa x (t0P p)) ∧ BpRange x.mem (pa x (t0P p)) 4095 4096) ∧
    (Reduced y.mem (pa y (t0P p)) ∧ BpRange y.mem (pa y (t0P p)) 4095 4096)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1.1, range_t0 t₁.1⟩, ⟨t₂.1.1, range_t0 t₂.1⟩⟩
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.bitPackAt
  exact bpAt_tr hP.bitPack (kgOk p) (bp_chk hF hi) bpOk_t0 fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

end
end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
