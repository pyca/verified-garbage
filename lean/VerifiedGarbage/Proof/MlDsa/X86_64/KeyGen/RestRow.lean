module

public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.RestPack
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.Arith.Representation
import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Base
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlKem.X86_64.FragS

/-!
# ML-DSA key generation on x86-64: the rows of `t`

Row `i` of `t`: `NTT⁻¹` of the sum of the products `Â[i, j] ŝ₁[j]` in `t`, in
one call (`dot_ok`), plus `s₂[i]` (`addS2_ok`), then
`Power2Round` (`p2r_ok`) and `t₁[i]` packed to `pk` and `t₀[i]` to `sk`
(`sbp_ok`, `bp_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG.Proof.MlDsa.Arith.Representation

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc seqR)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv add multiplyNTT bitPack simpleBitPack power2Round ofInt)
open VG.Proof.MlDsa (polyAt natPolyAt coeffAt Reduced PolyIs NatPolyIs)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K)
open VG.Spec.Sha3 (bytesAt)

theorem idx_lt {p : Params} {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k by omega_arith)
  rw [Nat.mul_succ, Nat.mul_comm p.ℓ p.k] at this
  omega_arith

/-- The `t` so far. -/
abbrev tIs (p : Params) (g : (Nat → Poly) → (Nat → IPoly) → Poly) (A : Nat → Poly) (S : Nat → IPoly) (s : State) :
    Prop := PolyIs s.mem (pa s (tP p)) (g A S)

theorem KR.polyA {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nj nr : Nat}
    {s : State} (h : KR p σ A S R np nj nr s) {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    PolyIs s.mem (pa s (aP (p.ℓ * i + j))) (A (p.ℓ * i + j)) := h.aS _ (idx_lt hi hj)

theorem KR.polyS {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nr : Nat}
    {s : State} (h : KR p σ A S R np p.ℓ nr s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem (pa s (sP p j)) (ntt (toRq (S j))) := by
  have := h.s1 j hj; rwa [ifp hj] at this

theorem famP_sc (b j : Nat) : famP (sc (oP b)) j = sc (oP (b + j)) := by
  simp only [famP, sc, oP, Nat.mul_add, Nat.add_assoc]

/-- Entry `j` of row `i` of `Â`, as polynomial `j` of the row. -/
theorem KR.famA {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nj nr : Nat}
    {s : State} (h : KR p σ A S R np nj nr s) {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    PolyIs s.mem (pa s (famP (aP (p.ℓ * i)) j)) (A (p.ℓ * i + j)) := by
  rw [famP_sc]; exact h.aS _ (idx_lt hi hj)

/-- `ŝ₁[j]`, as polynomial `j` of `ŝ₁`. -/
theorem KR.famS {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nr : Nat}
    {s : State} (h : KR p σ A S R np p.ℓ nr s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem (pa s (famP (sP p 0) j)) (ntt (toRq (S j))) := by
  rw [famP_sc, Nat.add_zero]; exact h.polyS hj

theorem l457 {p : Params} (hF : PFacts p) : p.ℓ = 4 ∨ p.ℓ = 5 ∨ p.ℓ = 7 := by
  rcases hF.mem with rfl | rfl | rfl <;> decide

theorem tP_ok {p : Params} (hF : PFacts p) : PtrOk (tP p) :=
  sc_ok _ (by have := hF.kl; have := hF.l; have := hF.k; simp only [oP]; omega_arith)

theorem tP1_ok {p : Params} (hF : PFacts p) : PtrOk (t1P p) :=
  sc_ok _ (by have := hF.kl; have := hF.l; have := hF.k; simp only [oP]; omega_arith)

theorem tP0_ok {p : Params} (hF : PFacts p) : PtrOk (t0P p) :=
  sc_ok _ (by have := hF.kl; have := hF.l; have := hF.k; simp only [oP]; omega_arith)

theorem modPm_t0 (t : Poly) :
    ((t.map fun c => ofInt (power2Round c).2).map fun c => Spec.MlDsa.modPm c.val Spec.MlDsa.q) =
      t.map fun c => (power2Round c).2 := by
  rw [Vector.map_map]
  refine Vector.map_congr_left fun c _ => ?_
  have := Proof.MlDsa.KeyGen.power2Round_snd c
  exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega_arith) (by omega_arith)

theorem packIn_t0 {m : Mem} {q : Addr} {t : Poly} (h : PolyIs m q (t.map fun c => ofInt (power2Round c).2)) :
    PackIn m q 4095 4096 := by
  refine ⟨h.1, fun j hj => ?_⟩
  rw [coeff_val h hj]
  simp only [Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_snd (t[j]'hj)
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega_arith) (by omega_arith)]
  omega_arith

/-! ## The checks of the writes of a row, once each -/

/-- Polynomial `j` of `scratch` after `s₁ ‖ s₂`. -/
theorem chk_poly {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) {j : Nat} (hj : j < 3) :
    KRChk p (p.ℓ + p.k) p.ℓ i [(sc (oP (p.k * p.ℓ + p.ℓ + p.k + j)), 1024)] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact KRChk.rbx hF (by omega_arith) (by omega_arith) (.inr (by simp only [VG.Impl.MlKem.X86_64.oSV, oP]; omega_arith))
    (.inr (by simp only [oP]; omega_arith)) (by simp only [scrLen, Spec.MlDsa.scratchWords, oP]; omega_arith)

theorem chk_t {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) : KRChk p (p.ℓ + p.k) p.ℓ i [(tP p, 1024)] := by
  have := chk_poly hF hi (j := 0) (by decide); rwa [Nat.add_zero] at this

theorem chk_inv {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    KRChk p (p.ℓ + p.k) p.ℓ i [(tP p, 1024), (sc VG.Impl.MlKem.X86_64.oSS, 1024)] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact (chk_t hF hi).append (ws₁ := [_]) (KRChk.rbx (o := VG.Impl.MlKem.X86_64.oSS) (n := 1024) hF (by omega_arith)
    (by omega_arith) (.inr (by decide)) (.inl (by decide))
    (by simp only [scrLen, Spec.MlDsa.scratchWords, VG.Impl.MlKem.X86_64.oSS]; omega_arith))

theorem chk_p2r {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    KRChk p (p.ℓ + p.k) p.ℓ i [(t1P p, 1024), (t0P p, 1024)] :=
  (chk_poly hF hi (j := 1) (by decide)).append (ws₁ := [_]) (chk_poly hF hi (j := 2) (by decide))

theorem chk_sbp {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    KRChk p (p.ℓ + p.k) p.ℓ i [((.r12, 32 + 320 * i), 320)] :=
  KRChk.r12 hF (Nat.le_refl _) (Nat.le_of_lt hi) (Nat.le_refl _) (by rw [hF.pk]; omega_arith)

theorem chk_bp {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    KRChk p (p.ℓ + p.k) p.ℓ i [((.r13, oT0 p + 416 * i), 416)] := by
  have := hF.k; have := hF.l
  refine KRChk.r13 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [oT0]; omega_arith) (.inr (by simp only [oT0]; omega_arith))
    (.inr (Nat.le_refl _)) (by rw [hF.sk]; omega_arith)

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) {i : Nat}
  (hi : i < p.k)
include hP hF hp hi


/-- `t = NTT⁻¹(Σⱼ Â[i, j] ŝ₁[j])`. -/
theorem dot_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State} (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) :
    WP isa (dotInvAt P.asfx (P.dotInv p.ℓ) p.ℓ (tP p) (aP (p.ℓ * i)) (sP p 0)) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => nttInv (dotK p A S i p.ℓ)) A S s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega_arith)
  rw [Nat.add_zero] at hx0
  have S₀ := h.kc.site hF hp
  refine WP.mono (dotInvAt_ok (tP_ok hF) (sc_ok _ (by simp only [oP]; omega_arith))
    (sc_ok _ (by simp only [oP]; omega_arith)) (by layd) (hP.dotInv p.ℓ (l457 hF)) S₀
    (fun j hj => (h.famA hi hj).1) (fun j hj => (h.famS hj).1)) fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(tP p, 1024), (sc VG.Impl.MlKem.X86_64.oSS, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (chk_inv hF hi), ?_⟩
  rw [tIs, hP''.pa (p := tP p) rbx_bases]
  have he : Proof.MlDsa.dotNTT (fun j => polyAt s.mem (pa s (famP (aP (p.ℓ * i)) j)))
      (fun j => polyAt s.mem (pa s (famP (sP p 0) j))) p.ℓ = dotK p A S i p.ℓ := by
    unfold Proof.MlDsa.dotNTT dotK
    refine congrArg (List.foldl Spec.MlDsa.add Spec.MlDsa.zero) (List.map_congr_left fun j hj => ?_)
    rw [List.mem_range] at hj
    dsimp only
    rw [(h.famA hi hj).2, (h.famS hj).2]
  rwa [he] at hb

/-- `t = t + s₂[i]`. -/
theorem addS2_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => nttInv (dotK p A S i p.ℓ)) A S s) :
    WP isa (addAt P.asfx P.add (tP p) (sP p (p.ℓ + i))) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => tK p A S i) A S s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  dsimp only [tIs] at ht
  have S₀ := h.kc.site hF hp
  have hS := h.s2 i hi
  refine WP.mono (addAt_ok (tP_ok hF) (sc_ok _ (by simp only [oP]; omega_arith)) (by layd) (by layd) hP.add S₀ ht.1 hS.1)
    fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(tP p, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (chk_t hF hi), ?_⟩
  rw [tIs, hP''.pa (p := tP p) rbx_bases, Proof.MlDsa.KeyGen.tK, ← hS.2, ← ht.2]
  exact hb

/-- `Power2Round` of `t`. -/
theorem p2r_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => tK p A S i) A S s) :
    WP isa (power2RoundAt P.power2Round (tP p) (t1P p) (t0P p)) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ NatPolyIs s'.mem (pa s' (t1P p)) (t1K p A S i) ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  dsimp only [tIs] at ht
  have S₀ := h.kc.site hF hp
  refine WP.mono (p2rAt_ok (tP_ok hF) (tP1_ok hF) (tP0_ok hF) (by layd) (by layd) (by layd) (by layd) (by layd)
    hP.power2Round S₀ ht.1) fun s' ⟨hP', hx, h1, h0⟩ => ?_
  have hP'' : PPostB s s' [(t1P p, 1024), (t0P p, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (chk_p2r hF hi), ?_, ?_⟩
  · rw [hP''.pa (p := t1P p) rbx_bases, Proof.MlDsa.KeyGen.t1K, ← ht.2]; exact h1
  · rw [hP''.pa (p := t0P p) rbx_bases, ← ht.2]; exact h0

/-- `t₁[i]` to `pk`. -/
theorem sbp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (h1 : NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i))
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)) :
    WP isa (simpleBitPackAt P.simpleBitPack (t1P p) 1023 (.r12, 32 + 320 * i) 320) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
      bytesAt s'.mem (pa s' (.r12, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S₀ := h.kc.site hF hp
  have L := S₀.lay
  refine WP.mono (sbpAt_ok (by decide) (by decide) (tP1_ok hF)
    ⟨by omega_arith, show Reg.r12 ∉ MlKem.X86_64.argRegs by decide⟩ (by layd) (by layd) hP.simpleBitPack S₀
    fun j hj => ?_) fun s' ⟨hP', hx, hb⟩ => ?_
  · rw [show (coeffAt s.mem (pa s (t1P p)) j).toNat = (t1K p A S i)[j]'hj from by
      rw [← h1]; simp only [Proof.MlDsa.natPolyAt, Vector.getElem_ofFn]]
    simp only [Proof.MlDsa.KeyGen.t1K, Vector.getElem_map]
    have := Proof.MlDsa.KeyGen.power2Round_fst ((tK p A S i)[j]'hj)
    omega_arith
  · have hP'' : PPostB s s' [((.r12, 32 + 320 * i), 320)] := hP'.b
    refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (chk_sbp hF hi),
      polyIs_frame' L hP'' (by layd) h0, ?_⟩
    rw [hP''.pa (p := (.r12, 32 + 320 * i)) (show Reg.r12 ∈ bases by decide), hb, h1]

/-- `t₀[i]` to `sk`. -/
theorem bp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s)
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2))
    (h1 : bytesAt s.mem (pa s (.r12, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023) :
    WP isa (bitPackAt P.bitPack (t0P p) 4095 4096 (.r13, oT0 p + 416 * i) 416) s
      (KR p σ A S R (p.ℓ + p.k) p.ℓ (i + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S₀ := h.kc.site hF hp
  have L := S₀.lay
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  refine WP.mono (bpAt_ok (by decide) (by decide) (tP0_ok hF)
    ⟨by rcases hlen with hl | hl <;> simp only [oT0, hl] <;> omega_arith,
      show Reg.r13 ∉ MlKem.X86_64.argRegs by decide⟩ (by layd)
    (by layd) hP.bitPack S₀ (packIn_t0 h0)) fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [((.r13, oT0 p + 416 * i), 416)] := hP'.b
  have hk' := h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (chk_bp hF hi)
  refine ⟨hk'.kc, hk'.r15, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1, hk'.packs,
    fun i' hi' => ?_⟩
  rcases (by omega_arith : i' < i ∨ i' = i) with hi' | rfl
  · exact hk'.rows i' hi'
  · refine ⟨by rw [L.keepBytes hP'' (by layd)]; exact h1, ?_⟩
    rw [hP''.pa (p := (.r13, oT0 p + 416 * i')) (show Reg.r13 ∈ bases by decide), hb, h0.2, modPm_t0]
    rfl

end

theorem t1_bound {m : Mem} {q : Addr} {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {i : Nat}
    (h1 : NatPolyIs m q (t1K p A S i)) : ∀ j < 256, (coeffAt m q j).toNat ≤ 1023 := fun j hj => by
  rw [show (coeffAt m q j).toNat = (t1K p A S i)[j]'hj from by
    rw [← h1]; simp only [Proof.MlDsa.natPolyAt, Vector.getElem_ofFn]]
  simp only [Proof.MlDsa.KeyGen.t1K, Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_fst ((Proof.MlDsa.KeyGen.tK p A S i)[j]'hj)
  omega_arith

/-! ## The pieces of a row -/

/-- In row `i`, with `f` holding of the memory. -/
abbrev RowI (p : Params) (i : Nat) (f : (Nat → Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, KR p σ A S R (p.ℓ + p.k) p.ℓ i s ∧ f A S s

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k)
include hP hF hi

theorem dot_piece : Piece p (KRx p (p.ℓ + p.k) p.ℓ i) (RowI p i (tIs p fun A S => nttInv (dotK p A S i p.ℓ)))
    (dotInvAt P.asfx (P.dotInv p.ℓ) p.ℓ (tP p) (aP (p.ℓ * i)) (sP p 0)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega_arith)
  rw [Nat.add_zero] at hx0
  refine ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (dot_ok hP hF hp hi h) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧
    ((∀ j < p.ℓ, Reduced x.mem (pa x (famP (aP (p.ℓ * i)) j))) ∧ ∀ j < p.ℓ, Reduced x.mem (pa x (famP (sP p 0) j))) ∧
    ((∀ j < p.ℓ, Reduced y.mem (pa y (famP (aP (p.ℓ * i)) j))) ∧ ∀ j < p.ℓ, Reduced y.mem (pa y (famP (sP p 0) j))))
    ?_ fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨fun j hj => (h₁.famA hi hj).1, fun j hj => (h₁.famS hj).1⟩,
        ⟨fun j hj => (h₂.famA hi hj).1, fun j hj => (h₂.famS hj).1⟩⟩
  exact dotInvAt_tr (tP_ok hF) (sc_ok _ (by simp only [oP]; omega_arith)) (sc_ok _ (by simp only [oP]; omega_arith))
    (by layd) (hP.dotInv p.ℓ (l457 hF)) (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide)
    (show Reg.rbx ∈ kgRegs by decide)

theorem addS2_piece : Piece p (RowI p i (tIs p fun A S => nttInv (dotK p A S i p.ℓ)))
    (RowI p i (tIs p fun A S => Proof.MlDsa.KeyGen.tK p A S i)) (addAt P.asfx P.add (tP p) (sP p (p.ℓ + i))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (addS2_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ (Reduced x.mem (pa x (tP p)) ∧ Reduced x.mem (pa x (sP p (p.ℓ + i)))) ∧
    (Reduced y.mem (pa y (tP p)) ∧ Reduced y.mem (pa y (sP p (p.ℓ + i))))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.s2 i hi).1⟩, ⟨t₂.1, (h₂.s2 i hi).1⟩⟩
  exact addAt_tr (tP_ok hF) (sc_ok _ (by simp only [oP]; omega_arith)) (by layd) (by layd) hP.add
    (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide)

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i) ∧
    PolyIs s.mem (pa s (t0P p)) ((Proof.MlDsa.KeyGen.tK p A S i).map fun c => ofInt (power2Round c).2)

theorem p2r_piece : Piece p (RowI p i (tIs p fun A S => Proof.MlDsa.KeyGen.tK p A S i)) (RowI p i (p2rIs p i))
    (power2RoundAt P.power2Round (tP p) (t1P p) (t0P p)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (p2r_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h.1, h.2⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ Reduced x.mem (pa x (tP p)) ∧ Reduced y.mem (pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  exact p2rAt_tr (tP_ok hF) (tP1_ok hF) (tP0_ok hF) (by layd) (by layd) (by layd) (by layd) (by layd) hP.power2Round
    (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide)

/-- After `t₁[i]` to `pk`. -/
abbrev sbpIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  PolyIs s.mem (pa s (t0P p)) ((Proof.MlDsa.KeyGen.tK p A S i).map fun c => ofInt (power2Round c).2) ∧
    bytesAt s.mem (pa s (.r12, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023

theorem sbp_piece : Piece p (RowI p i (p2rIs p i)) (RowI p i (sbpIs p i))
    (simpleBitPackAt P.simpleBitPack (t1P p) 1023 (.r12, 32 + 320 * i) 320) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, h1, h0⟩ => WP.mono (sbp_ok hP hF hp hi h h1 h0) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ (∀ j < 256, (coeffAt x.mem (pa x (t1P p)) j).toNat ≤ 1023) ∧
    (∀ j < 256, (coeffAt y.mem (pa y (t1P p)) j).toNat ≤ 1023)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t1_bound t₁.1, t1_bound t₂.1⟩
  exact sbpAt_tr (by decide) (by decide) (tP1_ok hF) ⟨by omega_arith, show Reg.r12 ∉ MlKem.X86_64.argRegs by decide⟩
    (by layd) (by layd) hP.simpleBitPack (show Reg.rbx ∈ kgRegs by decide)
    (show Reg.r12 ∈ kgRegs by decide)

theorem bp_piece : Piece p (RowI p i (sbpIs p i)) (KRx p (p.ℓ + p.k) p.ℓ (i + 1))
    (bitPackAt P.bitPack (t0P p) 4095 4096 (.r13, oT0 p + 416 * i) 416) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, h0, h1⟩ => WP.mono (bp_ok hP hF hp hi h h0 h1) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ PackIn x.mem (pa x (t0P p)) 4095 4096 ∧
    PackIn y.mem (pa y (t0P p)) 4095 4096) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, packIn_t0 t₁.1, packIn_t0 t₂.1⟩
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  exact bpAt_tr (by decide) (by decide) (tP0_ok hF)
    ⟨by rcases hlen with hl | hl <;> simp only [oT0, hl] <;> omega_arith,
      show Reg.r13 ∉ MlKem.X86_64.argRegs by decide⟩ (by layd)
    (by layd) hP.bitPack (show Reg.rbx ∈ kgRegs by decide) (show Reg.r13 ∈ kgRegs by decide)

end

end VG.Proof.MlDsa.X86_64.KeyGen
