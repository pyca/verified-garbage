module

public import VerifiedGarbage.Proof.MlDsa.Sign.Loop
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Proof.MlDsa.Sign.Leak
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.Framework.InstancePriority
import Batteries.Tactic.Init
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem

/-!
# ML-DSA: signing polynomial by polynomial

An implementation computes the vectors of signing one polynomial at a time, in
buffers of their own: this file states the algorithm's lists as `List.range n`
mapped by a function of the index, for the matrix, the private key, and each
value of an iteration of the signing loop (`yF`, `wF`, `zF`, `hF`, …), so that
`signCommit` (`signCommit_eq`), the validity checks (`iterOut_eq`, with each
norm checked polynomial by polynomial, `passF`) and `signIteration`
(`signIteration_eqF`) read as what the implementation computes. The norm of
`r₀`, a vector of `R` of `LowBits`, is that of its image in `R_q`
(`normR_lowBits`), which the implementation stores.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (foldl_max_lt normZq_lt mem_gamma2s q_eq)

/-! ## Lists by index -/

theorem zipWith_range {α β γ : Type} (f : α → β → γ) (a : Nat → α) (b : Nat → β) (m : Nat) :
    List.zipWith f ((List.range m).map a) ((List.range m).map b) = (List.range m).map fun i => f (a i) (b i) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp

theorem getD_range {α : Type} (f : Nat → α) {m i : Nat} (hi : i < m) (d : α) : ((List.range m).map f).getD i d = f i := by
  simp [hi]

/-! ## Norms -/

theorem normRq_lt_iff (v : List Poly) {B : Nat} (hB : 0 < B) : normRq v < B ↔ ∀ f ∈ v, normRq [f] < B := by
  simp only [normRq, foldl_max_lt, List.mem_flatMap, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  constructor
  · rintro ⟨_, h⟩ f hf
    exact ⟨hB, fun x hx => h x ⟨f, hf, hx⟩⟩
  · intro h
    exact ⟨hB, fun x ⟨f, hf, hx⟩ => (h f hf).2 x hx⟩

theorem normR_lt_iff (v : List IPoly) {B : Nat} (hB : 0 < B) : normR v < B ↔ ∀ f ∈ v, normR [f] < B := by
  simp only [normR, foldl_max_lt, List.mem_flatMap, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  constructor
  · rintro ⟨_, h⟩ f hf
    exact ⟨hB, fun x hx => h x ⟨f, hf, hx⟩⟩
  · intro h
    exact ⟨hB, fun x ⟨f, hf, hx⟩ => (h f hf).2 x hx⟩

theorem normRq_range_lt {m : Nat} (f : Nat → Poly) {B : Nat} (hB : 0 < B) :
    normRq ((List.range m).map f) < B ↔ ∀ i < m, normRq [f i] < B := by
  rw [normRq_lt_iff _ hB]
  simp

/-- `‖x mod q‖∞ = |x|` for `|x| ≤ (q - 1)/2`. -/
theorem modPm_ofInt {x : Int} (h₁ : -((q - 1) / 2 : Nat) ≤ x) (h₂ : x ≤ ((q - 1) / 2 : Nat)) :
    modPm (ofInt x).val q = x := by
  unfold modPm
  dsimp only
  split <;> (rename_i hc; simp only [ofInt, Fin.val_ofNat, q_eq] at *; omega)

theorem normZq_ofInt {x : Int} (h₁ : -((q - 1) / 2 : Nat) ≤ x) (h₂ : x ≤ ((q - 1) / 2 : Nat)) :
    normZq (ofInt x) = x.natAbs := by
  rw [normZq, modPm_ofInt h₁ h₂]

/-- `LowBits(r)` lies in `[-γ₂, γ₂]`. -/
theorem lowBits_range {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (r : Zq) :
    -(γ₂ : Int) ≤ lowBits γ₂ r ∧ lowBits γ₂ r ≤ γ₂ := by
  have hr := r.isLt
  rcases mem_gamma2s h with rfl | rfl <;>
  · simp only [lowBits, decompose, modPm, q_eq] at *
    split <;> split <;> simp only <;> omega

/-- `HighBits(r)` is at most `(q - 1)/(2γ₂) - 1`. -/
theorem highBits_le {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (r : Zq) : (highBits γ₂ r).toNat ≤ (q - 1) / (2 * γ₂) - 1 := by
  rw [VG.Proof.MlDsa.Round.highBits_eq h, Int.toNat_natCast]
  have : 0 < VG.Proof.MlDsa.Round.hbM γ₂ := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have := Nat.mod_lt (VG.Proof.MlDsa.Round.hbF γ₂ r.val) this
  simp only [VG.Proof.MlDsa.Round.hbM] at *
  omega

/-- The norm of a polynomial of `LowBits`, as the implementation stores it in `R_q`. -/
theorem normR_lowBits {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (w : Poly) :
    normR [w.map (lowBits γ₂)] = normRq [w.map fun c => ofInt (lowBits γ₂ c)] := by
  have hq : γ₂ ≤ (q - 1) / 2 := by rcases mem_gamma2s h with rfl | rfl <;> decide
  simp only [normR, normRq, List.flatMap_cons, List.flatMap_nil, List.append_nil, Vector.toList_map, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  have := lowBits_range h c
  simp only [Function.comp]
  rw [normZq_ofInt (by omega) (by omega)]

/-! ## The iteration, polynomial by polynomial -/

section
variable (p : Params) (A : Nat → Nat → Poly) (S1 S2 T0 : Nat → Poly) (μ ρ'' : List Byte) (κ : Nat)

/-- The matrix of the entries `A i j`. -/
def amat : List (List Poly) := (List.range p.k).map fun i => (List.range p.ℓ).map (A i)

/-- `y[r]` of `ExpandMask(ρ″, κ)`. -/
def yF (r : Nat) : IPoly :=
  bitUnpack (H (ρ'' ++ integerToBytes (κ + r) 2) (32 * (1 + bitlen (p.γ₁ - 1)))) (p.γ₁ - 1) p.γ₁

/-- `NTT(y[r])`. -/
def yhF (r : Nat) : Poly := ntt (toRq (yF p ρ'' κ r))

/-- `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])`. -/
def wF (i : Nat) : Poly := nttInv (((List.range p.ℓ).map fun j => multiplyNTT (A i j) (yhF p ρ'' κ j)).foldl add zero)

/-- `w₁[i] = HighBits(w[i])`. -/
def w1F (i : Nat) : Vector Nat n := (wF p A ρ'' κ i).map fun c => (highBits p.γ₂ c).toNat

/-- `c̃ = H(μ ‖ w1Encode(w₁), λ/4)`. -/
def ctF : List Byte := H (μ ++ w1Encode p ((List.range p.k).map (w1F p A ρ'' κ))) p.ctildeLen

theorem signCommit_eq : signCommit p (amat p A) μ ρ'' κ =
    ((List.range p.ℓ).map (yF p ρ'' κ), (List.range p.k).map (wF p A ρ'' κ), ctF p A μ ρ'' κ) := by
  have hy : expandMask p ρ'' κ = (List.range p.ℓ).map (yF p ρ'' κ) := rfl
  have hw : (matrixVectorNTT (amat p A) ((expandMask p ρ'' κ).map fun yi => ntt (toRq yi))).map nttInv =
      (List.range p.k).map (wF p A ρ'' κ) := by
    rw [hy, List.map_map]
    simp only [matrixVectorNTT, amat, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, wF]
    congr 2
    exact zipWith_range multiplyNTT (A i) (fun j => ntt (toRq (yF p ρ'' κ j))) p.ℓ
  simp only [signCommit]
  rw [hw, hy]
  simp only [List.map_map]
  rfl

variable (c : IPoly)

/-- `ĉ = NTT(c)`. -/
def chF : Poly := ntt (toRq c)

/-- `z[r] = y[r] + NTT⁻¹(ĉ ŝ₁[r])`. -/
def zF (r : Nat) : Poly := add (toRq (yF p ρ'' κ r)) (nttInv (multiplyNTT (chF c) (S1 r)))

/-- `w[i] - NTT⁻¹(ĉ ŝ₂[i])`. -/
def w'F (i : Nat) : Poly := sub (wF p A ρ'' κ i) (nttInv (multiplyNTT (chF c) (S2 i)))

/-- `r₀[i] = LowBits(w[i] - cs₂[i])`, in `R_q`. -/
def r0F (i : Nat) : Poly := (w'F p A S2 ρ'' κ c i).map fun x => ofInt (lowBits p.γ₂ x)

/-- `ct₀[i] = NTT⁻¹(ĉ t̂₀[i])`. -/
def ct0F (i : Nat) : Poly := nttInv (multiplyNTT (chF c) (T0 i))

/-- `w[i] - cs₂[i] + ct₀[i]`. -/
def w''F (i : Nat) : Poly := add (w'F p A S2 ρ'' κ c i) (ct0F T0 c i)

/-- `h[i] = MakeHint(-ct₀[i], w[i] - cs₂[i] + ct₀[i])`. -/
def hF (i : Nat) : Vector Bool n := Vector.zipWith (makeHint p.γ₂) (neg (ct0F T0 c i)) (w''F p A S2 T0 ρ'' κ c i)

/-- The validity checks of the iteration, polynomial by polynomial. -/
def passF : Prop :=
  (∀ r < p.ℓ, normRq [zF p S1 ρ'' κ c r] < p.γ₁ - p.β) ∧ (∀ i < p.k, normRq [r0F p A S2 ρ'' κ c i] < p.γ₂ - p.β) ∧
    (∀ i < p.k, normRq [ct0F T0 c i] < p.γ₂) ∧ ((List.range p.k).map fun i => hintOnes [hF p A S2 T0 ρ'' κ c i]).sum ≤ p.ω

instance : Decidable (passF p A S1 S2 T0 ρ'' κ c) := by unfold passF; infer_instance

/-- What the parameter sets have that the checks need. -/
structure ParamsOk (p : Params) : Prop where
  pos₁ : 0 < p.γ₁ - p.β
  pos₂ : 0 < p.γ₂ - p.β
  γ₂ : p.γ₂ ∈ gamma2s

theorem hintOnes_single (h : Vector Bool n) : hintOnes [h] = (h.toList.filter id).length := by
  simp [hintOnes]

theorem iterOut_eq (hp : ParamsOk p) :
    iterOut p ((List.range p.ℓ).map S1) ((List.range p.k).map S2) ((List.range p.k).map T0)
      ((List.range p.ℓ).map (yF p ρ'' κ)) ((List.range p.k).map (wF p A ρ'' κ)) c =
      if passF p A S1 S2 T0 ρ'' κ c then
        some ((List.range p.ℓ).map (zF p S1 ρ'' κ c), (List.range p.k).map (hF p A S2 T0 ρ'' κ c))
      else none := by
  have hγ₂ : 0 < p.γ₂ := by have := hp.pos₂; omega
  simp only [iterOut, List.map_map]
  have ez : addVec ((List.range p.ℓ).map (toRq ∘ yF p ρ'' κ))
      ((List.range p.ℓ).map ((fun s => nttInv (multiplyNTT (ntt (toRq c)) s)) ∘ S1)) =
      (List.range p.ℓ).map (zF p S1 ρ'' κ c) := zipWith_range add _ _ _
  have ew' : subVec ((List.range p.k).map (wF p A ρ'' κ))
      ((List.range p.k).map ((fun s => nttInv (multiplyNTT (ntt (toRq c)) s)) ∘ S2)) =
      (List.range p.k).map (w'F p A S2 ρ'' κ c) := zipWith_range sub _ _ _
  have ect : (List.range p.k).map ((fun t => nttInv (multiplyNTT (ntt (toRq c)) t)) ∘ T0) =
      (List.range p.k).map (ct0F T0 c) := rfl
  have eh : List.zipWith (fun u v => Vector.zipWith (makeHint p.γ₂) u v)
      ((List.range p.k).map (neg ∘ (fun s => nttInv (multiplyNTT (ntt (toRq c)) s)) ∘ T0))
      (addVec ((List.range p.k).map (w'F p A S2 ρ'' κ c)) ((List.range p.k).map (ct0F T0 c))) =
      (List.range p.k).map (hF p A S2 T0 ρ'' κ c) := by
    rw [addVec, zipWith_range add, zipWith_range]; rfl
  rw [ez, ew', ect, List.map_map, eh]
  have c1 : normRq ((List.range p.ℓ).map (zF p S1 ρ'' κ c)) ≥ p.γ₁ - p.β ↔
      ¬ ∀ r < p.ℓ, normRq [zF p S1 ρ'' κ c r] < p.γ₁ - p.β := by
    rw [← normRq_range_lt _ hp.pos₁]; omega
  have c2 : normR ((List.range p.k).map ((fun ri => Vector.map (lowBits p.γ₂) ri) ∘ w'F p A S2 ρ'' κ c)) ≥
      p.γ₂ - p.β ↔ ¬ ∀ i < p.k, normRq [r0F p A S2 ρ'' κ c i] < p.γ₂ - p.β := by
    rw [ge_iff_le, ← Nat.not_lt, normR_lt_iff _ hp.pos₂]
    simp only [List.mem_map, List.mem_range, Function.comp, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, r0F, normR_lowBits hp.γ₂]
  have c3 : normRq ((List.range p.k).map (ct0F T0 c)) ≥ p.γ₂ ↔ ¬ ∀ i < p.k, normRq [ct0F T0 c i] < p.γ₂ := by
    rw [← normRq_range_lt _ hγ₂]; omega
  have c4 : ((List.range p.k).map (hF p A S2 T0 ρ'' κ c)).map (fun hi => (hi.toList.filter id).length) =
      (List.range p.k).map fun i => hintOnes [hF p A S2 T0 ρ'' κ c i] := by
    simp only [List.map_map, hintOnes_single]; rfl
  rw [c4]
  by_cases h1 : ∀ r < p.ℓ, normRq [zF p S1 ρ'' κ c r] < p.γ₁ - p.β
  · by_cases h2 : ∀ i < p.k, normRq [r0F p A S2 ρ'' κ c i] < p.γ₂ - p.β
    · by_cases h3 : ∀ i < p.k, normRq [ct0F T0 c i] < p.γ₂
      · by_cases h4 : ((List.range p.k).map fun i => hintOnes [hF p A S2 T0 ρ'' κ c i]).sum ≤ p.ω
        · rw [ifn (by rw [c1, c2, c3]; rintro (h | h | h | h); exacts [h h1, h h2, h h3, by omega]),
            ifp (show passF p A S1 S2 T0 ρ'' κ c from ⟨h1, h2, h3, h4⟩)]
        · rw [ifp (by rw [c1, c2, c3]; exact .inr (.inr (.inr (by omega)))), ifn (fun h => h4 h.2.2.2)]
      · rw [ifp (by rw [c1, c2, c3]; exact .inr (.inr (.inl h3))), ifn (fun h => h3 h.2.2.1)]
    · rw [ifp (by rw [c1, c2, c3]; exact .inr (.inl h2)), ifn (fun h => h2 h.2.1)]
  · rw [ifp (by rw [c1, c2, c3]; exact .inl h1), ifn (fun h => h1 h.1)]

end

/-- An iteration of the signing loop, polynomial by polynomial. -/
theorem signIteration_eqF {p : Params} (hp : ParamsOk p) (b : Bounds) (A : Nat → Nat → Poly) (S1 S2 T0 : Nat → Poly)
    (μ ρ'' : List Byte) (κ : Nat) :
    signIteration p b (amat p A) ((List.range p.ℓ).map S1) ((List.range p.k).map S2) ((List.range p.k).map T0)
      μ ρ'' κ =
      (sampleInBall p.τ b.ball (ctF p A μ ρ'' κ)).map fun c =>
        (ctF p A μ ρ'' κ, if passF p A S1 S2 T0 ρ'' κ c then
          some ((List.range p.ℓ).map (zF p S1 ρ'' κ c), (List.range p.k).map (hF p A S2 T0 ρ'' κ c)) else none) := by
  rw [signIteration_eq, signCommit_eq]
  dsimp only
  congr 1
  funext c
  rw [iterOut_eq p A S1 S2 T0 ρ'' κ c hp]

/-- Which check rejects an iteration (`signRejectTagC`), polynomial by
polynomial. -/
theorem signRejectTagC_eqF {p : Params} (hp : ParamsOk p) (b : Bounds) (A : Nat → Nat → Poly)
    (S1 S2 T0 : Nat → Poly) (μ ρ'' : List Byte) (κ : Nat) :
    signRejectTagC p b (amat p A) ((List.range p.ℓ).map S1) ((List.range p.k).map S2) ((List.range p.k).map T0)
      μ ρ'' κ =
      match sampleInBall p.τ b.ball (ctF p A μ ρ'' κ) with
      | none => 0
      | some c =>
        if ¬ ∀ r < p.ℓ, normRq [zF p S1 ρ'' κ c r] < p.γ₁ - p.β then 0
        else if ¬ ∀ i < p.k, normRq [r0F p A S2 ρ'' κ c i] < p.γ₂ - p.β then 2
        else if ¬ ∀ i < p.k, normRq [ct0F T0 c i] < p.γ₂ then 3 else 4 := by
  have hγ₂ : 0 < p.γ₂ := by have := hp.pos₂; omega
  unfold signRejectTagC
  rw [signCommit_eq]
  dsimp only
  cases sampleInBall p.τ b.ball (ctF p A μ ρ'' κ) with
  | none => rfl
  | some c =>
    dsimp only
    simp only [List.map_map]
    have ez : addVec ((List.range p.ℓ).map (toRq ∘ yF p ρ'' κ))
        ((List.range p.ℓ).map ((fun s => nttInv (multiplyNTT (ntt (toRq c)) s)) ∘ S1)) =
        (List.range p.ℓ).map (zF p S1 ρ'' κ c) := zipWith_range add _ _ _
    have ew' : subVec ((List.range p.k).map (wF p A ρ'' κ))
        ((List.range p.k).map ((fun s => nttInv (multiplyNTT (ntt (toRq c)) s)) ∘ S2)) =
        (List.range p.k).map (w'F p A S2 ρ'' κ c) := zipWith_range sub _ _ _
    have ect : (List.range p.k).map ((fun t => nttInv (multiplyNTT (ntt (toRq c)) t)) ∘ T0) =
        (List.range p.k).map (ct0F T0 c) := rfl
    rw [ez, ew', ect, List.map_map]
    have c1 : normRq ((List.range p.ℓ).map (zF p S1 ρ'' κ c)) ≥ p.γ₁ - p.β ↔
        ¬ ∀ r < p.ℓ, normRq [zF p S1 ρ'' κ c r] < p.γ₁ - p.β := by
      rw [← normRq_range_lt _ hp.pos₁]; omega
    have c2 : normR ((List.range p.k).map ((fun ri => Vector.map (lowBits p.γ₂) ri) ∘ w'F p A S2 ρ'' κ c)) ≥
        p.γ₂ - p.β ↔ ¬ ∀ i < p.k, normRq [r0F p A S2 ρ'' κ c i] < p.γ₂ - p.β := by
      rw [ge_iff_le, ← Nat.not_lt, normR_lt_iff _ hp.pos₂]
      simp only [List.mem_map, List.mem_range, Function.comp, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, r0F, normR_lowBits hp.γ₂]
    have c3 : normRq ((List.range p.k).map (ct0F T0 c)) ≥ p.γ₂ ↔ ¬ ∀ i < p.k, normRq [ct0F T0 c i] < p.γ₂ := by
      rw [← normRq_range_lt _ hγ₂]; omega
    simp only [c1, c2, c3]

/-- Below `n`, the predicate `q` is false for all `j < k` exactly when `k`
is at most the first `j < n` where it is true. -/
theorem prefix_findIdx (n : Nat) (q : Nat → Bool) {k : Nat} (hk : k ≤ n) :
    (∀ j < k, q j = false) ↔ k ≤ (List.range n).findIdx q := by
  constructor
  · intro h
    refine Nat.le_of_not_lt fun hlt => ?_
    have hl : (List.range n).findIdx q < (List.range n).length := by
      rw [List.length_range]; omega
    have := List.findIdx_getElem (w := hl)
    rw [List.getElem_range, h _ hlt] at this
    cases this
  · intro h j hj
    have := List.not_of_lt_findIdx (Nat.lt_of_lt_of_le hj h)
    rwa [List.getElem_range] at this

/-- `signRejectTag`, polynomial by polynomial: the first polynomial of `z`
or `r₀` that fails its check. -/
theorem signRejectTag_eqF {p : Params} (hp : ParamsOk p) (b : Bounds) (A : Nat → Nat → Poly)
    (S1 S2 T0 : Nat → Poly) (μ ρ'' : List Byte) (κ : Nat) :
    signRejectTag p b (amat p A) ((List.range p.ℓ).map S1) ((List.range p.k).map S2) ((List.range p.k).map T0)
      μ ρ'' κ =
      match sampleInBall p.τ b.ball (ctF p A μ ρ'' κ) with
      | none => 0
      | some c =>
        if ¬ ∀ r < p.ℓ, normRq [zF p S1 ρ'' κ c r] < p.γ₁ - p.β then
          5 * (List.range p.ℓ).findIdx fun r => decide (normRq [zF p S1 ρ'' κ c r] ≥ p.γ₁ - p.β)
        else if ¬ ∀ i < p.k, normRq [r0F p A S2 ρ'' κ c i] < p.γ₂ - p.β then
          2 + 5 * (List.range p.k).findIdx fun i => decide (normRq [r0F p A S2 ρ'' κ c i] ≥ p.γ₂ - p.β)
        else if ¬ ∀ i < p.k, normRq [ct0F T0 c i] < p.γ₂ then 3 else 4 := by
  have hγ₂ : 0 < p.γ₂ := by have := hp.pos₂; omega
  unfold signRejectTag
  rw [signCommit_eq]
  dsimp only
  cases sampleInBall p.τ b.ball (ctF p A μ ρ'' κ) with
  | none => rfl
  | some c =>
    dsimp only
    simp only [List.map_map]
    have ez : addVec ((List.range p.ℓ).map (toRq ∘ yF p ρ'' κ))
        ((List.range p.ℓ).map ((fun s => nttInv (multiplyNTT (ntt (toRq c)) s)) ∘ S1)) =
        (List.range p.ℓ).map (zF p S1 ρ'' κ c) := zipWith_range add _ _ _
    have ew' : subVec ((List.range p.k).map (wF p A ρ'' κ))
        ((List.range p.k).map ((fun s => nttInv (multiplyNTT (ntt (toRq c)) s)) ∘ S2)) =
        (List.range p.k).map (w'F p A S2 ρ'' κ c) := zipWith_range sub _ _ _
    have ect : (List.range p.k).map ((fun t => nttInv (multiplyNTT (ntt (toRq c)) t)) ∘ T0) =
        (List.range p.k).map (ct0F T0 c) := rfl
    rw [ez, ew', ect, List.map_map]
    have c1 : normRq ((List.range p.ℓ).map (zF p S1 ρ'' κ c)) ≥ p.γ₁ - p.β ↔
        ¬ ∀ r < p.ℓ, normRq [zF p S1 ρ'' κ c r] < p.γ₁ - p.β := by
      rw [← normRq_range_lt _ hp.pos₁]; omega
    have c2 : normR ((List.range p.k).map ((fun ri => Vector.map (lowBits p.γ₂) ri) ∘ w'F p A S2 ρ'' κ c)) ≥
        p.γ₂ - p.β ↔ ¬ ∀ i < p.k, normRq [r0F p A S2 ρ'' κ c i] < p.γ₂ - p.β := by
      rw [ge_iff_le, ← Nat.not_lt, normR_lt_iff _ hp.pos₂]
      simp only [List.mem_map, List.mem_range, Function.comp, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, r0F, normR_lowBits hp.γ₂]
    have c3 : normRq ((List.range p.k).map (ct0F T0 c)) ≥ p.γ₂ ↔ ¬ ∀ i < p.k, normRq [ct0F T0 c i] < p.γ₂ := by
      rw [← normRq_range_lt _ hγ₂]; omega
    simp only [c1, c2, c3]
    simp only [List.findIdx_map, Function.comp_def, normR_lowBits hp.γ₂, r0F]
    rfl

end VG.Proof.MlDsa.Sign
