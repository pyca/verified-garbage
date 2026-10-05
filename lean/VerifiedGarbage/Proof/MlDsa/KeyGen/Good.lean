import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Proof.MlKem.KPke1024

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.KeyGen.Mono`. -/
section

/-!
# ML-DSA key generation: larger bounds give the same result

The XOF output a sampler draws within a larger bound extends the output within
a smaller one (`H_take`, `G_take`), so a sampler that finishes within a bound
finishes with the same result within any larger one (`rejNTTPoly_mono`,
`rejBoundedPoly_mono`), and so does `ML-DSA.KeyGen_internal`
(`keyGenInternal_mono`).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa
open VG.Spec.Sha3 (squeeze)

theorem ifp {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ifn {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-! ## The XOFs -/

theorem squeeze_take {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : Spec.Sha3.State) {d d' : Nat}
    (h : d ≤ d') : (squeeze rate S d').take d = squeeze rate S d :=
  List.ext_getElem (by rw [List.length_take, Proof.Sha3.length_squeeze hr hr', Proof.Sha3.length_squeeze hr hr']; omega)
    fun i h₁ h₂ => by
      rw [List.getElem_take, Proof.Sha3.squeeze_getElem hr hr' _ (by rw [List.length_take] at h₁; omega),
        Proof.Sha3.squeeze_getElem hr hr' _ (by rw [Proof.Sha3.length_squeeze hr hr'] at h₂; exact h₂)]

theorem H_eq (s : List Byte) (d : Nat) :
    VG.Spec.MlDsa.H s d = squeeze 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix s)) d := rfl

theorem G_eq (s : List Byte) (d : Nat) :
    VG.Spec.MlDsa.G s d = squeeze 168 (Spec.Sha3.absorb 168 (Spec.Sha3.pad 168 Spec.Sha3.shakeSuffix s)) d := rfl

theorem H_length (s : List Byte) (d : Nat) : (VG.Spec.MlDsa.H s d).length = d := by
  rw [VG.Proof.MlDsa.KeyGen.H_eq]; exact Proof.Sha3.length_squeeze (by decide) (by decide) _ _

theorem G_length (s : List Byte) (d : Nat) : (VG.Spec.MlDsa.G s d).length = d := by
  rw [VG.Proof.MlDsa.KeyGen.G_eq]; exact Proof.Sha3.length_squeeze (by decide) (by decide) _ _

theorem H_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (VG.Spec.MlDsa.H s d').take d = VG.Spec.MlDsa.H s d := by
  rw [VG.Proof.MlDsa.KeyGen.H_eq, VG.Proof.MlDsa.KeyGen.H_eq]; exact VG.Proof.MlDsa.KeyGen.squeeze_take (by decide) (by decide) _ h

theorem G_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (VG.Spec.MlDsa.G s d').take d = VG.Spec.MlDsa.G s d := by
  rw [VG.Proof.MlDsa.KeyGen.G_eq, VG.Proof.MlDsa.KeyGen.G_eq]; exact VG.Proof.MlDsa.KeyGen.squeeze_take (by decide) (by decide) _ h

theorem H_append (s : List Byte) {d d' : Nat} (h : d ≤ d') : VG.Spec.MlDsa.H s d' = VG.Spec.MlDsa.H s d ++ (VG.Spec.MlDsa.H s d').drop d := by
  rw [← VG.Proof.MlDsa.KeyGen.H_take s h, List.take_append_drop]

theorem G_append (s : List Byte) {d d' : Nat} (h : d ≤ d') : VG.Spec.MlDsa.G s d' = VG.Spec.MlDsa.G s d ++ (VG.Spec.MlDsa.G s d').drop d := by
  rw [← VG.Proof.MlDsa.KeyGen.G_take s h, List.take_append_drop]

/-! ## The loops -/

theorem rejNTTLoop_done {a : List VG.Spec.MlDsa.Zq} (h : VG.Spec.MlDsa.n ≤ a.length) : ∀ l, rejNTTLoop a l = some a
  | _ :: _ :: _ :: _ => by rw [rejNTTLoop, VG.Proof.MlDsa.KeyGen.ifp h]
  | [] => by rw [rejNTTLoop.eq_2 _ _ (by simp), VG.Proof.MlDsa.KeyGen.ifp h]
  | [_] => by rw [rejNTTLoop.eq_2 _ _ (by simp), VG.Proof.MlDsa.KeyGen.ifp h]
  | [_, _] => by rw [rejNTTLoop.eq_2 _ _ (by simp), VG.Proof.MlDsa.KeyGen.ifp h]

theorem rejNTTLoop_append : ∀ (a : List VG.Spec.MlDsa.Zq) (l l' : List Byte) {r : List VG.Spec.MlDsa.Zq},
    rejNTTLoop a l = some r → rejNTTLoop a (l ++ l') = some r
  | a, s₀ :: s₁ :: s₂ :: out, l', r, h => by
    rw [rejNTTLoop] at h
    rw [List.cons_append, List.cons_append, List.cons_append, rejNTTLoop]
    split at h
    · rw [VG.Proof.MlDsa.KeyGen.ifp ‹_›]; exact h
    · rw [VG.Proof.MlDsa.KeyGen.ifn ‹_›]; exact VG.Proof.MlDsa.KeyGen.rejNTTLoop_append _ out l' h
  | a, [], l', r, h | a, [_], l', r, h | a, [_, _], l', r, h => by
    rw [rejNTTLoop.eq_2 _ _ (by simp)] at h
    split at h
    · cases h; exact VG.Proof.MlDsa.KeyGen.rejNTTLoop_done ‹_› _
    · cases h

theorem rejBoundedLoop_done {η : Nat} {a : List Int} (h : VG.Spec.MlDsa.n ≤ a.length) : ∀ l, rejBoundedLoop η a l = some a
  | [] => by rw [rejBoundedLoop, VG.Proof.MlDsa.KeyGen.ifp h]
  | _ :: _ => by rw [rejBoundedLoop, VG.Proof.MlDsa.KeyGen.ifp h]

theorem rejBoundedLoop_append {η : Nat} : ∀ (a : List Int) (l l' : List Byte) {r : List Int},
    rejBoundedLoop η a l = some r → rejBoundedLoop η a (l ++ l') = some r
  | a, [], l', r, h => by
    rw [rejBoundedLoop] at h
    split at h
    · cases h; exact VG.Proof.MlDsa.KeyGen.rejBoundedLoop_done ‹_› _
    · cases h
  | a, z :: out, l', r, h => by
    rw [rejBoundedLoop] at h
    rw [List.cons_append, rejBoundedLoop]
    split at h
    · rw [VG.Proof.MlDsa.KeyGen.ifp ‹_›]; exact h
    · rw [VG.Proof.MlDsa.KeyGen.ifn ‹_›]; exact VG.Proof.MlDsa.KeyGen.rejBoundedLoop_append _ out l' h

/-! ## The samplers -/

theorem rejNTTPoly_mono {b b' : Nat} (h : b ≤ b') {ρ : List Byte} {x : VG.Spec.MlDsa.Poly}
    (hx : rejNTTPoly b ρ = some x) : rejNTTPoly b' ρ = some x := by
  unfold rejNTTPoly at hx ⊢
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hx
  rw [VG.Proof.MlDsa.KeyGen.G_append ρ h, VG.Proof.MlDsa.KeyGen.rejNTTLoop_append _ _ _ ha]
  rfl

theorem rejBoundedPoly_mono {η b b' : Nat} (h : b ≤ b') {ρ : List Byte} {x : IPoly}
    (hx : rejBoundedPoly η b ρ = some x) : rejBoundedPoly η b' ρ = some x := by
  unfold rejBoundedPoly at hx ⊢
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hx
  rw [VG.Proof.MlDsa.KeyGen.H_append ρ h, VG.Proof.MlDsa.KeyGen.rejBoundedLoop_append _ _ _ ha]
  rfl

/-! ## Bounds -/

/-- `b` is at most `b'` on every loop. -/
structure Bounds.Le (b b' : Bounds) : Prop where
  sign : b.sign ≤ b'.sign
  rejBounded : b.rejBounded ≤ b'.rejBounded
  rejNTT : b.rejNTT ≤ b'.rejNTT
  ball : b.ball ≤ b'.ball

/-- The larger of two bounds on every loop. -/
def bmax (b b' : Bounds) : Bounds :=
  { sign := Nat.max b.sign b'.sign, rejBounded := Nat.max b.rejBounded b'.rejBounded,
    rejNTT := Nat.max b.rejNTT b'.rejNTT, ball := Nat.max b.ball b'.ball }

theorem Bounds.le_max_left (b b' : Bounds) : Bounds.Le b (VG.Proof.MlDsa.KeyGen.bmax b b') :=
  ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩

theorem Bounds.le_max_right (b b' : Bounds) : Bounds.Le b' (VG.Proof.MlDsa.KeyGen.bmax b b') :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _⟩

/-! ## `mapM` in `Option` -/

theorem mapM_some {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x (List.mem_cons_self ..), VG.Proof.MlDsa.KeyGen.mapM_some fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem mapM_none {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∃ x ∈ l, f x = none) → l.mapM f = none
  | [], ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | x :: l, ⟨y, hy, hn⟩ => by
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hn]; rfl
    · cases e : f x with
      | none => rfl
      | some _ => rw [VG.Proof.MlDsa.KeyGen.mapM_none ⟨y, hy, hn⟩]; rfl

theorem mapM_mono {α β : Type} {f g : α → Option β} (hfg : ∀ x y, f x = some y → g x = some y) :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → l.mapM g = some r
  | [], _, h => h
  | x :: l, r, h => by
    rw [List.mapM_cons] at h ⊢
    cases e : f x with
    | none => rw [e] at h; cases h
    | some y =>
      rw [e] at h
      cases e' : l.mapM f with
      | none => rw [e'] at h; cases h
      | some ys =>
        rw [e'] at h
        rw [hfg x y e, VG.Proof.MlDsa.KeyGen.mapM_mono hfg e']
        exact h

/-! ## `ExpandA`, `ExpandS` and key generation -/

/-- The seed of `Â[r, s]`. -/
abbrev seedA (ρ : List Byte) (r s : Nat) : List Byte := ρ ++ integerToBytes s 1 ++ integerToBytes r 1

/-- The seed of entry `r` of `s₁ ‖ s₂`. -/
abbrev seedS (ρ' : List Byte) (r : Nat) : List Byte := ρ' ++ integerToBytes r 2

theorem expandA_mono {p : VG.Spec.MlDsa.Params} {b b' : Bounds} (h : Bounds.Le b b') {ρ : List Byte} {x : List (List VG.Spec.MlDsa.Poly)}
    (hx : expandA p b ρ = some x) : expandA p b' ρ = some x :=
  VG.Proof.MlDsa.KeyGen.mapM_mono (fun _ _ hr => VG.Proof.MlDsa.KeyGen.mapM_mono (fun _ _ hs => VG.Proof.MlDsa.KeyGen.rejNTTPoly_mono h.rejNTT hs) hr) hx

theorem expandS_eq (p : VG.Spec.MlDsa.Params) (b : Bounds) (ρ : List Byte) :
    expandS p b ρ = ((List.range p.ℓ).mapM fun r => rejBoundedPoly p.η b.rejBounded (VG.Proof.MlDsa.KeyGen.seedS ρ r)).bind
      fun s₁ => ((List.range p.k).mapM fun r => rejBoundedPoly p.η b.rejBounded (VG.Proof.MlDsa.KeyGen.seedS ρ (r + p.ℓ))).map
        fun s₂ => (s₁, s₂) := by
  unfold expandS
  cases (List.range p.ℓ).mapM fun r => rejBoundedPoly p.η b.rejBounded (VG.Proof.MlDsa.KeyGen.seedS ρ r) with
  | none => rfl
  | some s₁ =>
    cases (List.range p.k).mapM fun r => rejBoundedPoly p.η b.rejBounded (VG.Proof.MlDsa.KeyGen.seedS ρ (r + p.ℓ)) with
    | none => rfl
    | some s₂ => rfl

theorem expandS_mono {p : VG.Spec.MlDsa.Params} {b b' : Bounds} (h : Bounds.Le b b') {ρ : List Byte} {x : List IPoly × List IPoly}
    (hx : expandS p b ρ = some x) : expandS p b' ρ = some x := by
  rw [VG.Proof.MlDsa.KeyGen.expandS_eq] at hx ⊢
  obtain ⟨s₁, h₁, hx⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨s₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp hx
  rw [VG.Proof.MlDsa.KeyGen.mapM_mono (fun _ _ hs => VG.Proof.MlDsa.KeyGen.rejBoundedPoly_mono h.rejBounded hs) h₁, Option.bind_some,
    VG.Proof.MlDsa.KeyGen.mapM_mono (fun _ _ hs => VG.Proof.MlDsa.KeyGen.rejBoundedPoly_mono h.rejBounded hs) h₂]
  rfl

/-- `ExpandA` when every entry is sampled. -/
theorem expandA_some {p : VG.Spec.MlDsa.Params} {b : Bounds} {ρ : List Byte} {A : Nat → Nat → VG.Spec.MlDsa.Poly}
    (h : ∀ r < p.k, ∀ s < p.ℓ, rejNTTPoly b.rejNTT (VG.Proof.MlDsa.KeyGen.seedA ρ r s) = some (A r s)) :
    expandA p b ρ = some ((List.range p.k).map fun r => (List.range p.ℓ).map fun s => A r s) :=
  VG.Proof.MlDsa.KeyGen.mapM_some fun r hr => VG.Proof.MlDsa.KeyGen.mapM_some fun s hs => h r (List.mem_range.mp hr) s (List.mem_range.mp hs)

theorem expandA_none {p : VG.Spec.MlDsa.Params} {b : Bounds} {ρ : List Byte}
    (h : ∃ r < p.k, ∃ s < p.ℓ, rejNTTPoly b.rejNTT (VG.Proof.MlDsa.KeyGen.seedA ρ r s) = none) : expandA p b ρ = none := by
  obtain ⟨r, hr, s, hs, hn⟩ := h
  exact VG.Proof.MlDsa.KeyGen.mapM_none ⟨r, List.mem_range.mpr hr, VG.Proof.MlDsa.KeyGen.mapM_none ⟨s, List.mem_range.mpr hs, hn⟩⟩

/-- `ExpandS` when every entry is sampled. -/
theorem expandS_some {p : VG.Spec.MlDsa.Params} {b : Bounds} {ρ' : List Byte} {S : Nat → IPoly}
    (h : ∀ r < p.ℓ + p.k, rejBoundedPoly p.η b.rejBounded (VG.Proof.MlDsa.KeyGen.seedS ρ' r) = some (S r)) :
    expandS p b ρ' = some ((List.range p.ℓ).map S, (List.range p.k).map fun r => S (r + p.ℓ)) := by
  rw [VG.Proof.MlDsa.KeyGen.expandS_eq, VG.Proof.MlDsa.KeyGen.mapM_some (g := S) fun r hr => h r (by have := List.mem_range.mp hr; omega),
    Option.bind_some, VG.Proof.MlDsa.KeyGen.mapM_some (g := fun r => S (r + p.ℓ)) fun r hr => h (r + p.ℓ) (by have := List.mem_range.mp hr; omega)]
  rfl

theorem expandS_none {p : VG.Spec.MlDsa.Params} {b : Bounds} {ρ' : List Byte}
    (h : ∃ r < p.ℓ + p.k, rejBoundedPoly p.η b.rejBounded (VG.Proof.MlDsa.KeyGen.seedS ρ' r) = none) : expandS p b ρ' = none := by
  obtain ⟨r, hr, hn⟩ := h
  rw [VG.Proof.MlDsa.KeyGen.expandS_eq]
  by_cases hl : r < p.ℓ
  · rw [VG.Proof.MlDsa.KeyGen.mapM_none ⟨r, List.mem_range.mpr hl, hn⟩]; rfl
  · rw [VG.Proof.MlDsa.KeyGen.mapM_none (l := List.range p.k) ⟨r - p.ℓ, List.mem_range.mpr (by omega), by rw [Nat.sub_add_cancel (by omega)]; exact hn⟩]
    cases (List.mapM _ _ : Option (List IPoly)) <;> rfl

/-- `ML-DSA.KeyGen_internal` after `ExpandA` and `ExpandS`: lines 5–10 of Algorithm 6. -/
def kgRest (p : VG.Spec.MlDsa.Params) (ρ K : List Byte) (Â : List (List VG.Spec.MlDsa.Poly)) (s₁ s₂ : List IPoly) : List Byte × List Byte :=
  let ŝ₁ := s₁.map fun s => VG.Spec.MlDsa.ntt (toRq s)
  let t := VG.Spec.MlDsa.addVec ((matrixVectorNTT Â ŝ₁).map VG.Spec.MlDsa.nttInv) (s₂.map toRq)
  let t₁ := t.map fun ti => ti.map fun c => (power2Round c).1.toNat
  let t₀ := t.map fun ti => ti.map fun c => (power2Round c).2
  let pk := pkEncode ρ t₁
  (pk, skEncode p ρ K (VG.Spec.MlDsa.H pk 64) s₁ s₂ t₀)

theorem keyGenInternal_eq (p : VG.Spec.MlDsa.Params) (b : Bounds) (ξ : List Byte) :
    VG.Spec.MlDsa.keyGenInternal p b ξ =
      (expandA p b (keyGenSeeds p ξ).1).bind fun Â => (expandS p b (keyGenSeeds p ξ).2.1).map fun s =>
        VG.Proof.MlDsa.KeyGen.kgRest p (keyGenSeeds p ξ).1 (keyGenSeeds p ξ).2.2 Â s.1 s.2 := by
  unfold VG.Spec.MlDsa.keyGenInternal keyGenSeeds
  dsimp only
  cases expandA p b (List.take 32 (VG.Spec.MlDsa.H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128)) with
  | none => rfl
  | some Â =>
    cases expandS p b (List.take 64 (List.drop 32 (VG.Spec.MlDsa.H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128))) with
    | none => rfl
    | some s => rfl

theorem keyGenInternal_mono {p : VG.Spec.MlDsa.Params} {b b' : Bounds} (h : Bounds.Le b b') {ξ : List Byte}
    {x : List Byte × List Byte} (hx : VG.Spec.MlDsa.keyGenInternal p b ξ = some x) : VG.Spec.MlDsa.keyGenInternal p b' ξ = some x := by
  rw [VG.Proof.MlDsa.KeyGen.keyGenInternal_eq] at hx ⊢
  obtain ⟨Â, hA, hx⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨s, hS, rfl⟩ := Option.map_eq_some_iff.mp hx
  rw [VG.Proof.MlDsa.KeyGen.expandA_mono h hA, Option.bind_some, VG.Proof.MlDsa.KeyGen.expandS_mono h hS]
  rfl

end VG.Proof.MlDsa.KeyGen

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa

/-- Key generation fails within the least bounds if an entry of `Â` does. -/
theorem keyGenInternal_none_A {p : VG.Spec.MlDsa.Params} {ξ : List Byte} {r s : Nat} (hr : r < p.k) (hs : s < p.ℓ)
    (h : rejNTTPoly minBounds.rejNTT (VG.Proof.MlDsa.KeyGen.seedA (keyGenSeeds p ξ).1 r s) = none) : VG.Spec.MlDsa.keyGenInternal p minBounds ξ = none := by
  rw [VG.Proof.MlDsa.KeyGen.keyGenInternal_eq, VG.Proof.MlDsa.KeyGen.expandA_none ⟨r, hr, s, hs, h⟩]; rfl

/-- Key generation fails within the least bounds if an entry of `s₁ ‖ s₂` does. -/
theorem keyGenInternal_none_S {p : VG.Spec.MlDsa.Params} {ξ : List Byte} {r : Nat} (hr : r < p.ℓ + p.k)
    (h : rejBoundedPoly p.η minBounds.rejBounded (VG.Proof.MlDsa.KeyGen.seedS (keyGenSeeds p ξ).2.1 r) = none) :
    VG.Spec.MlDsa.keyGenInternal p minBounds ξ = none := by
  rw [VG.Proof.MlDsa.KeyGen.keyGenInternal_eq, VG.Proof.MlDsa.KeyGen.expandS_none ⟨r, hr, h⟩]
  cases expandA p minBounds (keyGenSeeds p ξ).1 <;> rfl

end VG.Proof.MlDsa.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.KeyGen.Poly`. -/
section

/-!
# ML-DSA key generation: coefficients and polynomials in memory

`mod± q` inverts the cast of a small integer to `ℤ_q` (`modPm_ofInt`), and the
cast inverts `mod± q` (`ofInt_modPm`); the ranges of the coefficients
`RejBoundedPoly` samples (`rejBoundedPoly_range`) and of `Power2Round`
(`power2Round_fst`, `power2Round_snd`); and ML-DSA's polynomials in memory
(`Spec/MlDsa/Poly.lean`) depend only on their 1024 bytes (`polyAt_congr`,
`polyIs_frame`, …).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `mod± q` and the cast to `ℤ_q` -/

theorem ofInt_val (x : Int) : ((ofInt x).val : Int) = x % 8380417 := by
  have h1 := Int.emod_nonneg x (show (8380417 : Int) ≠ 0 by decide)
  have h2 := Int.emod_lt_of_pos x (show (0 : Int) < 8380417 by decide)
  have hq : ((q : Nat) : Int) = 8380417 := rfl
  simp only [ofInt, Fin.val_ofNat]
  rw [Int.natCast_emod, hq, Int.toNat_of_nonneg (by rw [← hq]; exact h1)]
  omega

theorem modPm_q (m : Int) : modPm m q = if m % 8380417 > 4190208 then m % 8380417 - 8380417 else m % 8380417 := rfl

/-- `mod± q` of a small integer cast to `ℤ_q` is the integer. -/
theorem modPm_ofInt {x : Int} (h₁ : -4190208 ≤ x) (h₂ : x ≤ 4190208) : modPm (ofInt x).val q = x := by
  rw [VG.Proof.MlDsa.KeyGen.modPm_q, VG.Proof.MlDsa.KeyGen.ofInt_val]
  split <;> omega

/-- The cast of `mod± q` of an element of `ℤ_q` is the element. -/
theorem ofInt_modPm (c : Zq) : ofInt (modPm c.val q) = c := by
  apply Fin.ext
  have hc : c.val < 8380417 := c.isLt
  have key : modPm c.val q % 8380417 = c.val := by rw [VG.Proof.MlDsa.KeyGen.modPm_q]; split <;> omega
  have h := VG.Proof.MlDsa.KeyGen.ofInt_val (modPm c.val q)
  rw [key] at h
  exact_mod_cast h

theorem toRq_modPm (f : Poly) : toRq (f.map fun c => modPm c.val q) = f := by
  unfold toRq
  rw [Vector.map_map]
  exact (Vector.map_congr_left fun c _ => VG.Proof.MlDsa.KeyGen.ofInt_modPm c).trans (Vector.map_id f)

theorem modPm_toRq {f : IPoly} (h : ∀ c ∈ f.toList, -4190208 ≤ c ∧ c ≤ 4190208) :
    (toRq f).map (fun c => modPm c.val q) = f := by
  unfold toRq
  rw [Vector.map_map]
  refine (Vector.map_congr_left fun c hc => ?_).trans (Vector.map_id f)
  exact VG.Proof.MlDsa.KeyGen.modPm_ofInt (h c (Vector.mem_toList_iff.mpr hc)).1 (h c (Vector.mem_toList_iff.mpr hc)).2

/-! ## Ranges -/

theorem coeffFromHalfByte_range {η b : Nat} {v : Int} (h : coeffFromHalfByte η b = some v) :
    -(η : Int) ≤ v ∧ v ≤ η := by
  unfold coeffFromHalfByte at h
  split at h
  · rename_i hc; cases h; obtain ⟨rfl, _⟩ := hc; omega
  · split at h
    · rename_i hc; cases h; obtain ⟨rfl, _⟩ := hc; omega
    · cases h

theorem rejBoundedLoop_range {η : Nat} : ∀ {a : List Int} {l : List Byte} {r : List Int},
    (∀ c ∈ a, -(η : Int) ≤ c ∧ c ≤ η) → rejBoundedLoop η a l = some r → ∀ c ∈ r, -(η : Int) ≤ c ∧ c ≤ η
  | a, [], r, ha, h => by
    rw [rejBoundedLoop] at h
    split at h
    · cases h; exact ha
    · cases h
  | a, z :: out, r, ha, h => by
    rw [rejBoundedLoop] at h
    split at h
    · cases h; exact ha
    · refine VG.Proof.MlDsa.KeyGen.rejBoundedLoop_range (fun c hc => ?_) h
      have r1 := @VG.Proof.MlDsa.KeyGen.coeffFromHalfByte_range η (z.toNat % 16)
      have r2 := @VG.Proof.MlDsa.KeyGen.coeffFromHalfByte_range η (z.toNat / 16)
      revert hc r1 r2
      generalize coeffFromHalfByte η (z.toNat % 16) = o1
      generalize coeffFromHalfByte η (z.toNat / 16) = o2
      intro hc r1 r2
      cases o1 <;> cases o2 <;> simp only at hc
      · exact ha c hc
      · split at hc
        · rcases List.mem_append.mp hc with hc | hc
          · exact ha c hc
          · rw [List.mem_singleton.mp hc]; exact r2 rfl
        · exact ha c hc
      · rcases List.mem_append.mp hc with hc | hc
        · exact ha c hc
        · rw [List.mem_singleton.mp hc]; exact r1 rfl
      · split at hc
        · rcases List.mem_append.mp hc with hc | hc
          · rcases List.mem_append.mp hc with hc | hc
            · exact ha c hc
            · rw [List.mem_singleton.mp hc]; exact r1 rfl
          · rw [List.mem_singleton.mp hc]; exact r2 rfl
        · rcases List.mem_append.mp hc with hc | hc
          · exact ha c hc
          · rw [List.mem_singleton.mp hc]; exact r1 rfl

theorem rejBoundedPoly_range {η b : Nat} {ρ : List Byte} {x : IPoly} (h : rejBoundedPoly η b ρ = some x) :
    ∀ c ∈ x.toList, -(η : Int) ≤ c ∧ c ≤ η := by
  unfold rejBoundedPoly at h
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  have hr := VG.Proof.MlDsa.KeyGen.rejBoundedLoop_range (fun _ h => absurd h List.not_mem_nil) ha
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  simp only [Vector.getElem_toList, Vector.getElem_ofFn, List.getD_eq_getElem?_getD]
  cases e : a[i]? with
  | none => simp
  | some v => exact hr v (List.mem_of_getElem? e)

theorem power2Round_fst (c : Zq) : 0 ≤ (power2Round c).1 ∧ (power2Round c).1 ≤ 1023 := by
  have hc : c.val < 8380417 := c.isLt
  have h2 : ((2 ^ 13 : Nat) : Int) = 8192 := rfl
  simp only [power2Round, modPm, d, h2]
  split <;> omega

theorem power2Round_snd (c : Zq) : -4095 ≤ (power2Round c).2 ∧ (power2Round c).2 ≤ 4096 := by
  have h2 : ((2 ^ 13 : Nat) : Int) = 8192 := rfl
  simp only [power2Round, modPm, d, h2]
  split <;> omega

/-! ## Polynomials -/

theorem add_zero_left (f : Poly) : add zero f = f :=
  Vector.ext fun i hi => by simp [add, zero]

/-! ## Polynomials in memory -/

theorem coeffAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) {i : Nat} (hi : i < n) :
    coeffAt m' p i = coeffAt m p i := by
  refine Mem.readW_congr fun k hk => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by change i < 256 at hi; omega)

theorem polyAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    polyAt m' p = polyAt m p :=
  Vector.ext fun i hi => by simp only [polyAt, Vector.getElem_ofFn, VG.Proof.MlDsa.KeyGen.coeffAt_congr h hi]

theorem natPolyAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    natPolyAt m' p = natPolyAt m p :=
  Vector.ext fun i hi => by simp only [natPolyAt, Vector.getElem_ofFn, VG.Proof.MlDsa.KeyGen.coeffAt_congr h hi]

theorem reduced_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hr : Reduced m p) :
    Reduced m' p := fun i hi => by rw [VG.Proof.MlDsa.KeyGen.coeffAt_congr h hi]; exact hr i hi

theorem polyIs_congr {m m' : Mem} {p : Addr} {f : Poly}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hf : PolyIs m p f) :
    PolyIs m' p f := ⟨VG.Proof.MlDsa.KeyGen.reduced_congr h hf.1, (VG.Proof.MlDsa.KeyGen.polyAt_congr h).trans hf.2⟩

theorem bytes_of_bytesAt {m m' : Mem} {p : Addr} (h : bytesAt m' p 1024 = bytesAt m p 1024) :
    ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) := fun k hk => by
  have : (bytesAt m' p 1024)[k]! = (bytesAt m p 1024)[k]! := by rw [h]
  rwa [Proof.MlKem.bytesAt_getElem! _ _ hk, Proof.MlKem.bytesAt_getElem! _ _ hk] at this

end VG.Proof.MlDsa.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.KeyGen.Rest`. -/
section

/-!
# ML-DSA key generation: the keys from the sampled polynomials

Lines 5–10 of Algorithm 6 (`kgRest`) on the entries `A (ℓr + s)` of `Â` and `S
r` of `s₁ ‖ s₂`, row by row of `t` (`tK`), as the keys are computed: `t[i]` is
`NTT⁻¹` of the sum of the products `Â[i, j] ŝ₁[j]` (`dotK`, from `j = 0`) plus
`s₂[i]`, the public key is `ρ` followed by the packed `t₁[i]` (`pkK`), and the
private key `ρ ‖ K ‖ tr` followed by the packed `s₁ ‖ s₂` and `t₀[i]` (`skK`)
(`kgRest_eq`).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa

section
variable (p : Params) (A : Nat → Poly) (S : Nat → IPoly)

/-- `Σ_{j' < j} Â[i, j'] ŝ₁[j']`, summed from `j' = 0`. -/
def dotK (i j : Nat) : Poly :=
  ((List.range j).map fun j' => multiplyNTT (A (p.ℓ * i + j')) (ntt (toRq (S j')))).foldl add zero

/-- `t[i]`. -/
def tK (i : Nat) : Poly := add (nttInv (VG.Proof.MlDsa.KeyGen.dotK p A S i p.ℓ)) (toRq (S (p.ℓ + i)))

def t1K (i : Nat) : Vector Nat n := (VG.Proof.MlDsa.KeyGen.tK p A S i).map fun c => (power2Round c).1.toNat
def t0K (i : Nat) : IPoly := (VG.Proof.MlDsa.KeyGen.tK p A S i).map fun c => (power2Round c).2

def pkK (ρ : List Byte) : List Byte := ρ ++ (List.range p.k).flatMap fun i => simpleBitPack (VG.Proof.MlDsa.KeyGen.t1K p A S i) t1Max

def skK (ρ K : List Byte) : List Byte :=
  ρ ++ K ++ H (VG.Proof.MlDsa.KeyGen.pkK p A S ρ) 64 ++ (List.range (p.ℓ + p.k)).flatMap (fun r => bitPack (S r) p.η p.η) ++
    (List.range p.k).flatMap fun i => bitPack (VG.Proof.MlDsa.KeyGen.t0K p A S i) (2 ^ (d - 1) - 1) (2 ^ (d - 1))

theorem dotK_succ (i j : Nat) :
    VG.Proof.MlDsa.KeyGen.dotK p A S i (j + 1) = add (VG.Proof.MlDsa.KeyGen.dotK p A S i j) (multiplyNTT (A (p.ℓ * i + j)) (ntt (toRq (S j)))) := by
  simp only [VG.Proof.MlDsa.KeyGen.dotK, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem dotK_one (i : Nat) : VG.Proof.MlDsa.KeyGen.dotK p A S i 1 = multiplyNTT (A (p.ℓ * i)) (ntt (toRq (S 0))) := by
  rw [VG.Proof.MlDsa.KeyGen.dotK_succ, show VG.Proof.MlDsa.KeyGen.dotK p A S i 0 = zero from rfl, VG.Proof.MlDsa.KeyGen.add_zero_left, Nat.add_zero]

theorem zipWith_map_map {α β γ : Type} (f : α → β → γ) (g : Nat → α) (h : Nat → β) (k : Nat) :
    List.zipWith f ((List.range k).map g) ((List.range k).map h) = (List.range k).map fun j => f (g j) (h j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.zipWith_append (by simp), ih]
    simp

theorem kgRest_eq (ρ K : List Byte) :
    VG.Proof.MlDsa.KeyGen.kgRest p ρ K ((List.range p.k).map fun r => (List.range p.ℓ).map fun s => A (p.ℓ * r + s))
      ((List.range p.ℓ).map S) ((List.range p.k).map fun r => S (r + p.ℓ)) = (VG.Proof.MlDsa.KeyGen.pkK p A S ρ, VG.Proof.MlDsa.KeyGen.skK p A S ρ K) := by
  have ht : addVec ((matrixVectorNTT ((List.range p.k).map fun r => (List.range p.ℓ).map fun s => A (p.ℓ * r + s))
      (((List.range p.ℓ).map S).map fun s => ntt (toRq s))).map nttInv) (((List.range p.k).map fun r => S (r + p.ℓ)).map toRq) =
      (List.range p.k).map (VG.Proof.MlDsa.KeyGen.tK p A S) := by
    simp only [matrixVectorNTT, addVec, List.map_map]
    rw [VG.Proof.MlDsa.KeyGen.zipWith_map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, VG.Proof.MlDsa.KeyGen.tK, VG.Proof.MlDsa.KeyGen.dotK, Nat.add_comm i p.ℓ]
    rw [VG.Proof.MlDsa.KeyGen.zipWith_map_map]
    rfl
  unfold VG.Proof.MlDsa.KeyGen.kgRest
  dsimp only
  rw [ht]
  simp only [VG.Proof.MlDsa.KeyGen.pkK, VG.Proof.MlDsa.KeyGen.skK, VG.Proof.MlDsa.KeyGen.t1K, VG.Proof.MlDsa.KeyGen.t0K, skEncode, pkEncode, List.map_map, List.flatMap_map, List.range_add,
    List.flatMap_append, List.append_assoc]
  simp only [Function.comp, Nat.add_comm]

end

/-- Bytes in pieces of `len`. -/
theorem bytesAt_pieces (m : Mem) (a : Addr) (o len : Nat) :
    ∀ k, Spec.Sha3.bytesAt m (a + BitVec.ofNat 64 o) (len * k) =
      (List.range k).flatMap fun i => Spec.Sha3.bytesAt m (a + BitVec.ofNat 64 (o + len * i)) len
  | 0 => rfl
  | k + 1 => by
    rw [Nat.mul_succ, Proof.MlKem.bytesAt_add, VG.Proof.MlDsa.KeyGen.bytesAt_pieces m a o len k, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, BitVec.add_assoc, ← BitVec.ofNat_add]

end VG.Proof.MlDsa.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.KeyGen.Leak`. -/
section

/-!
# ML-DSA key generation: what it may leak, piece by piece

Two seeds that `ML-DSA.KeyGen_internal` may leak the same of (`keyGenLeak`)
have the same `ρ`, and each `RejBoundedPoly` of `ExpandS` leaks the same from
both (`keyGenLeak_split`); and the seeds of the samplers as
bytes (`integerToBytes_one`, `integerToBytes_two`).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa

theorem integerToBytes_one (x : Nat) : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem integerToBytes_two {x : Nat} (hx : x < 256) : integerToBytes x 2 = [BitVec.ofNat 8 x, 0] := by
  simp only [integerToBytes, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, Nat.pow_zero, Nat.div_one, Nat.pow_one, Nat.div_eq_of_lt hx]
  rfl

theorem keyGenSeeds_rho_length (p : VG.Spec.MlDsa.Params) (ξ : List Byte) : (keyGenSeeds p ξ).1.length = 32 := by
  simp [keyGenSeeds, VG.Proof.MlDsa.KeyGen.H_length]

theorem leakBytes_inj : ∀ {a b : List Byte}, leakBytes a = leakBytes b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: a, y :: b, h => by
    simp only [leakBytes, List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, VG.Proof.MlDsa.KeyGen.leakBytes_inj h.2]

theorem length_flatMap_pairs {α : Type} (f g : α → Nat) : ∀ l : List α, (l.flatMap fun z => [f z, g z]).length = 2 * l.length
  | [] => rfl
  | z :: l => by
    rw [List.flatMap_cons, List.length_append, VG.Proof.MlDsa.KeyGen.length_flatMap_pairs f g l, List.length_cons]; simp; omega

theorem rejBoundedLeak_length (η : Nat) (ρ : List Byte) : (rejBoundedLeak η ρ).length = 2 * 1088 := by
  unfold rejBoundedLeak
  rw [VG.Proof.MlDsa.KeyGen.length_flatMap_pairs, VG.Proof.MlDsa.KeyGen.H_length]; rfl

theorem flatMap_range_inj {f g : Nat → List Nat} {L : Nat} (hf : ∀ r, (f r).length = L) (hg : ∀ r, (g r).length = L) :
    ∀ {n : Nat}, (List.range n).flatMap f = (List.range n).flatMap g → ∀ r < n, f r = g r
  | 0, _, r, hr => absurd hr (Nat.not_lt_zero _)
  | n + 1, h, r, hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_singleton,
      List.flatMap_singleton] at h
    have hl : ((List.range n).flatMap f).length = ((List.range n).flatMap g).length := by
      simp only [List.length_flatMap, hf, hg]
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    rcases (by omega : r < n ∨ r = n) with hr | rfl
    · exact VG.Proof.MlDsa.KeyGen.flatMap_range_inj hf hg h1 r hr
    · exact h2

theorem keyGenLeak_split {p : VG.Spec.MlDsa.Params} {ξ₁ ξ₂ : List Byte} (h : keyGenLeak p ξ₁ = keyGenLeak p ξ₂) :
    (keyGenSeeds p ξ₁).1 = (keyGenSeeds p ξ₂).1 ∧ ∀ r < p.ℓ + p.k,
      rejBoundedLeak p.η (VG.Proof.MlDsa.KeyGen.seedS (keyGenSeeds p ξ₁).2.1 r) = rejBoundedLeak p.η (VG.Proof.MlDsa.KeyGen.seedS (keyGenSeeds p ξ₂).2.1 r) := by
  unfold keyGenLeak at h
  have hl : (leakBytes (keyGenSeeds p ξ₁).1).length = (leakBytes (keyGenSeeds p ξ₂).1).length := by
    simp [leakBytes, VG.Proof.MlDsa.KeyGen.keyGenSeeds_rho_length]
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  exact ⟨VG.Proof.MlDsa.KeyGen.leakBytes_inj h1, VG.Proof.MlDsa.KeyGen.flatMap_range_inj (fun _ => VG.Proof.MlDsa.KeyGen.rejBoundedLeak_length _ _) (fun _ => VG.Proof.MlDsa.KeyGen.rejBoundedLeak_length _ _) h2⟩

end VG.Proof.MlDsa.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.KeyGen.Masked`. -/
section

/-!
# ML-DSA key generation: the samplers' results, and masked polynomials

Key generation ANDs the results of the samplers (0 or 1) together (`and01`),
and ANDs each sampled polynomial with the negated result: a polynomial whose
sampler succeeded is kept (`masked_one`), and one whose sampler failed is zero
(`masked_zero`), so reduced and small (`small_zero`). The seeds of the
samplers as bytes (`seedA_eq`, `seedS_eq`).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa

/-- The coefficients of `x` are in `[-η, η]`. -/
def Small (η : Nat) (x : IPoly) : Prop := ∀ c ∈ x.toList, -(η : Int) ≤ c ∧ c ≤ η

theorem small_zero (η : Nat) : VG.Proof.MlDsa.KeyGen.Small η (Vector.replicate 256 0) := fun c hc => by
  rw [Vector.mem_toList_iff, Vector.mem_replicate] at hc
  rw [hc.2]; omega

theorem polyAt_coeff {m m' : Mem} {q : Addr} (h : ∀ i < 256, coeffAt m' q i = coeffAt m q i) :
    polyAt m' q = polyAt m q :=
  Vector.ext fun i hi => by simp only [polyAt, Vector.getElem_ofFn, h i hi]

/-- Kept if the sampler succeeded. -/
theorem masked_one {m m' : Mem} {q : Addr} {r : BitVec 32} (hr : r = 1)
    (h : ∀ i < 256, coeffAt m' q i = if r = 1 then coeffAt m q i else 0) :
    polyAt m' q = polyAt m q ∧ (Reduced m q → Reduced m' q) := by
  have h' : ∀ i < 256, coeffAt m' q i = coeffAt m q i := fun i hi => by rw [h i hi, VG.Proof.MlDsa.KeyGen.ifp hr]
  exact ⟨VG.Proof.MlDsa.KeyGen.polyAt_coeff h', fun hq i hi => by rw [h' i hi]; exact hq i hi⟩

/-- Zero if it failed. -/
theorem masked_zero {m m' : Mem} {q : Addr} {r : BitVec 32} (hr : r ≠ 1)
    (h : ∀ i < 256, coeffAt m' q i = if r = 1 then coeffAt m q i else 0) :
    PolyIs m' q (toRq (Vector.replicate 256 0)) := by
  have h' : ∀ i < 256, coeffAt m' q i = 0 := fun i hi => by rw [h i hi, VG.Proof.MlDsa.KeyGen.ifn hr]
  refine ⟨fun i hi => by rw [h' i hi]; decide, Vector.ext fun i hi => ?_⟩
  simp only [polyAt, Vector.getElem_ofFn, h' i hi, toRq, Vector.getElem_map, Vector.getElem_replicate]
  rfl

theorem outcome_01 {α : Type} {f : Bounds → Option α} {r : BitVec 32} {out : α}
    (h : Outcome f r out) : r = 0 ∨ r = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

/-- The AND of two results, 0 or 1, in 32 bits, zero-extended. -/
theorem and01 {v : BitVec 64} (hv : v = 0 ∨ v = 1) {r : BitVec 32} (hr : r = 0 ∨ r = 1) :
    BitVec.setWidth 64 (v.setWidth 32 &&& r) = if v = 1 ∧ r = 1 then 1 else 0 := by
  rcases hv with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

/-- The seed of `Â[r, s]`, as bytes. -/
theorem seedA_eq (ρ : List Byte) (r s : Nat) : VG.Proof.MlDsa.KeyGen.seedA ρ r s = ρ ++ [BitVec.ofNat 8 s, BitVec.ofNat 8 r] := by
  simp only [VG.Proof.MlDsa.KeyGen.seedA, VG.Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]; rfl

/-- The seed of entry `r` of `s₁ ‖ s₂`, as bytes. -/
theorem seedS_eq (ρ' : List Byte) {r : Nat} (hr : r < 256) : VG.Proof.MlDsa.KeyGen.seedS ρ' r = ρ' ++ [BitVec.ofNat 8 r, 0] := by
  simp only [VG.Proof.MlDsa.KeyGen.seedS, VG.Proof.MlDsa.KeyGen.integerToBytes_two hr]

end VG.Proof.MlDsa.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.KeyGen.Good`. -/
section

/-!
# ML-DSA key generation: the result of the samplers, for every target

Key generation samples every entry of `Â` and of `s₁ ‖ s₂`, and ANDs the
results of the samplers (`RejNTTPoly`, `RejBoundedPoly`, which may stop at
their bounds) without branching on them. `Good` says what the AND is after the
first `e` entries of `Â` and `r` of `s₁ ‖ s₂`: 1, with the entries those of
the standard for some bounds, or 0 if key generation fails within the least
bounds. Each sampler's outcome, ANDed in, keeps it (`good_A`, `good_S`), with
the entry stored masked by the result (`masked_one`, `masked_zero`); and at
the end it is the outcome of key generation (`outcome_keyGen`).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa

/-- The AND of the results so far, after the first `e` entries of `Â` and `r`
of `s₁ ‖ s₂` of key generation from `ξ`. -/
def Good (p : Params) (ξ : List Byte) (e r : Nat) (A : Nat → Poly) (S : Nat → IPoly) (v : BitVec 32) : Prop :=
  (v = 1 ∧ ∃ b : Bounds,
      (∀ e' < e, rejNTTPoly b.rejNTT (VG.Proof.MlDsa.KeyGen.seedA (keyGenSeeds p ξ).1 (e' / p.ℓ) (e' % p.ℓ)) = some (A e')) ∧
      ∀ r' < r, rejBoundedPoly p.η b.rejBounded (VG.Proof.MlDsa.KeyGen.seedS (keyGenSeeds p ξ).2.1 r') = some (S r')) ∨
    (v = 0 ∧ keyGenInternal p minBounds ξ = none)

theorem good_01 {p : Params} {ξ : List Byte} {e r : Nat} {A : Nat → Poly} {S : Nat → IPoly} {v : BitVec 32}
    (h : VG.Proof.MlDsa.KeyGen.Good p ξ e r A S v) : v = 0 ∨ v = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

theorem good_zero (p : Params) (ξ : List Byte) (A : Nat → Poly) (S : Nat → IPoly) : VG.Proof.MlDsa.KeyGen.Good p ξ 0 0 A S 1 :=
  .inl ⟨rfl, ⟨0, 0, 0, 0⟩, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem and_01 {v r : BitVec 32} (hv : v = 0 ∨ v = 1) (hr : r = 0 ∨ r = 1) :
    v &&& r = if v = 1 ∧ r = 1 then 1 else 0 := by
  rcases hv with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

/-- An entry of `Â`, sampled: `y` is what is stored, the output if the
sampler succeeded. -/
theorem good_A {p : Params} {ξ : List Byte} {e : Nat} (he : e < p.k * p.ℓ) {A : Nat → Poly} {S : Nat → IPoly}
    {v r : BitVec 32} {x y : Poly} (hG : VG.Proof.MlDsa.KeyGen.Good p ξ e 0 A S v)
    (ho : Outcome (fun b => rejNTTPoly b.rejNTT (VG.Proof.MlDsa.KeyGen.seedA (keyGenSeeds p ξ).1 (e / p.ℓ) (e % p.ℓ))) r x)
    (hy : r = 1 → y = x) :
    VG.Proof.MlDsa.KeyGen.Good p ξ (e + 1) 0 (fun e' => if e' = e then y else A e') S (v &&& r) := by
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at he; exact Nat.not_lt_zero _ he
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ hl
  rw [VG.Proof.MlDsa.KeyGen.and_01 (VG.Proof.MlDsa.KeyGen.good_01 hG) (VG.Proof.MlDsa.KeyGen.outcome_01 ho)]
  rcases hG with ⟨h1, b, hb, _⟩ | ⟨h0, hn⟩
  · rcases ho with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
    · refine .inl ⟨by rw [VG.Proof.MlDsa.KeyGen.ifp ⟨h1, ho⟩], VG.Proof.MlDsa.KeyGen.bmax b b', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      dsimp only
      rcases (by omega : e' < e ∨ e' = e) with he' | rfl
      · rw [VG.Proof.MlDsa.KeyGen.ifn (by omega)]
        exact VG.Proof.MlDsa.KeyGen.rejNTTPoly_mono (Bounds.le_max_left b b').rejNTT (hb e' he')
      · rw [VG.Proof.MlDsa.KeyGen.ifp rfl, hy ho]
        exact VG.Proof.MlDsa.KeyGen.rejNTTPoly_mono (Bounds.le_max_right b b').rejNTT hb'
    · rw [VG.Proof.MlDsa.KeyGen.ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
      exact .inr ⟨rfl, VG.Proof.MlDsa.KeyGen.keyGenInternal_none_A hq hr hn⟩
  · rw [VG.Proof.MlDsa.KeyGen.ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
    exact .inr ⟨rfl, hn⟩

/-- An entry of `s₁ ‖ s₂`, sampled: what is stored is `toRq z` for a small `z`,
the output if the sampler succeeded. -/
theorem good_S {p : Params} {ξ : List Byte} {r : Nat} (hr : r < p.ℓ + p.k) {A : Nat → Poly} {S : Nat → IPoly}
    {v res : BitVec 32} {x : Poly}
    (hG : VG.Proof.MlDsa.KeyGen.Good p ξ (p.k * p.ℓ) r A S v)
    (ho : Outcome (fun b => (rejBoundedPoly p.η b.rejBounded (VG.Proof.MlDsa.KeyGen.seedS (keyGenSeeds p ξ).2.1 r)).map toRq) res x) :
    ∃ z : IPoly, VG.Proof.MlDsa.KeyGen.Small p.η z ∧ (res = 1 → toRq z = x) ∧ (res ≠ 1 → z = Vector.replicate 256 0) ∧
      VG.Proof.MlDsa.KeyGen.Good p ξ (p.k * p.ℓ) (r + 1) A (fun r' => if r' = r then z else S r') (v &&& res) := by
  rw [VG.Proof.MlDsa.KeyGen.and_01 (VG.Proof.MlDsa.KeyGen.good_01 hG) (VG.Proof.MlDsa.KeyGen.outcome_01 ho)]
  by_cases h1 : res = 1
  · obtain ⟨b', hb'⟩ : ∃ b' : Bounds, (rejBoundedPoly p.η b'.rejBounded (VG.Proof.MlDsa.KeyGen.seedS (keyGenSeeds p ξ).2.1 r)).map toRq =
        some x := by
      rcases ho with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · rw [h] at h1; exact absurd h1 (by decide)
    obtain ⟨z, hz, htz⟩ := Option.map_eq_some_iff.mp hb'
    refine ⟨z, VG.Proof.MlDsa.KeyGen.rejBoundedPoly_range hz, fun _ => htz, fun h => absurd h1 h, ?_⟩
    rcases hG with ⟨hv, b, hbA, hbS⟩ | ⟨h0, hn⟩
    · refine .inl ⟨by rw [VG.Proof.MlDsa.KeyGen.ifp ⟨hv, h1⟩], VG.Proof.MlDsa.KeyGen.bmax b b', fun e' he' =>
        VG.Proof.MlDsa.KeyGen.rejNTTPoly_mono (Bounds.le_max_left b b').rejNTT (hbA e' he'), fun r' hr' => ?_⟩
      dsimp only
      rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
      · rw [VG.Proof.MlDsa.KeyGen.ifn (by omega)]
        exact VG.Proof.MlDsa.KeyGen.rejBoundedPoly_mono (Bounds.le_max_left b b').rejBounded (hbS r' hr')
      · rw [VG.Proof.MlDsa.KeyGen.ifp rfl]
        exact VG.Proof.MlDsa.KeyGen.rejBoundedPoly_mono (Bounds.le_max_right b b').rejBounded hz
    · rw [VG.Proof.MlDsa.KeyGen.ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl, hn⟩
  · have hn : rejBoundedPoly p.η minBounds.rejBounded (VG.Proof.MlDsa.KeyGen.seedS (keyGenSeeds p ξ).2.1 r) = none := by
      rcases ho with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h h1
      · exact Option.map_eq_none_iff.mp h
    refine ⟨Vector.replicate 256 0, VG.Proof.MlDsa.KeyGen.small_zero _, fun h => absurd h h1, fun _ => rfl, ?_⟩
    rw [VG.Proof.MlDsa.KeyGen.ifn (fun h => h1 h.2)]
    exact .inr ⟨rfl, VG.Proof.MlDsa.KeyGen.keyGenInternal_none_S hr hn⟩

theorem idx_lt {p : Params} {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have : p.ℓ * i + j < p.ℓ * (i + 1) := by rw [Nat.mul_succ]; omega
  have : p.ℓ * (i + 1) ≤ p.ℓ * p.k := Nat.mul_le_mul_left _ hi
  rw [Nat.mul_comm p.k]; omega

/-- At the end, the AND of the results is the outcome of key generation. -/
theorem outcome_keyGen {p : Params} {ξ : List Byte} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 32}
    (hl : 0 < p.ℓ) (hG : VG.Proof.MlDsa.KeyGen.Good p ξ (p.k * p.ℓ) (p.ℓ + p.k) A S R) :
    Outcome (fun b => keyGenInternal p b ξ) R
      (VG.Proof.MlDsa.KeyGen.pkK p A S (keyGenSeeds p ξ).1, VG.Proof.MlDsa.KeyGen.skK p A S (keyGenSeeds p ξ).1 (keyGenSeeds p ξ).2.2) := by
  rcases hG with ⟨rfl, b, hbA, hbS⟩ | ⟨rfl, hn⟩
  · refine .inl ⟨rfl, b, ?_⟩
    show keyGenInternal p b ξ = _
    rw [VG.Proof.MlDsa.KeyGen.keyGenInternal_eq, VG.Proof.MlDsa.KeyGen.expandA_some (A := fun r s => A (p.ℓ * r + s)) fun r hr s hs => ?_, Option.bind_some,
      VG.Proof.MlDsa.KeyGen.expandS_some (S := S) hbS, Option.map_some, VG.Proof.MlDsa.KeyGen.kgRest_eq]
    have := hbA (p.ℓ * r + s) (VG.Proof.MlDsa.KeyGen.idx_lt hr hs)
    rwa [Nat.mul_add_div hl, Nat.div_eq_of_lt hs, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hs] at this
  · exact .inr ⟨rfl, hn⟩

/-! ## A masked polynomial -/

end VG.Proof.MlDsa.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.KeyGen.Mask32`. -/
section

/-!
# ML-DSA key generation: masked samples, and the leakage as bytes

A sampler's result `r` (0 or
1) is ANDed into an accumulator (`acc_and`), and its polynomial with `-r`
(`masked`): kept if the sampler succeeded, zero (reduced, and small) if it
failed. What key generation may leak (`keyGenLeak`) is a list of numbers
less than 256 (`keyGenLeak_lt`), so as bytes it is the same exactly when it
is the same (`map_ofNat_inj`).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa

/-! ## Masks -/

theorem acc_and {a r : BitVec 32} (ha : a = 0 ∨ a = 1) (hr : r = 0 ∨ r = 1) :
    (a &&& r = 0 ∨ a &&& r = 1) ∧ (a &&& r = 1 ↔ a = 1 ∧ r = 1) := by
  rcases ha with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

/-- The zero polynomial, as the samplers' outputs are when they fail. -/
abbrev zeroI : IPoly := Vector.replicate 256 0

/-- A polynomial masked with the result `r` of the sampler that wrote it. -/
theorem masked {m m' : Mem} {p : Addr} {r : BitVec 32} (hr : r = 0 ∨ r = 1)
    (h : ∀ i < 256, VG.Spec.MlDsa.coeffAt m' p i = VG.Spec.MlDsa.coeffAt m p i &&& (0 - r)) :
    (r = 1 → (∀ i < 256, VG.Spec.MlDsa.coeffAt m' p i = VG.Spec.MlDsa.coeffAt m p i) ∧ VG.Spec.MlDsa.polyAt m' p = VG.Spec.MlDsa.polyAt m p ∧
        (VG.Spec.MlDsa.Reduced m p → VG.Spec.MlDsa.Reduced m' p)) ∧
      (r = 0 → VG.Spec.MlDsa.PolyIs m' p (toRq VG.Proof.MlDsa.KeyGen.zeroI)) := by
  rcases hr with rfl | rfl
  · have h' : ∀ i < 256, VG.Spec.MlDsa.coeffAt m' p i = 0 := fun i hi => by rw [h i hi]; simp
    refine ⟨fun e => absurd e (by decide), fun _ => ⟨fun i hi => by rw [h' i hi]; decide, Vector.ext fun i hi => ?_⟩⟩
    simp only [VG.Spec.MlDsa.polyAt, Vector.getElem_ofFn, h' i hi, toRq, Vector.getElem_map, Vector.getElem_replicate]
    rfl
  · have h' : ∀ i < 256, VG.Spec.MlDsa.coeffAt m' p i = VG.Spec.MlDsa.coeffAt m p i := fun i hi => by
      rw [h i hi, show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    refine ⟨fun _ => ⟨h', Vector.ext fun i hi => ?_, fun hq i hi => by rw [h' i hi]; exact hq i hi⟩,
      fun e => absurd e (by decide)⟩
    simp only [VG.Spec.MlDsa.polyAt, Vector.getElem_ofFn, h' i hi]

theorem zeroI_small (η : Nat) : ∀ c ∈ zeroI.toList, -(η : Int) ≤ c ∧ c ≤ η := fun c hc => by
  rw [Vector.mem_toList_iff, Vector.mem_replicate] at hc
  rw [hc.2]; omega

/-! ## The leakage as bytes -/

theorem map_ofNat_inj : ∀ {a b : List Nat}, (∀ x ∈ a, x < 256) → (∀ x ∈ b, x < 256) →
    a.map (BitVec.ofNat 8) = b.map (BitVec.ofNat 8) → a = b
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | x :: a, y :: b, ha, hb, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hx := ha x (List.mem_cons_self ..)
    have hy := hb y (List.mem_cons_self ..)
    have := congrArg BitVec.toNat h.1
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
    rw [this, VG.Proof.MlDsa.KeyGen.map_ofNat_inj (fun z hz => ha z (List.mem_cons_of_mem _ hz))
      (fun z hz => hb z (List.mem_cons_of_mem _ hz)) h.2]

theorem halfByteOk_le (η b : Nat) : halfByteOk η b < 256 := by
  unfold halfByteOk; split <;> decide

theorem keyGenLeak_lt (p : VG.Spec.MlDsa.Params) (ξ : List Byte) : ∀ x ∈ keyGenLeak p ξ, x < 256 := by
  intro x hx
  simp only [keyGenLeak, leakBytes, rejBoundedLeak, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ⟨b, _, rfl⟩ | ⟨_, _, _, _, rfl | rfl⟩
  · exact b.isLt
  all_goals exact VG.Proof.MlDsa.KeyGen.halfByteOk_le _ _

theorem keyGenLeak_bytes {p : VG.Spec.MlDsa.Params} {ξ₁ ξ₂ : List Byte}
    (h : (keyGenLeak p ξ₁).map (BitVec.ofNat 8) = (keyGenLeak p ξ₂).map (BitVec.ofNat 8)) :
    keyGenLeak p ξ₁ = keyGenLeak p ξ₂ :=
  VG.Proof.MlDsa.KeyGen.map_ofNat_inj (VG.Proof.MlDsa.KeyGen.keyGenLeak_lt p ξ₁) (VG.Proof.MlDsa.KeyGen.keyGenLeak_lt p ξ₂) h

end VG.Proof.MlDsa.KeyGen

end
