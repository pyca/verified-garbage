import VerifiedGarbage.Spec.MlDsa
import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Spec.MlDsa.Poly
import Mathlib.Tactic.SplitIfs

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Verify.Bounds`. -/
section

/-!
# ML-DSA: larger bounds give the same results

`H` and `G` squeezed to fewer bytes give a prefix of their longer outputs
(`H_take`, `G_take`), so the samplers `RejNTTPoly` and `SampleInBall`, which
stop once they have their output, give the same result from any larger bound
once they succeed (`rejNTTPoly_mono`, `sampleInBall_mono`); and so does
`verifyMu` (`verifyMu_mono`), for bounds that are larger in the two loops it
has.
-/

namespace VG.Proof.MlDsa.Verify

open VG.Spec.MlDsa
open VG.Spec.Sha3 (squeeze keccak sponge)

theorem iteP {α : Sort _} {p : Prop} [Decidable p] (h : p) {a b : α} : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem iteN {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) {a b : α} : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-- `b` bounds each loop by no more than `b'` does. -/
structure BLe (b b' : Bounds) : Prop where
  sign : b.sign ≤ b'.sign
  rejBounded : b.rejBounded ≤ b'.rejBounded
  rejNTT : b.rejNTT ≤ b'.rejNTT
  ball : b.ball ≤ b'.ball

/-- The larger of two bounds on each loop. -/
def bmax (b b' : Bounds) : Bounds :=
  ⟨max b.sign b'.sign, max b.rejBounded b'.rejBounded, max b.rejNTT b'.rejNTT, max b.ball b'.ball⟩

theorem bmax_left (b b' : Bounds) : VG.Proof.MlDsa.Verify.BLe b (VG.Proof.MlDsa.Verify.bmax b b') :=
  ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩

theorem bmax_right (b b' : Bounds) : VG.Proof.MlDsa.Verify.BLe b' (VG.Proof.MlDsa.Verify.bmax b b') :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _⟩

theorem BLe.refl (b : Bounds) : VG.Proof.MlDsa.Verify.BLe b b := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem BLe.trans {a b c : Bounds} (h₁ : VG.Proof.MlDsa.Verify.BLe a b) (h₂ : VG.Proof.MlDsa.Verify.BLe b c) : VG.Proof.MlDsa.Verify.BLe a c :=
  ⟨Nat.le_trans h₁.1 h₂.1, Nat.le_trans h₁.2 h₂.2, Nat.le_trans h₁.3 h₂.3, Nat.le_trans h₁.4 h₂.4⟩

/-! ## Prefixes of the outputs of `H` and `G` -/

theorem squeeze_take {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : Spec.Sha3.State) {d d' : Nat}
    (h : d ≤ d') : (squeeze rate S d').take d = squeeze rate S d := by
  refine List.ext_getElem (by simp [Proof.Sha3.length_squeeze hr hr']; omega) fun i h₁ h₂ => ?_
  rw [Proof.Sha3.length_squeeze hr hr'] at h₂
  rw [List.getElem_take, Proof.Sha3.squeeze_getElem hr hr' _ h₂, Proof.Sha3.squeeze_getElem hr hr' _ (by omega)]

theorem H_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (H s d').take d = H s d :=
  VG.Proof.MlDsa.Verify.squeeze_take (by decide) (by decide) _ h

theorem G_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (G s d').take d = G s d :=
  VG.Proof.MlDsa.Verify.squeeze_take (by decide) (by decide) _ h

theorem H_length (s : List Byte) (d : Nat) : (H s d).length = d :=
  Proof.Sha3.length_squeeze (by decide) (by decide) _ _

/-! ## `RejNTTPoly` -/

theorem rejNTTLoop_full {a : List Zq} (ha : a.length ≥ n) : ∀ out, rejNTTLoop a out = some a
  | _ :: _ :: _ :: _ => by unfold rejNTTLoop; exact ite_eq_left_iff.mpr fun h => absurd ha h
  | [] => by unfold rejNTTLoop; exact ite_eq_left_iff.mpr fun h => absurd ha h
  | [_] => by unfold rejNTTLoop; exact ite_eq_left_iff.mpr fun h => absurd ha h
  | [_, _] => by unfold rejNTTLoop; exact ite_eq_left_iff.mpr fun h => absurd ha h

theorem rejNTTLoop_step {a : List Zq} (ha : ¬ a.length ≥ n) (s₀ s₁ s₂ : Byte) (out : List Byte) :
    rejNTTLoop a (s₀ :: s₁ :: s₂ :: out) = rejNTTLoop (match coeffFromThreeBytes s₀ s₁ s₂ with
      | some c => a ++ [c]
      | none => a) out := by
  rw [rejNTTLoop.eq_1]
  exact VG.Proof.MlDsa.Verify.iteN ha

theorem rejNTTLoop_short {a : List Zq} (ha : ¬ a.length ≥ n) {out : List Byte} (h : out.length < 3) :
    rejNTTLoop a out = none := by
  match out, h with
  | [], _ => unfold rejNTTLoop; exact VG.Proof.MlDsa.Verify.iteN ha
  | [_], _ => unfold rejNTTLoop; exact VG.Proof.MlDsa.Verify.iteN ha
  | [_, _], _ => unfold rejNTTLoop; exact VG.Proof.MlDsa.Verify.iteN ha

theorem rejNTTLoop_append : ∀ (a : List Zq) (out more : List Byte) (x : List Zq),
    rejNTTLoop a out = some x → rejNTTLoop a (out ++ more) = some x
  | a, s₀ :: s₁ :: s₂ :: out, more, x, h => by
    by_cases ha : a.length ≥ n
    · rw [VG.Proof.MlDsa.Verify.rejNTTLoop_full ha] at h ⊢; exact h
    · rw [VG.Proof.MlDsa.Verify.rejNTTLoop_step ha] at h
      rw [List.cons_append, List.cons_append, List.cons_append, VG.Proof.MlDsa.Verify.rejNTTLoop_step ha]
      exact VG.Proof.MlDsa.Verify.rejNTTLoop_append _ out more x h
  | a, [], more, x, h
  | a, [_], more, x, h
  | a, [_, _], more, x, h => by
    by_cases ha : a.length ≥ n
    · rw [VG.Proof.MlDsa.Verify.rejNTTLoop_full ha] at h ⊢; exact h
    · rw [VG.Proof.MlDsa.Verify.rejNTTLoop_short ha (by simp)] at h; cases h

theorem rejNTTPoly_mono {bound bound' : Nat} (hb : bound ≤ bound') {ρ : List Byte} {x : Poly}
    (h : rejNTTPoly bound ρ = some x) : rejNTTPoly bound' ρ = some x := by
  unfold rejNTTPoly at h ⊢
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  have e : G ρ bound' = G ρ bound ++ (G ρ bound').drop bound := by
    rw [← VG.Proof.MlDsa.Verify.G_take ρ hb, List.take_append_drop]
  rw [e, VG.Proof.MlDsa.Verify.rejNTTLoop_append _ _ _ _ ha]
  rfl

/-! ## `SampleInBall` -/

theorem ballLoop_full (τ : Nat) (h : Array Bool) {c : IPoly} {i : Nat} (hi : i ≥ n) :
    ∀ out, ballLoop τ h c i out = some c
  | [] => by rw [ballLoop.eq_1]; exact VG.Proof.MlDsa.Verify.iteP hi
  | _ :: _ => by rw [ballLoop.eq_2]; exact VG.Proof.MlDsa.Verify.iteP hi

theorem ballLoop_step (τ : Nat) (h : Array Bool) {c : IPoly} {i : Nat} (hi : ¬ i ≥ n) (j : Byte)
    (out : List Byte) : ballLoop τ h c i (j :: out) =
      if j.toNat > i then ballLoop τ h c i out
      else ballLoop τ h ((c.set! i c[j.toNat]!).set! j.toNat (if h.getD (i + τ - 256) false then -1 else 1))
        (i + 1) out := by
  rw [ballLoop.eq_2]; exact VG.Proof.MlDsa.Verify.iteN hi

theorem ballLoop_append (τ : Nat) (h : Array Bool) : ∀ (out more : List Byte) (c : IPoly) (i : Nat) (x : IPoly),
    ballLoop τ h c i out = some x → ballLoop τ h c i (out ++ more) = some x
  | [], more, c, i, x, e => by
    by_cases hi : i ≥ n
    · rw [VG.Proof.MlDsa.Verify.ballLoop_full τ h hi] at e ⊢; exact e
    · rw [ballLoop.eq_1, VG.Proof.MlDsa.Verify.iteN hi] at e; cases e
  | j :: out, more, c, i, x, e => by
    by_cases hi : i ≥ n
    · rw [VG.Proof.MlDsa.Verify.ballLoop_full τ h hi] at e ⊢; exact e
    · rw [VG.Proof.MlDsa.Verify.ballLoop_step τ h hi] at e
      rw [List.cons_append, VG.Proof.MlDsa.Verify.ballLoop_step τ h hi]
      split at e
      · rw [VG.Proof.MlDsa.Verify.iteP ‹_›]; exact VG.Proof.MlDsa.Verify.ballLoop_append τ h out more _ _ _ e
      · rw [VG.Proof.MlDsa.Verify.iteN ‹_›]; exact VG.Proof.MlDsa.Verify.ballLoop_append τ h out more _ _ _ e

theorem sampleInBall_mono {τ bound bound' : Nat} (hb : bound ≤ bound') {ρ : List Byte} {x : IPoly}
    (h : sampleInBall τ bound ρ = some x) : sampleInBall τ bound' ρ = some x := by
  unfold sampleInBall at h ⊢
  dsimp only at h ⊢
  rw [VG.Proof.MlDsa.Verify.H_length] at h ⊢
  split at h
  · cases h
  · rename_i h8
    rw [VG.Proof.MlDsa.Verify.iteN (by omega)]
    have e : H ρ bound' = H ρ bound ++ (H ρ bound').drop bound := by
      rw [← VG.Proof.MlDsa.Verify.H_take ρ hb, List.take_append_drop]
    have e8 : (H ρ bound').take 8 = (H ρ bound).take 8 := by
      rw [e, List.take_append_of_le_length (by rw [VG.Proof.MlDsa.Verify.H_length]; omega)]
    have ed := congrArg (List.drop 8) e
    rw [List.drop_append_of_le_length (by rw [VG.Proof.MlDsa.Verify.H_length]; omega)] at ed
    rw [e8, ed]
    exact VG.Proof.MlDsa.Verify.ballLoop_append _ _ _ _ _ _ _ h

/-! ## `ExpandA` and `verifyMu` -/

theorem mapM_mono {α β : Type} {f f' : α → Option β}
    (hf : ∀ a y, f a = some y → f' a = some y) : ∀ {l : List α} {ys : List β},
    l.mapM f = some ys → l.mapM f' = some ys
  | [], _, h => h
  | a :: l, ys, h => by
    rw [List.mapM_cons] at h ⊢
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys', hys, h⟩ := Option.bind_eq_some_iff.mp h
    rw [hf a y hy, VG.Proof.MlDsa.Verify.mapM_mono hf hys]
    exact h

theorem expandA_mono {p : Params} {b b' : Bounds} (hb : b.rejNTT ≤ b'.rejNTT) {ρ : List Byte}
    {A : List (List Poly)} (h : expandA p b ρ = some A) : expandA p b' ρ = some A :=
  VG.Proof.MlDsa.Verify.mapM_mono (fun _ _ hr => VG.Proof.MlDsa.Verify.mapM_mono (fun _ _ hs => VG.Proof.MlDsa.Verify.rejNTTPoly_mono hb hs) hr) h

theorem verifyMu_mono {p : Params} {b b' : Bounds} (h₁ : b.rejNTT ≤ b'.rejNTT) (h₂ : b.ball ≤ b'.ball)
    {pk μ σ : List Byte} {x : Bool} (h : verifyMu p b pk μ σ = some x) : verifyMu p b' pk μ σ = some x := by
  unfold verifyMu at h ⊢
  generalize pkDecode p pk = PK at h ⊢
  obtain ⟨ρ, t₁⟩ := PK
  generalize sigDecode p σ = SD at h ⊢
  obtain ⟨ct, z, ho⟩ := SD
  cases ho with
  | none => exact h
  | some hh =>
    dsimp only at h ⊢
    obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    rw [VG.Proof.MlDsa.Verify.expandA_mono h₁ hA, VG.Proof.MlDsa.Verify.sampleInBall_mono h₂ hc]
    exact h

/-! ## The postcondition of verification -/

/-- The postcondition of `verifyContract`, from the value of `verifyMu` for
some bounds: a result of 1 if it is true, and 0 if it is false. -/
theorem post_of_value {v : Bounds → Option Bool}
    (hv : ∀ b b' x, b.rejNTT ≤ b'.rejNTT → b.ball ≤ b'.ball → v b = some x → v b' = some x)
    {b : Bounds} {x : Bool} (h : v b = some x) (r : BitVec 32) (hr : r = if x then 1 else 0) :
    (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true) := by
  cases x
  · refine .inr ⟨hr, fun hm => ?_⟩
    have e₁ := hv _ _ _ (VG.Proof.MlDsa.Verify.bmax_left b minBounds).rejNTT (VG.Proof.MlDsa.Verify.bmax_left b minBounds).ball h
    have e₂ := hv _ _ _ (VG.Proof.MlDsa.Verify.bmax_right b minBounds).rejNTT (VG.Proof.MlDsa.Verify.bmax_right b minBounds).ball hm
    rw [e₁] at e₂
    cases e₂
  · exact .inl ⟨hr, b, h⟩

end VG.Proof.MlDsa.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Verify.Spec`. -/
section

/-!
# ML-DSA: `verifyMu` as the verification functions compute it

The pieces of the public key and of the signature (`vT1`, `vCt`, `vZ`,
`vHint`) and the seeds of `Â` (`aSeed`); and, once the hint is well formed and
the samplers have given `Â` and `c` within the bounds `b`, `verifyMu` computed
row by row (`verifyMu_rows`): row `r` of `w′` is `NTT⁻¹` of the sum of the
products `Â[r, s] ẑ[s]` from `s = 0` (`dotAcc`), less `ĉ t̂₁[r]`, and its
`w′₁` the `UseHint`s of `h[r]` and its coefficients.
-/

namespace VG.Proof.MlDsa.Verify

open VG.Spec.MlDsa

/-! ## The pieces of the inputs -/

section
variable (p : Params) (pk σ : List Byte)

/-- The length of a packed `z[i]`, `32(1 + bitlen (γ₁ - 1))` bytes. -/
def lenZ : Nat := 32 * (1 + bitlen (p.γ₁ - 1))

/-- `ρ`, the first 32 bytes of the public key. -/
def vRho : List Byte := pk.take 32

/-- `t₁[r]`. -/
def vT1 (r : Nat) : Vector Nat n := simpleBitUnpack ((pk.drop (32 + 320 * r)).take 320) t1Max

/-- `c̃`. -/
def vCt : List Byte := σ.take p.ctildeLen

/-- `z[i]`. -/
def vZ (i : Nat) : IPoly :=
  bitUnpack ((σ.drop (p.ctildeLen + VG.Proof.MlDsa.Verify.lenZ p * i)).take (VG.Proof.MlDsa.Verify.lenZ p)) (p.γ₁ - 1) p.γ₁

/-- `h`, or `⊥`. -/
def vHint : Option (List (Vector Bool n)) :=
  hintBitUnpack p.ω p.k ((σ.drop (p.ctildeLen + VG.Proof.MlDsa.Verify.lenZ p * p.ℓ)).take (p.ω + p.k))

/-- The seed `ρ ‖ s ‖ r` of `Â[r, s]`. -/
def aSeed (r s : Nat) : List Byte := VG.Proof.MlDsa.Verify.vRho pk ++ integerToBytes s 1 ++ integerToBytes r 1

end

theorem bitlen_q : bitlen (q - 1) = 23 := by decide

theorem pkDecode_eq (p : Params) (pk : List Byte) :
    pkDecode p pk = (VG.Proof.MlDsa.Verify.vRho pk, (List.range p.k).map (VG.Proof.MlDsa.Verify.vT1 pk)) := by
  unfold pkDecode
  rw [VG.Proof.MlDsa.Verify.bitlen_q]
  rfl

theorem sigDecode_eq (p : Params) (σ : List Byte) :
    sigDecode p σ = (VG.Proof.MlDsa.Verify.vCt p σ, (List.range p.ℓ).map (VG.Proof.MlDsa.Verify.vZ p σ), VG.Proof.MlDsa.Verify.vHint p σ) := by
  simp only [sigDecode, pieces, VG.Proof.MlDsa.Verify.vCt, VG.Proof.MlDsa.Verify.vHint, VG.Proof.MlDsa.Verify.lenZ, List.map_map]
  rfl

/-! ## Row by row -/

/-- `mapM` of a function that succeeds everywhere. -/
theorem mapM_range {β : Type} {f : Nat → Option β} {g : Nat → β} :
    ∀ {k : Nat}, (∀ i < k, f i = some (g i)) → (List.range k).mapM f = some ((List.range k).map g)
  | 0, _ => rfl
  | k + 1, h => by
    rw [List.range_succ, List.mapM_append, VG.Proof.MlDsa.Verify.mapM_range fun i hi => h i (by omega), List.mapM_cons,
      h k (by omega), List.map_append]
    rfl

theorem add_zero_left (f : Poly) : add zero f = f := by
  apply Vector.ext
  intro i hi
  simp only [add, zero, Vector.getElem_zipWith, Vector.getElem_replicate]
  exact Fin.ext (by rw [Fin.val_add]; simp)

section
variable (p : Params) (σ : List Byte) (A : Nat → Nat → Poly)

/-- `ẑ[i]`. -/
def zHat (i : Nat) : Poly := ntt (toRq (VG.Proof.MlDsa.Verify.vZ p σ i))

/-- `Σ_{s < j} Â[r, s] ẑ[s]`, from `s = 0`. -/
def dotAcc (r : Nat) : Nat → Poly
  | 0 => zero
  | j + 1 => add (VG.Proof.MlDsa.Verify.dotAcc r j) (multiplyNTT (A r j) (VG.Proof.MlDsa.Verify.zHat p σ j))

end

/-- `t̂₁[r]`. -/
def t1Hat (pk : List Byte) (r : Nat) : Poly := ntt ((VG.Proof.MlDsa.Verify.vT1 pk r).map fun c => ofInt (c * 2 ^ d : Nat))

section
variable (p : Params) (pk σ : List Byte) (A : Nat → Nat → Poly) (ch : Poly)

/-- Row `r` of `w′`, with `ĉ = ch`. -/
def wRow (r : Nat) : Poly :=
  nttInv (sub (VG.Proof.MlDsa.Verify.dotAcc p σ A r p.ℓ) (multiplyNTT ch (VG.Proof.MlDsa.Verify.t1Hat pk r)))

/-- Row `r` of `w′₁`, with the hint `h`. -/
def w1Row (h : List (Vector Bool n)) (r : Nat) : Vector Nat n :=
  Vector.zipWith (fun hj wj => (useHint p.γ₂ hj wj).toNat) (h.getD r (Vector.replicate n false))
    (VG.Proof.MlDsa.Verify.wRow p pk σ A ch r)

end

theorem foldl_dot (p : Params) (σ : List Byte) (A : Nat → Nat → Poly) (r : Nat) :
    ∀ j, ((List.range j).map fun s => multiplyNTT (A r s) (VG.Proof.MlDsa.Verify.zHat p σ s)).foldl add zero = VG.Proof.MlDsa.Verify.dotAcc p σ A r j
  | 0 => rfl
  | j + 1 => by
    rw [List.range_succ, List.map_append, List.foldl_append, VG.Proof.MlDsa.Verify.foldl_dot p σ A r j]
    rfl

theorem zipWith_range {α β γ : Type} (f : α → β → γ) (g : Nat → α) (h : Nat → β) (k : Nat) :
    List.zipWith f ((List.range k).map g) ((List.range k).map h) = (List.range k).map fun i => f (g i) (h i) := by
  rw [List.zipWith_map, List.zipWith_self]

theorem zipWith_getD {α β γ : Type} (f : α → β → γ) (d : α) (l : List α) (g : Nat → β) {k : Nat}
    (hl : l.length = k) :
    List.zipWith f l ((List.range k).map g) = (List.range k).map fun i => f (l.getD i d) (g i) := by
  subst hl
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa using h₁)]
  rfl

theorem some_bind' {α β : Type} (x : α) (f : α → Option β) : (some x >>= f) = f x := rfl

/-- `verifyMu`, once the hint is well formed and the samplers have given
`Â` and `c`. -/
theorem verifyMu_rows (p : Params) (b : Bounds) (pk μ σ : List Byte) {h : List (Vector Bool n)}
    (hh : VG.Proof.MlDsa.Verify.vHint p σ = some h) (hl : h.length = p.k) {A : Nat → Nat → Poly}
    (hA : ∀ r < p.k, ∀ s < p.ℓ, rejNTTPoly b.rejNTT (VG.Proof.MlDsa.Verify.aSeed pk r s) = some (A r s)) {c : IPoly}
    (hc : sampleInBall p.τ b.ball (VG.Proof.MlDsa.Verify.vCt p σ) = some c) :
    verifyMu p b pk μ σ = some (decide (normR ((List.range p.ℓ).map (VG.Proof.MlDsa.Verify.vZ p σ)) < p.γ₁ - p.β) &&
      VG.Proof.MlDsa.Verify.vCt p σ == H (μ ++ (List.range p.k).flatMap fun r =>
        simpleBitPack (VG.Proof.MlDsa.Verify.w1Row p pk σ A (ntt (toRq c)) h r) ((q - 1) / (2 * p.γ₂) - 1)) p.ctildeLen) := by
  have eA : expandA p b (VG.Proof.MlDsa.Verify.vRho pk) = some ((List.range p.k).map fun r => (List.range p.ℓ).map (A r)) :=
    VG.Proof.MlDsa.Verify.mapM_range fun r hr => VG.Proof.MlDsa.Verify.mapM_range fun s hs => hA r hr s hs
  unfold verifyMu
  rw [VG.Proof.MlDsa.Verify.pkDecode_eq, VG.Proof.MlDsa.Verify.sigDecode_eq, hh]
  dsimp only
  rw [eA, hc]
  have e1 : ∀ r, List.zipWith multiplyNTT (List.map (A r) (List.range p.ℓ))
      (List.map (fun x => ntt (toRq (VG.Proof.MlDsa.Verify.vZ p σ x))) (List.range p.ℓ)) =
      (List.range p.ℓ).map fun s => multiplyNTT (A r s) (VG.Proof.MlDsa.Verify.zHat p σ s) := fun r => VG.Proof.MlDsa.Verify.zipWith_range _ _ _ _
  simp only [VG.Proof.MlDsa.Verify.some_bind', List.map_map, w1Encode, matrixVectorNTT, scalarVectorNTT, subVec, Function.comp_def, e1,
    VG.Proof.MlDsa.Verify.foldl_dot]
  rw [VG.Proof.MlDsa.Verify.zipWith_range, List.map_map, VG.Proof.MlDsa.Verify.zipWith_getD _ (Vector.replicate n false) _ _ hl, List.flatMap_map]
  simp only [Function.comp_apply, VG.Proof.MlDsa.Verify.w1Row, VG.Proof.MlDsa.Verify.wRow, VG.Proof.MlDsa.Verify.t1Hat]
  rfl

end VG.Proof.MlDsa.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Verify.Norm`. -/
section

/-!
# ML-DSA: the norm of `z` and the range of `UseHint`

The coefficients of `z` unpacked from a signature are in `(-γ₁, γ₁]`
(`bitUnpack_bounds`), so the norm of each, as a polynomial of `R_q` (what
`vg_mldsa_norm_lt` computes), is its norm in `R` (`normZq_ofInt`), and `‖z‖∞ <
B` exactly when each `‖z[i]‖∞ < B` (`normR_vZ_iff`). `UseHint` gives a
coefficient of `w₁` of at most `(q - 1)/(2γ₂) - 1` (`useHint_le`), which
`SimpleBitPack` needs.
-/

namespace VG.Proof.MlDsa.Verify

open VG.Spec.MlDsa

/-! ## Norms -/

theorem foldl_max_lt {B : Nat} : ∀ (l : List Nat) (a : Nat), l.foldl max a < B ↔ a < B ∧ ∀ x ∈ l, x < B
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, VG.Proof.MlDsa.Verify.foldl_max_lt l (max a x)]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · intro ⟨h₁, h₂⟩; exact ⟨by omega, by omega, h₂⟩
    · intro ⟨h₁, h₂, h₃⟩; exact ⟨by omega, h₃⟩

theorem normR_lt_iff {B : Nat} (hB : 0 < B) (zs : List IPoly) :
    normR zs < B ↔ ∀ z ∈ zs, ∀ x ∈ z.toList, x.natAbs < B := by
  unfold normR
  rw [VG.Proof.MlDsa.Verify.foldl_max_lt]
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · intro ⟨_, h⟩ z hz x hx; exact h _ ⟨z, hz, x, hx, rfl⟩
  · intro h; exact ⟨hB, fun _ ⟨z, hz, x, hx, e⟩ => e ▸ h z hz x hx⟩

theorem normRq_lt_iff {B : Nat} (hB : 0 < B) (f : Poly) :
    normRq [f] < B ↔ ∀ x ∈ f.toList, normZq x < B := by
  unfold normRq
  rw [VG.Proof.MlDsa.Verify.foldl_max_lt]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map]
  constructor
  · intro ⟨_, h⟩ x hx; exact h _ ⟨x, hx, rfl⟩
  · intro h; exact ⟨hB, fun _ ⟨x, hx, e⟩ => e ▸ h x hx⟩

/-- `‖x mod q‖∞ = |x|` for `|x| ≤ (q - 1)/2`. -/
theorem normZq_ofInt {x : Int} (h₁ : -4190208 ≤ x) (h₂ : x ≤ 4190208) : normZq (ofInt x) = x.natAbs := by
  have hq : (q : Int) = 8380417 := rfl
  have hq2 : ((q / 2 : Nat) : Int) = 4190208 := rfl
  unfold normZq ofInt modPm
  have hv : ((Fin.ofNat q (x % (q : Int)).toNat : Zq).val : Int) = x % 8380417 := by
    rw [Fin.val_ofNat, hq, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hv]
  dsimp only
  rw [hq, hq2]
  split <;> omega

theorem bitsToInteger_lt : ∀ (l : List Bool), bitsToInteger l < 2 ^ l.length
  | [] => by decide
  | b :: l => by
    have := VG.Proof.MlDsa.Verify.bitsToInteger_lt l
    have : b.toNat ≤ 1 := by cases b <;> decide
    simp only [bitsToInteger, List.foldr_cons, List.length_cons, Nat.pow_succ] at *
    omega

/-- The coefficients of `BitUnpack(v, a, b)` are in `(b - 2^bitlen (a + b), b]`. -/
theorem bitUnpack_bounds (v : List Byte) (a b : Nat) {i : Nat} (hi : i < n) :
    (b : Int) - 2 ^ bitlen (a + b) < (bitUnpack v a b)[i] ∧ (bitUnpack v a b)[i] ≤ b := by
  simp only [bitUnpack, Vector.getElem_ofFn]
  have := VG.Proof.MlDsa.Verify.bitsToInteger_lt ((List.range (bitlen (a + b))).map fun j =>
    (bytesToBits v).getD (i * bitlen (a + b) + j) false)
  rw [List.length_map, List.length_range] at this
  have e : ((2 ^ bitlen (a + b) : Nat) : Int) = 2 ^ bitlen (a + b) := Int.natCast_pow 2 _
  constructor <;> omega

/-- The parameter sets' `γ₁`. -/
def gamma1s : List Nat := [2 ^ 17, 2 ^ 19]

theorem bitlen_gamma1 {γ₁ : Nat} (h : γ₁ ∈ VG.Proof.MlDsa.Verify.gamma1s) : (2 : Int) ^ bitlen (γ₁ - 1 + γ₁) = 2 * (γ₁ : Int) := by
  simp only [VG.Proof.MlDsa.Verify.gamma1s, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

/-- `‖z[i]‖∞` in `R_q` is its norm in `R`. -/
theorem normRq_vZ {B : Nat} (hB : 0 < B) (p : Params) (hg : p.γ₁ ∈ VG.Proof.MlDsa.Verify.gamma1s) (σ : List Byte) (i : Nat) :
    normRq [toRq (VG.Proof.MlDsa.Verify.vZ p σ i)] < B ↔ ∀ x ∈ (VG.Proof.MlDsa.Verify.vZ p σ i).toList, x.natAbs < B := by
  rw [VG.Proof.MlDsa.Verify.normRq_lt_iff hB]
  have hb := VG.Proof.MlDsa.Verify.bitlen_gamma1 hg
  have hs : p.γ₁ ≤ 2 ^ 19 := by
    simp only [VG.Proof.MlDsa.Verify.gamma1s, List.mem_cons, List.not_mem_nil, or_false] at hg; omega
  constructor
  · intro h x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [Vector.length_toList] at hj
    have hb' := VG.Proof.MlDsa.Verify.bitUnpack_bounds (((σ.drop (p.ctildeLen + VG.Proof.MlDsa.Verify.lenZ p * i)).take (VG.Proof.MlDsa.Verify.lenZ p))) (p.γ₁ - 1) p.γ₁ hj
    rw [hb] at hb'
    have := h (toRq (VG.Proof.MlDsa.Verify.vZ p σ i))[j] (List.mem_iff_getElem.mpr ⟨j, by simpa using hj, by simp⟩)
    simp only [toRq, Vector.getElem_map, Vector.getElem_toList] at this ⊢
    rw [VG.Proof.MlDsa.Verify.normZq_ofInt (by unfold VG.Proof.MlDsa.Verify.vZ; omega) (by unfold VG.Proof.MlDsa.Verify.vZ; omega)] at this
    exact this
  · intro h x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [Vector.length_toList] at hj
    have hb' := VG.Proof.MlDsa.Verify.bitUnpack_bounds (((σ.drop (p.ctildeLen + VG.Proof.MlDsa.Verify.lenZ p * i)).take (VG.Proof.MlDsa.Verify.lenZ p))) (p.γ₁ - 1) p.γ₁ hj
    rw [hb] at hb'
    simp only [toRq, Vector.getElem_toList, Vector.getElem_map]
    rw [VG.Proof.MlDsa.Verify.normZq_ofInt (by unfold VG.Proof.MlDsa.Verify.vZ; omega) (by unfold VG.Proof.MlDsa.Verify.vZ; omega)]
    exact h _ (List.mem_iff_getElem.mpr ⟨j, by simpa using hj, by simp⟩)

/-- `‖z‖∞ < B` exactly when each `‖z[i]‖∞ < B`, in `R_q`. -/
theorem normR_vZ_iff {B : Nat} (hB : 0 < B) (p : Params) (hg : p.γ₁ ∈ VG.Proof.MlDsa.Verify.gamma1s) (σ : List Byte) :
    normR ((List.range p.ℓ).map (VG.Proof.MlDsa.Verify.vZ p σ)) < B ↔ ∀ i < p.ℓ, normRq [toRq (VG.Proof.MlDsa.Verify.vZ p σ i)] < B := by
  rw [VG.Proof.MlDsa.Verify.normR_lt_iff hB]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun i _ => (VG.Proof.MlDsa.Verify.normRq_vZ hB p hg σ i).symm

/-! ## `UseHint` -/

/-- The coefficients of `w₁`: at most `(q - 1)/(2γ₂) - 1`. -/
theorem useHint_le₁ (h : Bool) (r : Zq) : (useHint ((q - 1) / 88) h r).toNat ≤ (q - 1) / (2 * ((q - 1) / 88)) - 1 := by
  have hr := r.isLt
  have e1 : (((q - 1) / (2 * ((q - 1) / 88)) : Nat) : Int) = 44 := rfl
  have e2 : ((2 * ((q - 1) / 88) : Nat) : Int) = 190464 := rfl
  have e3 : ((q : Nat) : Int) = 8380417 := rfl
  have e4 : ((2 * ((q - 1) / 88) / 2 : Nat) : Int) = 95232 := rfl
  have e5 : (q - 1) / (2 * ((q - 1) / 88)) - 1 = 43 := rfl
  unfold useHint decompose modPm
  have hR : 0 ≤ ((r.val : Nat) : Int) ∧ ((r.val : Nat) : Int) < 8380417 := ⟨by omega, by omega⟩
  simp only [e1, e2, e3, e4, e5]
  generalize ((r.val : Nat) : Int) = R at *
  split_ifs <;> omega

theorem useHint_le₂ (h : Bool) (r : Zq) : (useHint ((q - 1) / 32) h r).toNat ≤ (q - 1) / (2 * ((q - 1) / 32)) - 1 := by
  have hr := r.isLt
  have e1 : (((q - 1) / (2 * ((q - 1) / 32)) : Nat) : Int) = 16 := rfl
  have e2 : ((2 * ((q - 1) / 32) : Nat) : Int) = 523776 := rfl
  have e3 : ((q : Nat) : Int) = 8380417 := rfl
  have e4 : ((2 * ((q - 1) / 32) / 2 : Nat) : Int) = 261888 := rfl
  have e5 : (q - 1) / (2 * ((q - 1) / 32)) - 1 = 15 := rfl
  unfold useHint decompose modPm
  have hR : 0 ≤ ((r.val : Nat) : Int) ∧ ((r.val : Nat) : Int) < 8380417 := ⟨by omega, by omega⟩
  simp only [e1, e2, e3, e4, e5]
  generalize ((r.val : Nat) : Int) = R at *
  split_ifs <;> omega

/-- The coefficients of `w₁`: at most `(q - 1)/(2γ₂) - 1`. -/
theorem useHint_le {γ₂ : Nat} (hg : γ₂ ∈ gamma2s) (h : Bool) (r : Zq) :
    (useHint γ₂ h r).toNat ≤ (q - 1) / (2 * γ₂) - 1 := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  exacts [VG.Proof.MlDsa.Verify.useHint_le₁ h r, VG.Proof.MlDsa.Verify.useHint_le₂ h r]

end VG.Proof.MlDsa.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Verify.Final`. -/
section

/-!
# ML-DSA: when verification fails

`verifyMu` is false when the hint is malformed (`verifyMu_hint_none`), not
true when `‖z‖∞` is too large (`verifyMu_norm`), and `none` when a sampler
does not finish within its bound (`verifyMu_rej_none`, `verifyMu_ball_none`);
and bounds for each entry of `Â` give one bound for all of them
(`common_bound`).
-/

namespace VG.Proof.MlDsa.Verify

open VG.Spec.MlDsa

theorem verifyMu_hint_none {p : Params} (b : Bounds) (pk μ : List Byte) {σ : List Byte} (hh : VG.Proof.MlDsa.Verify.vHint p σ = none) :
    verifyMu p b pk μ σ = some false := by
  unfold verifyMu
  rw [VG.Proof.MlDsa.Verify.pkDecode_eq, VG.Proof.MlDsa.Verify.sigDecode_eq, hh]
  rfl

theorem verifyMu_eq {p : Params} (b : Bounds) (pk μ : List Byte) {σ : List Byte} {h : List (Vector Bool n)}
    (hh : VG.Proof.MlDsa.Verify.vHint p σ = some h) :
    ∃ f : List (List Poly) → IPoly → Bool,
      verifyMu p b pk μ σ = (expandA p b (VG.Proof.MlDsa.Verify.vRho pk)).bind fun A => (sampleInBall p.τ b.ball (VG.Proof.MlDsa.Verify.vCt p σ)).bind
        fun c => some (decide (normR ((List.range p.ℓ).map (VG.Proof.MlDsa.Verify.vZ p σ)) < p.γ₁ - p.β) && f A c) := by
  unfold verifyMu
  rw [VG.Proof.MlDsa.Verify.pkDecode_eq, VG.Proof.MlDsa.Verify.sigDecode_eq, hh]
  exact ⟨_, rfl⟩

theorem verifyMu_norm {p : Params} (b : Bounds) (pk μ : List Byte) {σ : List Byte} {h : List (Vector Bool n)}
    (hh : VG.Proof.MlDsa.Verify.vHint p σ = some h) (hn : ¬ normR ((List.range p.ℓ).map (VG.Proof.MlDsa.Verify.vZ p σ)) < p.γ₁ - p.β) :
    verifyMu p b pk μ σ ≠ some true := by
  obtain ⟨f, e⟩ := VG.Proof.MlDsa.Verify.verifyMu_eq b pk μ hh
  rw [e]
  cases expandA p b (VG.Proof.MlDsa.Verify.vRho pk) with
  | none => simp
  | some A =>
    cases sampleInBall p.τ b.ball (VG.Proof.MlDsa.Verify.vCt p σ) with
    | none => simp
    | some c => simp [hn]

theorem mapM_none {α β : Type} {f : α → Option β} : ∀ {l : List α}, (∃ a ∈ l, f a = none) → l.mapM f = none
  | [], ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | a :: l, ⟨x, hx, hn⟩ => by
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hn]; rfl
    · cases f a with
      | none => rfl
      | some y => rw [VG.Proof.MlDsa.Verify.mapM_none ⟨x, hx, hn⟩]; rfl

theorem verifyMu_rej_none {p : Params} (b : Bounds) (pk μ : List Byte) {σ : List Byte} {h : List (Vector Bool n)}
    (hh : VG.Proof.MlDsa.Verify.vHint p σ = some h) {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ)
    (hn : rejNTTPoly b.rejNTT (VG.Proof.MlDsa.Verify.aSeed pk r c) = none) : verifyMu p b pk μ σ = none := by
  obtain ⟨f, e⟩ := VG.Proof.MlDsa.Verify.verifyMu_eq b pk μ hh
  have hA : expandA p b (VG.Proof.MlDsa.Verify.vRho pk) = none :=
    VG.Proof.MlDsa.Verify.mapM_none ⟨r, List.mem_range.mpr hr, VG.Proof.MlDsa.Verify.mapM_none ⟨c, List.mem_range.mpr hc, hn⟩⟩
  rw [e, hA]
  rfl

theorem verifyMu_ball_none {p : Params} (b : Bounds) (pk μ : List Byte) {σ : List Byte} {h : List (Vector Bool n)}
    (hh : VG.Proof.MlDsa.Verify.vHint p σ = some h) (hn : sampleInBall p.τ b.ball (VG.Proof.MlDsa.Verify.vCt p σ) = none) : verifyMu p b pk μ σ = none := by
  obtain ⟨f, e⟩ := VG.Proof.MlDsa.Verify.verifyMu_eq b pk μ hh
  rw [e]
  cases expandA p b (VG.Proof.MlDsa.Verify.vRho pk) with
  | none => rfl
  | some A => rw [Option.bind_some, hn]; rfl

/-- A bound for each of finitely many monotone facts gives one for all. -/
theorem common_bound {P : Nat → Nat → Prop} (hm : ∀ i n n', n ≤ n' → P i n → P i n') :
    ∀ K, (∀ i < K, ∃ n, P i n) → ∃ n, ∀ i < K, P i n
  | 0, _ => ⟨0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | K + 1, h => by
    obtain ⟨n, hn⟩ := VG.Proof.MlDsa.Verify.common_bound hm K fun i hi => h i (by omega)
    obtain ⟨n', hn'⟩ := h K (by omega)
    refine ⟨max n n', fun i hi => ?_⟩
    rcases (by omega : i < K ∨ i = K) with hi | rfl
    · exact hm i _ _ (Nat.le_max_left _ _) (hn i hi)
    · exact hm i _ _ (Nat.le_max_right _ _) hn'

end VG.Proof.MlDsa.Verify

end
