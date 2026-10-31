module

public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Run
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimA
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimC
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimB
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Words
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Local
import VerifiedGarbage.Proof.MlKem.X86.TopSeq
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.DecideAt

/-!
# ML-DSA signing on x86 (32-bit): the checks of an iteration

Once `SampleInBall` succeeded (`ballCall_piece`), the checks (`CS`: what they
keep, with `y`, `w`, the hint, `OK` and `ONES` as far as they got) compute `z`
in place of `y` (`zR_piece`), `w - cs₂` in place of `w` and the norm of its
`LowBits` (`r0R_piece`), and `ct₀`, `w - cs₂ + ct₀` and the hint (`hR_piece`);
`OK` is then 1 exactly when the checks pass (`onesOk_piece`, `pass_iff`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_shr)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

section
variable (p : Params)

/-- `c`, and the values of the checks, of the iteration with counter `κ`. -/
abbrev Cv (s₀ : State) (κ : Nat) : IPoly := cV p (skOf p s₀) (muOf s₀) (rndOf s₀) κ
abbrev Zv (s₀ : State) (κ r : Nat) : Poly := zF p (S1 p s₀) (rppS p s₀) κ (Cv p s₀ κ) r
abbrev W'v (s₀ : State) (κ i : Nat) : Poly := w'F p (Am p s₀) (S2 p s₀) (rppS p s₀) κ (Cv p s₀ κ) i
abbrev R0v (s₀ : State) (κ i : Nat) : Poly := r0F p (Am p s₀) (S2 p s₀) (rppS p s₀) κ (Cv p s₀ κ) i
abbrev CT0v (s₀ : State) (κ i : Nat) : Poly := ct0F (T0 p s₀) (Cv p s₀ κ) i
abbrev W''v (s₀ : State) (κ i : Nat) : Poly := w''F p (Am p s₀) (S2 p s₀) (T0 p s₀) (rppS p s₀) κ (Cv p s₀ κ) i
abbrev Hv (s₀ : State) (κ i : Nat) : Vector Bool n := hF p (Am p s₀) (S2 p s₀) (T0 p s₀) (rppS p s₀) κ (Cv p s₀ κ) i

/-- The checks of the first `r` polynomials. -/
def okZ (s₀ : State) (κ r : Nat) : Bool := (List.range r).all fun j => decide (normRq [Zv p s₀ κ j] < p.γ₁ - p.β)
def okR (s₀ : State) (κ i : Nat) : Bool := (List.range i).all fun j => decide (normRq [R0v p s₀ κ j] < p.γ₂ - p.β)
def okT (s₀ : State) (κ i : Nat) : Bool := (List.range i).all fun j => decide (normRq [CT0v p s₀ κ j] < p.γ₂)
/-- The number of 1s of the first `i` polynomials of the hint. -/
def onesS (s₀ : State) (κ i : Nat) : Nat := ((List.range i).map fun j => hintOnes [Hv p s₀ κ j]).sum

end

theorem all_range_succ {f : Nat → Bool} {r : Nat} :
    (List.range (r + 1)).all f = ((List.range r).all f && f r) := by
  simp only [List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

theorem all_range_iff {f : Nat → Prop} [DecidablePred f] {r : Nat} :
    (List.range r).all (fun j => decide (f j)) = true ↔ ∀ j < r, f j := by
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]

/-- The checks pass exactly when `OK` ends up 1. -/
theorem pass_iff {s₀ : State} {κ : Nat} :
    passV p (skOf p s₀) (muOf s₀) (rndOf s₀) κ ↔
      (okZ p s₀ κ p.ℓ && okR p s₀ κ p.k && okT p s₀ κ p.k && decide (onesS p s₀ κ p.k ≤ p.ω)) = true := by
  simp only [Bool.and_eq_true, okZ, okR, okT, all_range_iff, onesS, passV, passF, and_assoc]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, decide_eq_true d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, of_decide_eq_true d⟩⟩

section
variable (p : Params)
abbrev PassV (σ : State) (κ : Nat) : Prop :=
  passF p (Am p σ) (S1 p σ) (S2 p σ) (T0 p σ) (rppS p σ) κ (Cv p σ κ)
abbrev ZOk (σ : State) (κ : Nat) : Prop := ∀ j < p.ℓ, normRq [Zv p σ κ j] < p.γ₁-p.β
abbrev R0Ok (σ : State) (κ : Nat) : Prop := ∀ j < p.k, normRq [R0v p σ κ j] < p.γ₂-p.β
abbrev iterF (σ : State) (b : Bounds) (κ : Nat) := iterV p (skOf p σ) (muOf σ) (rndOf σ) b κ
abbrev leakL (σ : State) (n κ : Nat) :=
  signLeakLoop p maxBounds (amat p (Am p σ)) ((List.range p.ℓ).map (S1 p σ))
    ((List.range p.k).map (S2 p σ)) ((List.range p.k).map (T0 p σ)) (muOf σ) (rppS p σ) n κ
abbrev LeakEq (t : Nat) (σ₁ σ₂ : State) : Prop := leakL p σ₁ (1000-t) (p.ℓ*t) = leakL p σ₂ (1000-t) (p.ℓ*t)
end

/-- What the branches of the checks need two runs to agree on: whether the
first `r` polynomials of `z` passed, for each `r` (the checks stop at the
first that fails), whether `z` and the first `i` polynomials of `r₀` passed,
for each `i`, and whether the iteration passed. -/
abbrev ChecksAgree (p : Params) (t : Nat) (σ₁ σ₂ : State) : Prop :=
  (∀ r ≤ p.ℓ, (∀ j < r, normRq [Zv p σ₁ (p.ℓ * t) j] < p.γ₁ - p.β) ↔
    (∀ j < r, normRq [Zv p σ₂ (p.ℓ * t) j] < p.γ₁ - p.β)) ∧
  (∀ i ≤ p.k, (ZOk p σ₁ (p.ℓ * t) ∧ ∀ j < i, normRq [R0v p σ₁ (p.ℓ * t) j] < p.γ₂ - p.β) ↔
    (ZOk p σ₂ (p.ℓ * t) ∧ ∀ j < i, normRq [R0v p σ₂ (p.ℓ * t) j] < p.γ₂ - p.β)) ∧
  (PassV p σ₁ (p.ℓ * t) ↔ PassV p σ₂ (p.ℓ * t))

theorem iterF_eq {p : Params} (hp : ParamsOk p) {σ : State} {b : Bounds} {κ : Nat} :
    iterF p σ b κ = (sampleInBall p.τ b.ball (CTv p σ κ)).map fun c =>
      (CTv p σ κ, if passF p (Am p σ) (S1 p σ) (S2 p σ) (T0 p σ) (rppS p σ) κ c then
        some ((List.range p.ℓ).map (zF p (S1 p σ) (rppS p σ) κ c),
          (List.range p.k).map (hF p (Am p σ) (S2 p σ) (T0 p σ) (rppS p σ) κ c)) else none) :=
  iterV_eq hp b

theorem iter_rej {p : Params} {σ : State} {κ : Nat} (hp : ParamsOk p)
    (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) (hn : ¬ PassV p σ κ) :
    iterF p σ maxBounds κ = some (CTv p σ κ, none) := iterV_rej hp hs hn

section
variable {p : Params} {σ₁ σ₂ : State} {t : Nat}
theorem leq_step (h : LeakEq p t σ₁ σ₂) (ht : t < 814) :
    signLeakLoop p maxBounds (amat p (Am p σ₁)) ((List.range p.ℓ).map (S1 p σ₁)) ((List.range p.k).map (S2 p σ₁))
      ((List.range p.k).map (T0 p σ₁)) (muOf σ₁) (rppS p σ₁) ((999 - t) + 1) (p.ℓ * t) =
    signLeakLoop p maxBounds (amat p (Am p σ₂)) ((List.range p.ℓ).map (S1 p σ₂)) ((List.range p.k).map (S2 p σ₂))
      ((List.range p.k).map (T0 p σ₂)) (muOf σ₂) (rppS p σ₂) ((999 - t) + 1) (p.ℓ * t) := by
  rw [show 999 - t + 1 = 1000 - t by omega]; exact h

theorem leq_ct (h : LeakEq p t σ₁ σ₂) (ht : t < 814) : CTv p σ₁ (p.ℓ * t) = CTv p σ₂ (p.ℓ * t) := by
  have := (leakF_step (leq_step h ht)).1
  rwa [signCommit_eq, signCommit_eq] at this

theorem leq_succ (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hr : ∃ ct, iterF p σ₁ maxBounds (p.ℓ * t) = some (ct, none)) : LeakEq p (t + 1) σ₁ σ₂ := by
  have := ((leakF_step (leq_step h ht)).2.1 hr).2
  unfold LeakEq
  rw [show 1000 - (t + 1) = 999 - t by omega, Nat.mul_succ]
  exact this

theorem outTag_eq (hp : ParamsOk p) {σ : State} {κ : Nat} (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    outTag (iterF p σ maxBounds κ) = if PassV p σ κ then
      1 :: ((List.range p.k).map (Hv p σ κ)).flatMap (fun hi => hi.toList.map Bool.toNat) else [0] := by
  rw [iterF_eq hp, cV_eq hs, Option.map_some]
  by_cases hv : PassV p σ κ
  · rw [ifp hv, ifp hv]; rfl
  · rw [ifn hv, ifn hv]; rfl

theorem leq_pass (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome) :
    PassV p σ₁ (p.ℓ * t) ↔ PassV p σ₂ (p.ℓ * t) := by
  have e := (leakF_step (leq_step h ht)).2.2
  rw [outTag_eq hp hs₁, outTag_eq hp hs₂] at e
  by_cases h1 : PassV p σ₁ (p.ℓ * t) <;> by_cases h2 : PassV p σ₂ (p.ℓ * t)
  · exact iff_of_true h1 h2
  · rw [ifp h1, ifn h2] at e; cases e
  · rw [ifn h1, ifp h2] at e; cases e
  · exact iff_of_false h1 h2

/-- `signRejectTag`'s value: which check failed, and for those of `z` and
`r₀` the first polynomial that failed it. -/
def tagFn (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] (x y : Nat) : Nat :=
  if ¬ a then 5 * x else if ¬ b then 2 + 5 * y else if ¬ c then 3 else 4

theorem tagFn_eq {a b c a' b' c' : Prop} [Decidable a] [Decidable b] [Decidable c] [Decidable a'] [Decidable b']
    [Decidable c'] {x y x' y' : Nat} (h : tagFn a b c x y = tagFn a' b' c' x' y') :
    (a ↔ a') ∧ (¬ a → x = x') ∧ (a ∧ b ↔ a' ∧ b') ∧ (a → ¬ b → y = y') := by
  unfold tagFn at h
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases ha' : a' <;> by_cases hb' : b' <;>
    by_cases hc' : c' <;> simp only [ha, hb, hc, ha', hb', hc', not_true_eq_false, not_false_eq_true,
      ite_true, ite_false] at h <;> first | omega | (simp_all <;> omega)

/-- The first polynomial of `z` that fails its check, or `ℓ`. -/
abbrev zFirst (p : Params) (σ : State) (κ : Nat) : Nat :=
  (List.range p.ℓ).findIdx fun r => decide (normRq [Zv p σ κ r] ≥ p.γ₁ - p.β)

/-- The first polynomial of `r₀` that fails its check, or `k`. -/
abbrev rFirst (p : Params) (σ : State) (κ : Nat) : Nat :=
  (List.range p.k).findIdx fun i => decide (normRq [R0v p σ κ i] ≥ p.γ₂ - p.β)

theorem tag_eq (hp : ParamsOk p) {σ : State} {κ : Nat}
    (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    signRejectTag p maxBounds (amat p (Am p σ)) ((List.range p.ℓ).map (S1 p σ)) ((List.range p.k).map (S2 p σ))
      ((List.range p.k).map (T0 p σ)) (muOf σ) (rppS p σ) κ =
      tagFn (ZOk p σ κ) (R0Ok p σ κ) (∀ j < p.k, normRq [CT0v p σ κ j] < p.γ₂) (zFirst p σ κ) (rFirst p σ κ) := by
  rw [signRejectTag_eqF hp, show ctF p (Am p σ) (muOf σ) (rppS p σ) κ = CTv p σ κ from rfl, cV_eq hs]
  rfl

/-- The first `r ≤ n` polynomials pass a check exactly when the first that
fails it comes at `r` or later. -/
theorem prefix_ok {n B : Nat} (f : Nat → Poly) {r : Nat} (hr : r ≤ n) :
    (∀ j < r, normRq [f j] < B) ↔ r ≤ (List.range n).findIdx fun j => decide (normRq [f j] ≥ B) := by
  rw [← prefix_findIdx n _ hr]
  simp only [decide_eq_false_iff_not, ge_iff_le, Nat.not_le]

/-- Two runs that agree on what the iterations from `t` leak agree on the
checks of iteration `t` that pass, polynomial by polynomial. -/
theorem leq_agree (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome) : ChecksAgree p t σ₁ σ₂ := by
  have hpass := leq_pass hp h ht hs₁ hs₂
  by_cases h1 : PassV p σ₁ (p.ℓ * t)
  · have h2 := hpass.mp h1
    exact ⟨fun r hr => iff_of_true (fun j hj => h1.1 j (by omega)) (fun j hj => h2.1 j (by omega)),
      fun i hi => iff_of_true ⟨h1.1, fun j hj => h1.2.1 j (by omega)⟩ ⟨h2.1, fun j hj => h2.2.1 j (by omega)⟩, hpass⟩
  · have h2 : ¬ PassV p σ₂ (p.ℓ * t) := fun h2 => h1 (hpass.mpr h2)
    have e := leakF_tag (leq_step h ht) (iter_rej hp hs₁ h1) (iter_rej hp hs₂ h2)
    rw [tag_eq hp hs₁, tag_eq hp hs₂] at e
    obtain ⟨ea, ex, eab, ey⟩ := tagFn_eq e
    refine ⟨fun r hr => ?_, fun i hi => ?_, hpass⟩
    · by_cases hz : ZOk p σ₁ (p.ℓ * t)
      · exact iff_of_true (fun j hj => hz j (by omega)) (fun j hj => ea.mp hz j (by omega))
      · rw [prefix_ok _ hr, prefix_ok _ hr]; exact iff_of_eq (congrArg (r ≤ ·) (ex hz))
    · by_cases hz : ZOk p σ₁ (p.ℓ * t)
      · have hz' := ea.mp hz
        by_cases hr0 : R0Ok p σ₁ (p.ℓ * t)
        · have hr0' := (eab.mp ⟨hz, hr0⟩).2
          exact iff_of_true ⟨hz, fun j hj => hr0 j (by omega)⟩ ⟨hz', fun j hj => hr0' j (by omega)⟩
        · rw [and_iff_right hz, and_iff_right hz', prefix_ok _ hi, prefix_ok _ hi]
          exact iff_of_eq (congrArg (i ≤ ·) (ey hz hr0))
      · exact iff_of_false (fun h => hz h.1) (fun h => hz (ea.mpr h.1))

end

theorem run_agree {F : PrimsOk P} {t : Nat} {x y : State} (ps : PS p) (hq : SPub p x y)
    (h : Run p F t x) (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p x (p.ℓ*t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p y (p.ℓ*t))).isSome) : ChecksAgree p t x y :=
  leq_agree ps.hok (run_leak ps hq h) h.lt hs₁ hs₂

/-! ## The hint -/

/-- The first `nh` polynomials of the hint, in the slots from 5. -/
def HF (s₀ : State) (m : Mem) (nh : Nat) (f : Nat → Vector Bool n) : Prop :=
  ∀ j < nh, HintIs m (Buf.addr s₀ (pS (5 + j))) 1 [f j]

theorem hintIs_congr {m m' : Mem} {a : Addr} {h : Vector Bool n}
    (e : ∀ x < 1024, m' (a + BitVec.ofNat 64 x) = m (a + BitVec.ofNat 64 x)) (hh : HintIs m a 1 [h]) :
    HintIs m' a 1 [h] := by
  refine ⟨hh.1, fun i hi j hj => ?_⟩
  have : coeffAt m' a (256 * i + j) = coeffAt m a (256 * i + j) := by
    unfold coeffAt
    refine Mem.readW_congr fun t ht => ?_
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact e _ (by have : n = 256 := rfl; omega_arith)
  rw [this]; exact hh.2 i hi j hj

theorem HF.keep {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {nh : Nat} (hn : 5 + nh ≤ nS p)
    (h : ∀ c ∈ bs, Out p (oP 5) (oP (5 + nh)) c) {f : Nat → Vector Bool n} (hf : HF s₀ m nh f) : HF s₀ m' nh f :=
  fun j hj => hintIs_congr (VG.Proof.MlKem.X86.Top.keep hp (N := N) (by show N + 16 ≤ 96; omega_arith)
    (apart_of (slot_ok' ps (by omega_arith)) rfl fun c hc => by
      obtain ⟨h₁, h₂⟩ := h c hc
      exact ⟨h₁, fun e => by simp only [oP] at h₂ ⊢; have := h₂ e; omega_arith⟩) fr) (hf j hj)

theorem HF.snoc {s₀ : State} {m : Mem} {nh : Nat} {f : Nat → Vector Bool n} (h : HF s₀ m nh f)
    (h' : HintIs m (Buf.addr s₀ (pS (5 + nh))) 1 [f nh]) : HF s₀ m (nh + 1) f := fun j hj => by
  by_cases e : j < nh
  · exact h j e
  · rw [show j = nh by omega_arith]; exact h'

/-- Slot `r` of a family changed, the others kept. -/
theorem Fam.upd {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {b n r : Nat} (hb : b + n ≤ nS p) (hr : r < n)
    (h : ∀ c ∈ bs, Out p (oP b) (oP (b + r)) c ∧ Out p (oP (b + r + 1)) (oP (b + n)) c) {f g : Nat → Poly}
    (hf : Fam s₀ m b n f) (hv : PolyIs m' (Buf.addr s₀ (pS (b + r))) (g r)) (hg : ∀ j < n, j ≠ r → g j = f j) :
    Fam s₀ m' b n g := fun j hj => by
  by_cases e : j = r
  · subst e; exact hv
  · rw [hg j hj e]
    exact keepP hp ps hN fr (by omega_arith) (fun c hc => by
      obtain ⟨⟨h₁, h₂⟩, -, h₃⟩ := h c hc
      exact ⟨h₁, fun ea => by
        have := h₂ ea; have := h₃ ea; simp only [oP] at *
        rcases (by omega_arith : j < r ∨ r < j) with hj' | hj' <;> omega_arith⟩) (hf j hj)

/-! ## The state of the checks -/

/-- The checks of iteration `t`, with `y`, `w`, the first `nh` polynomials of
the hint, `OK` and `ONES` as `fY`, `fW`, `okb` and `ones` say. -/
structure CS (p : Params) (t : Nat) (fY fW : State → Nat → Poly) (nh : Nat) (okb : State → Bool)
    (ones : State → Nat) (s₀ s : State) : Prop where
  it : IT p t s₀ s
  ct : bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * t)
  c : PolyIs s.mem (Buf.addr s₀ cP) (chF (Cv p s₀ (p.ℓ * t)))
  fy : Fam s₀ s.mem (yB p) p.ℓ (fY s₀)
  fw : Fam s₀ s.mem (wB p) p.k (fW s₀)
  fh : HF s₀ s.mem nh (Hv p s₀ (p.ℓ * t))
  ok : scw s₀ s oOK = if okb s₀ then 1 else 0
  ones : scw s₀ s oONES = BitVec.ofNat 32 (ones s₀)
  nh : nh ≤ p.k

section
variable {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
  {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
  {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
include hp ps h c' hN fr

omit c' in
theorem CS.ct_keep (hb : ∀ c ∈ bs, Out p oCT (oCT + 64) c) :
    bytesAt s'.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * t) := by
  have := ps.hcLen
  rw [keepB hp hN fr (by ofsd) fun c hc => ⟨(hb c hc).1, fun e => by
    have := (hb c hc).2 e; simp only [oCT] at this ⊢; omega_arith⟩, h.ct]

theorem CS.keep (hb : ∀ c ∈ bs, OutC p nh c) : CS p t fY fW nh okb ones s₀ s' := by
  have := h.nh
  exact ⟨h.it.keep hp ps c' hN fr fun c hc => (hb c hc).1, h.ct_keep hp ps hN fr fun c hc => (hb c hc).2.2.1,
    keepP hp ps hN fr (j := 0) (by simp only [nS]; omega_arith) (fun c hc => (hb c hc).2.1) h.c,
    h.fy.keep hp ps hN fr (by simp only [nS, yB]; omega_arith) fun c hc => ⟨(hb c hc).2.2.2.1.1, fun e => by
      have := (hb c hc).2.2.2.1.2 e; simp only [oP, yB, wB] at this ⊢; omega_arith⟩,
    h.fw.keep hp ps hN fr (by simp only [nS, wB]; omega_arith) fun c hc => ⟨(hb c hc).2.2.2.1.1, fun e => by
      have := (hb c hc).2.2.2.1.2 e; simp only [oP, yB, wB] at this ⊢; omega_arith⟩,
    h.fh.keep hp ps hN fr (by simp only [nS]; omega_arith) fun c hc => (hb c hc).2.2.2.2.1,
    by rw [scw, keepW' hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2.2.2.2.2.1]; exact h.ok,
    by rw [scw, keepW' hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2.2.2.2.2.2]; exact h.ones,
    h.nh⟩

end

/-! ## `SampleInBall` -/

theorem ball_val {τ : Nat} {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => (sampleInBall τ b.ball x).map toRq) r out) (h1 : r = 1)
    (hm : (sampleInBall τ maxBounds.ball x).isSome) :
    out = toRq ((sampleInBall τ maxBounds.ball x).getD (Vector.replicate n 0)) := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
    have e1 := sampleInBall_mono (Nat.le_max_left b.ball maxBounds.ball) hc
    have e2 := sampleInBall_mono (Nat.le_max_right b.ball maxBounds.ball) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

/-- After `SampleInBall` in iteration `t`. -/
structure IB (p : Params) (F : PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  cc : CC p t s₀ s
  run : Run p F t s₀
  eax : s.gpr .eax = if F.ballF p.τ (CTv p s₀ (p.ℓ * t)) then 1 else 0
  yes : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true → PolyIs s.mem (Buf.addr s₀ cP) (toRq (Cv p s₀ (p.ℓ * t)))
  no : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = false → sampleInBall p.τ minBounds.ball (CTv p s₀ (p.ℓ * t)) = none

theorem CC.keep {t : Nat} {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CC p t s₀ s)
    (c' : Ctx (Y p) s₀ s') {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, (OutI p c ∧ Out p (oP (yB p)) (oP (wB p + p.k)) c) ∧ Out p oCT (oCT + 64) c) : CC p t s₀ s' := by
  have := ps.hcLen
  exact ⟨h.cw.keep hp ps (Nat.le_refl _) c' hN fr fun c hc => (hb c hc).1, by
    rw [keepB hp hN fr (by ofsd) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [oCT] at this ⊢; omega_arith⟩, h.ct]⟩

/-- `c = SampleInBall(c̃)` to `ĉ`'s slot. -/
theorem ballCall_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (fun s₀ s => CC p t s₀ s ∧ Run p F t s₀) (IB p F t) (ballAt P (cLen p) p.τ cP) := by
  have := ps.hcLen
  refine ball_piece F.ball (F.ok _ (by simp)) (cLen p) p.τ ps.hball SC oCT SC (oP 0) SC oPS (by ofsd)
    (fun _ _ _ h => h.1.cw.cm.it.kd.ctx) (fun s₀ s₀' s s' hp hp' hq h h' => ?_)
    fun s₀ s s' hp h c' fr heax hred hout => ?_
  · rw [h.1.ct, h'.1.ct]; exact (run_at ps hq h.2).1
  · rw [h.1.ct] at heax hout
    refine ⟨h.1.keep hp ps c' (by decide) fr (by ofsd), h.2, heax, fun hy => ?_, fun hn => ?_⟩
    · rw [hy] at heax; simp only [↓reduceIte] at heax
      exact ⟨hred heax, ball_val hout heax (F.ballMax _ _ hy)⟩
    · rw [hn] at heax
      rcases hout with ⟨h1, _⟩ | ⟨_, h0⟩
      · rw [heax] at h1; cases h1
      · simpa using h0

/-- Whether `SampleInBall` succeeded, in a run that reaches iteration `t`. -/
def ballB (p : Params) (F : PrimsOk P) (t : Nat) (s₀ : State) : Bool :=
  decide (Run p F t s₀) && F.ballF p.τ (CTv p s₀ (p.ℓ * t))

theorem ballB_eq {F : PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') :
    ballB p F t s₀ = ballB p F t s₀' := by
  unfold ballB
  by_cases h : Run p F t s₀
  · rw [decide_eq_true h, decide_eq_true ((run_iff ps hq).mp h), (run_at ps hq h).1]
  · rw [decide_eq_false h, decide_eq_false fun h' => h ((run_iff ps hq).mpr h'), Bool.false_and, Bool.false_and]

theorem ballB_of {F : PrimsOk P} {t : Nat} {s₀ : State} (h : Run p F t s₀) :
    ballB p F t s₀ = F.ballF p.τ (CTv p s₀ (p.ℓ * t)) := by
  simp only [ballB, decide_eq_true h, Bool.true_and]

/-- `ZF ← eax = 0`, after `SampleInBall`. -/
theorem ballTest_piece (F : PrimsOk P) (t : Nat) :
    SP p (IB p F t) (fun s₀ s => ∃ s', IB p F t s₀ s' ∧ Ctx (Y p) s₀ s ∧ s.mem = s'.mem ∧
      s.zf = some (!ballB p F t s₀)) (.block [.alu .test .eax (.reg .eax)]) := by
  refine blk_piece (fun _ _ _ h => h.cc.cw.cm.it.kd.ctx) (fun s₀ s hp h => wp_test fun s₁ o₁ z₁ =>
    WP.block_nil_iff.mpr ⟨s, h, h.cc.cw.cm.it.kd.ctx.only o₁ (by simp) (by simp), o₁.mem, ?_⟩) rfl
  rw [z₁, h.eax, ballB_of h.run]
  cases F.ballF p.τ (CTv p s₀ (p.ℓ * t)) <;> rfl

/-! ## The start of the checks -/

/-- `y`, with `z` in place of its first `r` polynomials. -/
abbrev zY (p : Params) (t r : Nat) (s₀ : State) (j : Nat) : Poly :=
  if j < r then Zv p s₀ (p.ℓ * t) j else Yv p s₀ (p.ℓ * t) j

/-- `w`, with `w - cs₂` in place of its first `i` polynomials. -/
abbrev rW (p : Params) (t i : Nat) (s₀ : State) (j : Nat) : Poly :=
  if j < i then W'v p s₀ (p.ℓ * t) j else Wv p s₀ (p.ℓ * t) j

/-- `w - cs₂`, with `w - cs₂ + ct₀` in place of its first `i` polynomials. -/
abbrev hW (p : Params) (t i : Nat) (s₀ : State) (j : Nat) : Poly :=
  if j < i then W''v p s₀ (p.ℓ * t) j else W'v p s₀ (p.ℓ * t) j

theorem zY_lt {t r j : Nat} {s₀ : State} (h : j < r) : zY p t r s₀ j = Zv p s₀ (p.ℓ * t) j := ifp h _ _
theorem zY_ge {t r j : Nat} {s₀ : State} (h : ¬ j < r) : zY p t r s₀ j = Yv p s₀ (p.ℓ * t) j := ifn h _ _
theorem rW_lt {t i j : Nat} {s₀ : State} (h : j < i) : rW p t i s₀ j = W'v p s₀ (p.ℓ * t) j := ifp h _ _
theorem rW_ge {t i j : Nat} {s₀ : State} (h : ¬ j < i) : rW p t i s₀ j = Wv p s₀ (p.ℓ * t) j := ifn h _ _
theorem hW_lt {t i j : Nat} {s₀ : State} (h : j < i) : hW p t i s₀ j = W''v p s₀ (p.ℓ * t) j := ifp h _ _
theorem hW_ge {t i j : Nat} {s₀ : State} (h : ¬ j < i) : hW p t i s₀ j = W'v p s₀ (p.ℓ * t) j := ifn h _ _

/-- The family whose first `r` values are `g` changed at `r`, for `r + 1`. -/
theorem upd_step {α : Type} {f g : Nat → α} {r j : Nat} (h : j ≠ r) :
    (if j < r + 1 then g j else f j) = if j < r then g j else f j := by
  by_cases e : j < r
  · rw [ifp (by omega_arith : j < r + 1), ifp e]
  · rw [ifn (by omega_arith : ¬ j < r + 1), ifn e]

/-- What the checks start from. -/
structure KP (p : Params) (F : PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  cc : CC p t s₀ s
  run : Run p F t s₀
  ball : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true

theorem CC.ofMem {t : Nat} {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CC p t s₀ s')
    (c : Ctx (Y p) s₀ s) (hm : s.mem = s'.mem) : CC p t s₀ s :=
  h.keep hp ps c (N := 0) (bs := []) (by decide) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- `OK ← 1` and `ONES ← 0`. -/
theorem checksInit_piece (ps : PS p) (t : Nat) :
    SP p (fun s₀ s => CC p t s₀ s ∧ PolyIs s.mem (Buf.addr s₀ cP) (chF (Cv p s₀ (p.ℓ * t))))
      (CS p t (zY p t 0) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) 0) (fun _ => 0))
      (.block (st32 oOK 1 ++ st32 oONES 0)) := by
  refine blk_piece (fun _ _ _ h => h.1.cw.cm.it.kd.ctx) (fun s₀ s hp h => ?_) rfl
  refine wp_st32 hp h.1.cw.cm.it.kd.ctx (sc_ok ps (by decide) (by decide)) 1 fun s₁ c₁ f₁ v₁ => ?_
  rw [← List.append_nil (st32 oONES 0)]
  refine wp_st32 hp c₁ (sc_ok ps (by decide) (by decide)) 0 fun s₂ c₂ f₂ v₂ => WP.block_nil_iff.mpr ?_
  have g₁ := (h.1.keep hp ps c₁ (N := 80) (by decide) (fr0 hp (by decide) f₁) (by ofsd))
  have g₂ := (g₁.keep hp ps c₂ (N := 80) (by decide) (fr0 hp (by decide) f₂) (by ofsd))
  have hc := keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) f₁) (j := 0) (by simp only [nS]; omega_arith) (by ofsd) h.2
  have hc' := keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) f₂) (j := 0) (by simp only [nS]; omega_arith) (by ofsd) hc
  refine ⟨g₂.cw.cm.it, g₂.ct, hc', g₂.cw.cm.fy.congr fun j hj => by simp, g₂.cw.fw, fun j hj => absurd hj (Nat.not_lt_zero _),
    ?_, v₂, Nat.zero_le _⟩
  rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) f₂) (sc_ok' ps (by decide) (by decide)) (by ofsd)]
  exact v₁

/-! ## Norms -/

/-- `OK ← OK ∧ b`, with `eax = b`. -/
theorem CS.setOK {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (fr : Frame (FR s₀ [sc oOK 4] 0) s.mem s'.mem) (b : State → Bool)
    (v : scw s₀ s' oOK = scw s₀ s oOK &&& s.gpr .eax) (he : s.gpr .eax = if b s₀ then 1 else 0) :
    CS p t fY fW nh (fun s₀ => okb s₀ && b s₀) ones s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (N := 80) (by decide) (fr0 hp (by decide) fr) (by ofsd),
    h.ct_keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by ofsd),
    keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (j := 0) (by simp only [nS]; omega_arith) (by ofsd) h.c,
    h.fy.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS, yB]; omega_arith) (by ofsd),
    h.fw.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS, wB]; omega_arith) (by ofsd),
    h.fh.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS]; omega_arith) (by ofsd),
    by rw [v, h.ok, he, and01], ?_, h.nh⟩
  rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) fr) (sc_ok' ps (by decide) (by decide)) (by ofsd)]
  exact h.ones

/-- `OK ← OK ∧ ‖f‖∞ < bnd`, for the polynomial `v` in slot `j`, which stays. -/
theorem normAnd_piece (F : PrimsOk P) (ps : PS p) {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool}
    {ones : State → Nat} (j : Nat) (hj : j < nS p) (bnd : Nat) (hb : bnd < 2 ^ 32) (v : State → Poly) :
    SP p (fun s₀ s => CS p t fY fW nh okb ones s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS j)) (v s₀))
      (fun s₀ s => CS p t fY fW nh (fun s₀ => okb s₀ && decide (normRq [v s₀] < bnd)) ones s₀ s ∧
        PolyIs s.mem (Buf.addr s₀ (pS j)) (v s₀)) (normAt P (pS j) bnd) := by
  refine Piece.seq (B := fun s₀ s => (CS p t fY fW nh okb ones s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS j)) (v s₀)) ∧
      s.gpr .eax = if normRq [v s₀] < bnd then 1 else 0)
    (norm_piece F.normLt (F.ok _ (by simp)) bnd hb SC (oP j) (slot_ok' ps hj) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr he => ⟨⟨h.1.keep hp ps c' (by decide) fr (by simp),
        keepP hp ps (by decide) fr hj (by simp) h.2⟩, by rw [he, h.2.2]⟩) ?_
  refine blk_piece (fun _ _ _ h => h.1.1.it.kd.ctx) (fun s₀ s hp h => wp_andOK hp h.1.1.it.kd.ctx ps
    fun s' c' fr v' => ⟨h.1.1.setOK hp ps c' fr (fun s₀ => decide (normRq [v s₀] < bnd)) v' ?_,
      keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) hj (by ofsd) h.1.2⟩) rfl
  rw [h.2]; by_cases e : normRq [v s₀] < bnd <;> simp [e]

theorem CS.congr {t nh : Nat} {fY fY' fW fW' : State → Nat → Poly} {okb okb' : State → Bool} {ones : State → Nat}
    {s₀ s : State} (h : CS p t fY fW nh okb ones s₀ s) (e₁ : ∀ j < p.ℓ, fY s₀ j = fY' s₀ j)
    (e₂ : ∀ j < p.k, fW s₀ j = fW' s₀ j) (e₃ : okb s₀ = okb' s₀) : CS p t fY' fW' nh okb' ones s₀ s :=
  { h with fy := h.fy.congr e₁, fw := h.fw.congr e₂, ok := by rw [h.ok, e₃] }

/-- Slot `r` of `y` changed. -/
theorem CS.updY {t nh r : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (hr : r < p.ℓ) (fr : Frame (FR s₀ [pS (yB p + r)] 80) s.mem s'.mem) {fY' : State → Nat → Poly}
    (hv : PolyIs s'.mem (Buf.addr s₀ (pS (yB p + r))) (fY' s₀ r)) (hg : ∀ j < p.ℓ, j ≠ r → fY' s₀ j = fY s₀ j) :
    CS p t fY' fW nh okb ones s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (by decide) fr (by ofsd), h.ct_keep hp ps (by decide) fr (by ofsd),
    keepP hp ps (by decide) fr (j := 0) (by simp only [nS]; omega_arith) (by ofsd) h.c,
    h.fy.upd hp ps (by decide) fr (by simp only [nS, yB]; omega_arith) hr (by ofsd) hv hg,
    h.fw.keep hp ps (by decide) fr (by simp only [nS, wB]; omega_arith) (by ofsd),
    h.fh.keep hp ps (by decide) fr (by simp only [nS]; omega_arith) (by ofsd),
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd)]; exact h.ok,
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd)]; exact h.ones, h.nh⟩

/-- Slot `i` of `w` changed. -/
theorem CS.updW {t nh i : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (hi : i < p.k) (fr : Frame (FR s₀ [pS (wB p + i)] 80) s.mem s'.mem) {fW' : State → Nat → Poly}
    (hv : PolyIs s'.mem (Buf.addr s₀ (pS (wB p + i))) (fW' s₀ i)) (hg : ∀ j < p.k, j ≠ i → fW' s₀ j = fW s₀ j) :
    CS p t fY fW' nh okb ones s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (by decide) fr (by ofsd), h.ct_keep hp ps (by decide) fr (by ofsd),
    keepP hp ps (by decide) fr (j := 0) (by simp only [nS]; omega_arith) (by ofsd) h.c,
    h.fy.keep hp ps (by decide) fr (by simp only [nS, yB]; omega_arith) (by ofsd),
    h.fw.upd hp ps (by decide) fr (by simp only [nS, wB]; omega_arith) hi (by ofsd) hv hg,
    h.fh.keep hp ps (by decide) fr (by simp only [nS]; omega_arith) (by ofsd),
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd)]; exact h.ok,
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd)]; exact h.ones, h.nh⟩

/-! ## `z` -/

/-- `z[r] = y[r] + NTT⁻¹(ĉ ŝ₁[r])` in place of `y[r]`, and its norm. -/
theorem zR_piece (F : PrimsOk P) (ps : PS p) (t r : Nat) (hr : r < p.ℓ) :
    SP p (CS p t (zY p t r) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) r) (fun _ => 0))
      (CS p t (zY p t (r + 1)) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) (r + 1)) (fun _ => 0))
      (zR P p r) := by
  have hj : s1B p + r < nS p := by simp only [nS, s1B]; omega_arith
  have hy : yB p + r < nS p := by simp only [nS, yB]; omega_arith
  have hβ := ps.hβ
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t r) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) r) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (S1 p s₀ r)))
    (mul_piece F.mul (F.ok _ (by simp)) SC (oP 1) SC (oP 0) SC (oP (s1B p + r)) (by ofsd)
      (fun _ _ _ h => ⟨h.it.kd.ctx, h.c.1, (fam_at h.it.kd.dk.f1 hr).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofsd), by
        rw [h.c.2, (fam_at h.it.kd.dk.f1 hr).2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t r) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) r) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (nttInv (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (S1 p s₀ r))))
    (inPlace_piece (t := nttInv) F.invNtt (F.ok _ (by simp)) t1P rfl (by ofsd) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofsd), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := CS p t (zY p t (r + 1)) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) r) (fun _ => 0))
    (acc_piece (op := add) F.add (F.ok _ (by simp)) SC (oP (yB p + r)) SC (oP 1) (by ofsd)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, (fam_at h.1.fy hr).1, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => h.1.updY hp ps c' hr fr (by
        rw [(fam_at h.1.fy hr).2, h.2.2, zY_ge (Nat.lt_irrefl r)] at hq
        rw [zY_lt (Nat.lt_succ_self r)]; exact hq) fun j _ hjr => upd_step hjr) ?_
  refine (normAnd_piece F ps (yB p + r) hy (p.γ₁ - p.β) (by omega_arith) (fun s₀ => Zv p s₀ (p.ℓ * t) r)).mono
    (fun s₀ s _ h => ⟨h, by have := fam_at h.fy hr; rwa [zY_lt (Nat.lt_succ_self r)] at this⟩)
    fun s₀ s _ h => h.1.congr (fun _ _ => rfl)
      (fun _ _ => rfl) (by simp only [okZ, all_range_succ])

/-! ## `r₀` -/

/-- `w[i] - NTT⁻¹(ĉ ŝ₂[i])` in place of `w[i]`, and the norm of its `LowBits`. -/
theorem r0R_piece (F : PrimsOk P) (ps : PS p) (t i : Nat) (hi : i < p.k) :
    SP p (CS p t (zY p t p.ℓ) (rW p t i) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0))
      (CS p t (zY p t p.ℓ) (rW p t (i + 1)) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) (i + 1))
        (fun _ => 0)) (r0R P p i) := by
  have hj : s2B p + i < nS p := by simp only [nS, s2B]; omega_arith
  have hβ := ps.hβ
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t p.ℓ) (rW p t i) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (S2 p s₀ i)))
    (mul_piece F.mul (F.ok _ (by simp)) SC (oP 1) SC (oP 0) SC (oP (s2B p + i)) (by ofsd)
      (fun _ _ _ h => ⟨h.it.kd.ctx, h.c.1, (fam_at h.it.kd.dk.f2 hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofsd), by
        rw [h.c.2, (fam_at h.it.kd.dk.f2 hi).2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t p.ℓ) (rW p t i) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (nttInv (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (S2 p s₀ i))))
    (inPlace_piece (t := nttInv) F.invNtt (F.ok _ (by simp)) t1P rfl (by ofsd) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofsd), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := CS p t (zY p t p.ℓ) (rW p t (i + 1)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0))
    (acc_piece (op := sub) F.sub (F.ok _ (by simp)) SC (oP (wB p + i)) SC (oP 1) (by ofsd)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, (fam_at h.1.fw hi).1, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => h.1.updW hp ps c' hi fr (by
        rw [(fam_at h.1.fw hi).2, h.2.2, rW_ge (Nat.lt_irrefl i)] at hq
        rw [rW_lt (Nat.lt_succ_self i)]; exact hq) fun j _ hji => upd_step hji) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t p.ℓ) (rW p t (i + 1)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t2P) (R0v p s₀ (p.ℓ * t) i))
    (lb_piece F.lowBits (F.ok _ (by simp)) p.γ₂ ps.hγ₂ SC (oP (wB p + i)) SC (oP 2) (by ofsd)
      (fun _ _ _ h => ⟨h.it.kd.ctx, (fam_at h.fw hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofsd), by
        rw [(fam_at h.fw hi).2, rW_lt (Nat.lt_succ_self i)] at hq; exact hq⟩) ?_
  refine (normAnd_piece F ps 2 (by simp only [nS]; omega_arith) (p.γ₂ - p.β) (by omega_arith) (fun s₀ => R0v p s₀ (p.ℓ * t) i)).mono
    (fun s₀ s _ h => h) fun s₀ s _ h => h.1.congr (fun _ _ => rfl) (fun _ _ => rfl)
      (by simp only [okR, all_range_succ, Bool.and_assoc])

/-! ## `ct₀` and the hint -/

theorem zq_sub_add (a b : Zq) : a - (a + b) = -b := by
  apply Fin.ext
  have ha := a.isLt; have hb := b.isLt
  simp only [Fin.sub_def, Fin.add_def, Fin.neg_def, q] at *
  omega_arith

theorem sub_add_neg (a b : Poly) : sub a (add a b) = neg b := by
  apply Vector.ext
  intro j hj
  simp only [sub, add, neg, Vector.getElem_zipWith, Vector.getElem_map, zq_sub_add]

theorem hintOnes_le (h : Vector Bool n) : hintOnes [h] ≤ 256 := by
  rw [hintOnes_single]
  exact Nat.le_trans (List.length_filter_le _ _) (by rw [Vector.length_toList])

theorem sum_range_succ (f : Nat → Nat) (i : Nat) :
    ((List.range (i + 1)).map f).sum = ((List.range i).map f).sum + f i := by
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero]

theorem onesS_succ {s₀ : State} {κ i : Nat} : onesS p s₀ κ (i + 1) = onesS p s₀ κ i + hintOnes [Hv p s₀ κ i] :=
  sum_range_succ _ i

theorem onesS_le {s₀ : State} {κ : Nat} : ∀ i, onesS p s₀ κ i ≤ 256 * i
  | 0 => by simp [onesS]
  | i + 1 => by rw [onesS_succ]; have := onesS_le (s₀ := s₀) (κ := κ) i; have := hintOnes_le (Hv p s₀ κ i); omega_arith

/-- `ONES ← ONES + eax`, with `eax` the number of 1s of the hint's polynomial `nh - 1`. -/
theorem CS.addOnes {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (fr : Frame (FR s₀ [sc oONES 4] 0) s.mem s'.mem) {x : State → Nat}
    (v : scw s₀ s' oONES = scw s₀ s oONES + s.gpr .eax) (he : (s.gpr .eax).toNat = x s₀)
    (hb : ones s₀ + x s₀ < 2 ^ 32) : CS p t fY fW nh okb (fun s₀ => ones s₀ + x s₀) s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (N := 80) (by decide) (fr0 hp (by decide) fr) (by ofsd),
    h.ct_keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by ofsd),
    keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (j := 0) (by simp only [nS]; omega_arith) (by ofsd) h.c,
    h.fy.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS, yB]; omega_arith) (by ofsd),
    h.fw.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS, wB]; omega_arith) (by ofsd),
    h.fh.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS]; omega_arith) (by ofsd), ?_, ?_, h.nh⟩
  · rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) fr) (sc_ok' ps (by decide) (by decide)) (by ofsd)]
    exact h.ok
  · rw [v, h.ones]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, he, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := ones s₀) (by omega_arith),
      Nat.mod_eq_of_lt hb]

/-- The hint's polynomial `nh`, made. -/
theorem CS.addHint {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (hn : nh < p.k) (fr : Frame (FR s₀ [pS (5 + nh)] 80) s.mem s'.mem)
    (hh : HintIs s'.mem (Buf.addr s₀ (pS (5 + nh))) 1 [Hv p s₀ (p.ℓ * t) nh]) :
    CS p t fY fW (nh + 1) okb ones s₀ s' :=
  have k := h.keep hp ps c' (by decide) fr (by ofsd)
  { k with fh := k.fh.snoc hh, nh := hn }

/-- The okays of the checks of `ct₀` so far. -/
abbrev okH (p : Params) (t i : Nat) (s₀ : State) : Bool :=
  okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) p.k && okT p s₀ (p.ℓ * t) i

/-- `ct₀[i]` and its norm, `w - cs₂ + ct₀` in place of `w[i]`, and `h[i]`. -/
theorem hR_piece (F : PrimsOk P) (ps : PS p) (t i : Nat) (hi : i < p.k) :
    SP p (CS p t (zY p t p.ℓ) (hW p t i) i (okH p t i) (fun s₀ => onesS p s₀ (p.ℓ * t) i))
      (CS p t (zY p t p.ℓ) (hW p t (i + 1)) (i + 1) (okH p t (i + 1)) (fun s₀ => onesS p s₀ (p.ℓ * t) (i + 1)))
      (hR P p i) := by
  have hj : t0B p + i < nS p := by simp only [nS, t0B]; omega_arith
  have hwj : wB p + i < nS p := by simp only [nS, wB]; omega_arith
  have hk := ps.hk
  have hβ := ps.hβ
  let H0 : State → State → Prop := CS p t (zY p t p.ℓ) (hW p t i) i (okH p t i) (fun s₀ => onesS p s₀ (p.ℓ * t) i)
  let H1 : State → State → Prop := CS p t (zY p t p.ℓ) (hW p t i) i
    (fun s₀ => okH p t i s₀ && decide (normRq [CT0v p s₀ (p.ℓ * t) i] < p.γ₂)) (fun s₀ => onesS p s₀ (p.ℓ * t) i)
  let H2 : State → State → Prop := CS p t (zY p t p.ℓ) (hW p t (i + 1)) i
    (fun s₀ => okH p t i s₀ && decide (normRq [CT0v p s₀ (p.ℓ * t) i] < p.γ₂)) (fun s₀ => onesS p s₀ (p.ℓ * t) i)
  refine Piece.seq (B := fun s₀ s => H0 s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t3P) (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (T0 p s₀ i)))
    (mul_piece F.mul (F.ok _ (by simp)) SC (oP 3) SC (oP 0) SC (oP (t0B p + i)) (by ofsd)
      (fun _ _ _ h => ⟨h.it.kd.ctx, h.c.1, (fam_at h.it.kd.dk.f0 hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofsd), by
        rw [h.c.2, (fam_at h.it.kd.dk.f0 hi).2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => H0 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS 3)) (CT0v p s₀ (p.ℓ * t) i))
    (inPlace_piece (t := nttInv) F.invNtt (F.ok _ (by simp)) t3P rfl (by ofsd) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofsd), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => H1 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS 3)) (CT0v p s₀ (p.ℓ * t) i))
    (normAnd_piece F ps 3 (by simp only [nS]; omega_arith) p.γ₂ (by omega_arith) (fun s₀ => CT0v p s₀ (p.ℓ * t) i)) ?_
  refine Piece.seq (B := fun s₀ s => (H1 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS 3)) (CT0v p s₀ (p.ℓ * t) i)) ∧
      PolyIs s.mem (Buf.addr s₀ t4P) (W'v p s₀ (p.ℓ * t) i))
    (copy_piece SC (oP (wB p + i)) SC (oP 4) 256 (by decide) (by decide) (by ofsd) (fun _ _ _ h => h.1.it.kd.ctx)
      fun s₀ s s' hp h c' fr hb => by
        have fr' : Frame (FR s₀ [t4P] 80) s.mem s'.mem := fr.mono (by simp)
        have hw := fam_at h.1.fw hi
        rw [hW_ge (Nat.lt_irrefl i)] at hw
        exact ⟨⟨h.1.keep hp ps c' (by decide) fr' (by ofsd), keepP hp ps (by decide) fr' (by simp only [nS]; omega_arith)
          (by ofsd) h.2⟩, polyIs_of_bytes hb hw⟩) ?_
  refine Piece.seq (B := fun s₀ s => H2 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ t4P) (W'v p s₀ (p.ℓ * t) i))
    (acc_piece (op := add) F.add (F.ok _ (by simp)) SC (oP (wB p + i)) SC (oP 3) (by ofsd)
      (fun _ _ _ h => ⟨h.1.1.it.kd.ctx, (fam_at h.1.1.fw hi).1, h.1.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.1.updW hp ps c' hi fr (by
        rw [(fam_at h.1.1.fw hi).2, h.1.2.2, hW_ge (Nat.lt_irrefl i)] at hq
        rw [hW_lt (Nat.lt_succ_self i)]; exact hq) fun j _ hji => upd_step hji,
        keepP hp ps (by decide) fr (by simp only [nS]; omega_arith) (by ofsd) h.2⟩) ?_
  refine Piece.seq (B := fun s₀ s => H2 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ t4P) (neg (CT0v p s₀ (p.ℓ * t) i)))
    (acc_piece (op := sub) F.sub (F.ok _ (by simp)) SC (oP 4) SC (oP (wB p + i)) (by ofsd)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1, (fam_at h.1.fw hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofsd), by
        rw [h.2.2, (fam_at h.1.fw hi).2, hW_lt (Nat.lt_succ_self i)] at hq
        rw [← sub_add_neg]; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t p.ℓ) (hW p t (i + 1)) (i + 1)
      (fun s₀ => okH p t i s₀ && decide (normRq [CT0v p s₀ (p.ℓ * t) i] < p.γ₂)) (fun s₀ => onesS p s₀ (p.ℓ * t) i) s₀ s ∧
      (s.gpr .eax).toNat = hintOnes [Hv p s₀ (p.ℓ * t) i])
    (hint_piece F.makeHint (F.ok _ (by simp)) p.γ₂ ps.hγ₂ SC (oP 4) SC (oP (wB p + i)) SC (oP (5 + i)) (by ofsd)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1, (fam_at h.1.fw hi).1⟩)
      fun s₀ s s' hp h c' fr hh he => by
        rw [h.2.2, (fam_at h.1.fw hi).2, hW_lt (Nat.lt_succ_self i)] at hh he
        exact ⟨h.1.addHint hp ps c' hi fr hh, he⟩) ?_
  refine blk_piece (fun _ _ _ h => h.1.it.kd.ctx) (fun s₀ s hp h => wp_addOnes hp h.1.it.kd.ctx ps
    fun s' c' fr v => ?_) rfl
  have hb : onesS p s₀ (p.ℓ * t) i + hintOnes [Hv p s₀ (p.ℓ * t) i] < 2 ^ 32 := by
    have := onesS_le (p := p) (s₀ := s₀) (κ := p.ℓ * t) i; have := hintOnes_le (Hv p s₀ (p.ℓ * t) i); omega_arith
  have k := (h.1.addOnes hp ps c' fr (x := fun s₀ => hintOnes [Hv p s₀ (p.ℓ * t) i]) v h.2 hb).congr
    (fun _ _ => rfl) (fun _ _ => rfl) (okb' := okH p t (i + 1)) (by simp only [okH, okT, all_range_succ, Bool.and_assoc])
  exact { k with ones := by rw [k.ones, onesS_succ] }

/-! ## The 1s of the hint -/

theorem sign_bit {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b) >>> 31 = if a < b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  split
  · show _ = 1
    rw [Nat.shiftRight_eq_div_pow]; omega_arith
  · show _ = 0
    rw [Nat.shiftRight_eq_div_pow]; omega_arith

/-- The okays of all of the checks. -/
abbrev okAll (p : Params) (t : Nat) (s₀ : State) : Bool :=
  okH p t p.k s₀ && decide (onesS p s₀ (p.ℓ * t) p.k ≤ p.ω)

/-- `OK ← OK ∧ ONES ≤ ω`. -/
theorem onesOk_piece (ps : PS p) (t : Nat) :
    SP p (CS p t (zY p t p.ℓ) (hW p t p.k) p.k (okH p t p.k) (fun s₀ => onesS p s₀ (p.ℓ * t) p.k))
      (CS p t (zY p t p.ℓ) (hW p t p.k) p.k (okAll p t) (fun s₀ => onesS p s₀ (p.ℓ * t) p.k)) (.block (onesOk p)) := by
  refine blk_piece (fun _ _ _ h => h.it.kd.ctx) (fun s₀ s hp h => ?_) rfl
  have hω := ps.hω
  have hk := ps.hk
  have hS := onesS_le (p := p) (s₀ := s₀) (κ := p.ℓ * t) p.k
  unfold onesOk
  refine wp_ldsc hp h.it.kd.ctx (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_subi fun s₂ o₂ v₂ _ =>
    wp_shr (by decide) (by decide) fun s₃ o₃ v₃ => ?_
  have o := (o₁.trans o₂).trans o₃
  have c₃ := h.it.kd.ctx.only o (by simp) (by simp)
  have h₃ : CS p t (zY p t p.ℓ) (hW p t p.k) p.k (okH p t p.k) (fun s₀ => onesS p s₀ (p.ℓ * t) p.k) s₀ s₃ :=
    h.keep hp ps c₃ (N := 0) (bs := []) (by decide) (by rw [o.mem]; exact Frame.refl _ _) (by simp)
  refine wp_andOK hp c₃ ps fun s' c' fr v => h₃.setOK hp ps c' fr (fun s₀ => decide (onesS p s₀ (p.ℓ * t) p.k ≤ p.ω)) v ?_
  rw [v₃, v₂, v₁, h.ones, sign_bit (by omega_arith) (by omega_arith)]
  by_cases e : onesS p s₀ (p.ℓ * t) p.k ≤ p.ω
  · rw [ifp (by omega_arith), decide_eq_true e]; rfl
  · rw [ifn (by omega_arith), decide_eq_false e]; rfl

/-! ## The end of the checks -/

/-- A piece keeps facts about the initial state. -/
theorem sp_pure {A B : State → State → Prop} {c : Prog isa} (φ : State → Prop) (h : SP p A B c) :
    SP p (fun s₀ s => A s₀ s ∧ φ s₀) (fun s₀ s => B s₀ s ∧ φ s₀) c where
  wp s₀ s hp ha := (h.wp s₀ s hp ha.1).mono fun _ hb => ⟨hb, ha.2⟩
  ct s₀ s₀' hp hp' hq := (h.ct s₀ s₀' hp hp' hq).mono (fun _ _ ⟨a, a'⟩ => ⟨a.1, a'.1⟩) fun _ _ h => h

/-- Iteration `t` continues the loop. -/
abbrev contS (p : Params) (F : PrimsOk P) (t : Nat) (s₀ : State) : Bool :=
  contV p (skOf p s₀) (muOf s₀) (rndOf s₀) F.ballF t

/-- The checks of iteration `t` pass. -/
abbrev passS (p : Params) (t : Nat) (s₀ : State) : Prop := passV p (skOf p s₀) (muOf s₀) (rndOf s₀) (p.ℓ * t)

/-- Iteration `t`, before `CNT ← CNT - 1`. -/
structure ED (p : Params) (F : PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  kd : KD p s₀ s
  run : Run p F t s₀
  cnt : scw s₀ s oCNT = if contS p F t s₀ then BitVec.ofNat 32 (814 - t) else 1
  kap : contS p F t s₀ = true → scw s₀ s oKAP = BitVec.ofNat 32 (p.ℓ * (t + 1))
  ok : scw s₀ s oOK = if (F.ballF p.τ (CTv p s₀ (p.ℓ * t)) && decide (passS p t s₀)) then 1 else 0
  out : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true → passS p t s₀ →
    Fam s₀ s.mem (yB p) p.ℓ (Zv p s₀ (p.ℓ * t)) ∧ HF s₀ s.mem p.k (Hv p s₀ (p.ℓ * t)) ∧
      bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * t)
  none : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = false → sampleInBall p.τ minBounds.ball (CTv p s₀ (p.ℓ * t)) = none

theorem KD.keep {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : KD p s₀ s) (c' : Ctx (Y p) s₀ s')
    {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, OutK p p.ℓ p.k p.k c ∧ Out p oMS (oMS + 64) c) : KD p s₀ s' :=
  ⟨c', h.dk.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hN fr fun c hc => (hb c hc).1,
    by rw [keepB hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2, h.ms]⟩

theorem okAll_eq {t : Nat} {s₀ : State} : okAll p t s₀ = decide (passS p t s₀) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact pass_iff.symm

/-- Whether the checks passed, in a run that reaches iteration `t` and whose `SampleInBall` succeeded. -/
def passB (p : Params) (F : PrimsOk P) (t : Nat) (s₀ : State) : Bool :=
  decide (Run p F t s₀ ∧ F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true ∧ passS p t s₀)

theorem passB_eq {F : PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') :
    passB p F t s₀ = passB p F t s₀' := by
  unfold passB
  by_cases h : Run p F t s₀
  · have h' := (run_iff ps hq).mp h
    obtain ⟨ect, hb⟩ := run_at ps hq h
    by_cases hs : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true
    · have hs' : F.ballF p.τ (CTv p s₀' (p.ℓ * t)) = true := by rw [← ect]; exact hs
      exact decide_eq_decide.mpr ⟨fun ⟨_, _, a⟩ => ⟨h', hs', (hb hs).1.mp a⟩, fun ⟨_, _, a⟩ => ⟨h, hs, (hb hs).1.mpr a⟩⟩
    · have hs' : ¬ F.ballF p.τ (CTv p s₀' (p.ℓ * t)) = true := by rw [← ect]; exact hs
      exact decide_eq_decide.mpr ⟨fun ⟨_, a, _⟩ => absurd a hs, fun ⟨_, a, _⟩ => absurd a hs'⟩
  · exact decide_eq_decide.mpr ⟨fun ⟨a, _⟩ => absurd a h, fun ⟨a, _⟩ => absurd ((run_iff ps hq).mpr a) h⟩

theorem CS.ofMem {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s') (c : Ctx (Y p) s₀ s)
    (hm : s.mem = s'.mem) : CS p t fY fW nh okb ones s₀ s :=
  h.keep hp ps c (N := 0) (bs := []) (by decide) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- Only an accepted candidate needs complete response and hint buffers. -/
structure CE (p : Params) (F : PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  it : IT p t s₀ s
  run : Run p F t s₀
  ball : F.ballF p.τ (CTv p s₀ (p.ℓ*t)) = true
  ok : scw s₀ s oOK = if decide (passS p t s₀) then 1 else 0
  out : passS p t s₀ → Fam s₀ s.mem (yB p) p.ℓ (Zv p s₀ (p.ℓ*t)) ∧
    HF s₀ s.mem p.k (Hv p s₀ (p.ℓ*t)) ∧
    bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ*t)

theorem CE.ofMem {F : PrimsOk P} {t : Nat} {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p)
    (h : CE p F t s₀ s') (ctx : Ctx (Y p) s₀ s) (hm : s.mem=s'.mem) : CE p F t s₀ s := by
  have fr : Frame (FR s₀ [] 0) s'.mem s.mem := by rw [hm]; exact Frame.refl _ _
  exact ⟨h.it.keep hp ps ctx (by decide) fr (by simp), h.run, h.ball,
    by rw [scw, hm]; exact h.ok, fun hp => by rw [hm]; exact h.out hp⟩

/-- `CNT ← 1` if the checks passed, and `κ ← κ + ℓ` otherwise. -/
theorem checksEnd_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (CE p F t) (ED p F t) (ifOkElse (.block (st32 oCNT 1)) (.block (nextKappa p))) := by
  refine okIte_piece (sc_ok' ps (by decide) (by decide)) (passB p F t) (fun s₀ s hp h => ⟨h.it.kd.ctx, ?_⟩)
    (fun s₀ s₀' _ _ hq => passB_eq ps hq) ?_ ?_
  · rw [h.ok]
    simp only [passB, h.run, h.ball, true_and]
  · refine blk_piece (fun _ _ _ h => h.1.choose_spec.2.1) (fun s₀ s₁ hp h => ?_) rfl
    obtain ⟨⟨s, ha, c₁, m₁⟩, hb⟩ := h
    have h₁ := ha.ofMem hp ps c₁ m₁
    simp only [passB, decide_eq_true_iff] at hb
    rw [← List.append_nil (st32 oCNT 1)]
    refine wp_st32 hp c₁ (sc_ok ps (by decide) (by decide)) 1 fun s' c' fr v => WP.block_nil_iff.mpr ?_
    have fr' := fr0 hp (N := 80) (by decide) fr
    have hc : contS p F t s₀ = false := by
      simp only [contS, contV, hb.2.2, decide_true, Bool.not_true, Bool.and_false]
    obtain ⟨hz, hh, hct⟩ := h₁.out hb.2.2
    refine ⟨h₁.it.kd.keep hp ps c' (by decide) fr' (by ofsd), hb.1, by rw [hc, v]; rfl, (fun e => by rw [hc] at e; cases e),
      ?_, fun _ _ => ⟨?_, hh.keep hp ps (by decide) fr' (by simp only [nS]; omega_arith) (by ofsd),
        by rw [keepB hp (by decide) fr' (sc_ok' ps (by ofsd) (by ofsd)) (by ofsd)]; exact hct⟩, (fun e => by rw [hb.2.1] at e; cases e)⟩
    · rw [scw, keepW' hp (by decide) fr' (sc_ok' ps (by decide) (by decide)) (by ofsd), ← scw, h₁.ok,
        hb.2.1, Bool.true_and]
    · exact hz.keep hp ps (by decide) fr' (by simp only [nS,yB]; omega_arith) (by ofsd)
  · refine blk_piece (fun _ _ _ h => h.1.choose_spec.2.1) (fun s₀ s₁ hp h => ?_) rfl
    obtain ⟨⟨s, ha, c₁, m₁⟩, hb⟩ := h
    have h₁ := ha.ofMem hp ps c₁ m₁
    have hpass : ¬ passS p t s₀ := fun hq => by
      simp only [passB, decide_eq_false_iff_not] at hb; exact hb ⟨ha.run, ha.ball, hq⟩
    have hc : contS p F t s₀ = true := by
      simp only [contS, contV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨ha.ball, hpass⟩
    unfold nextKappa
    refine wp_ldsc hp c₁ (sc_ok' ps (by decide) (by decide)) fun s₂ o₂ v₂ => wp_addi fun s₃ o₃ v₃ => ?_
    have o := o₂.trans o₃
    have c₃ := c₁.only o (by simp) (by simp)
    refine wp_stsc hp c₃ (sc_ok ps (by decide) (by decide)) fun s' c' g' m' => WP.block_nil_iff.mpr ?_
    have fr : Frame (FR s₀ [sc oKAP 4] 80) s₁.mem s'.mem := fr0 hp (by decide) (by
      rw [m', o.mem]; exact frW32 (Y := Y p))
    refine ⟨h₁.it.kd.keep hp ps c' (by decide) fr (by ofsd), ha.run, ?_, fun _ => ?_, ?_,
      (fun _ e => absurd e hpass), (fun e => by rw [ha.ball] at e; cases e)⟩
    · rw [hc, scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd), ← scw, h₁.it.cnt]; rfl
    · rw [scw, m', Mem.readW_writeW_self32, v₃, v₂, h₁.it.kap, ← BitVec.ofNat_add, Nat.mul_succ]
    · rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd), ← scw, h₁.ok,
        decide_eq_false hpass, Bool.and_false]

/-- A sequence of checks stops at its first false public prefix predicate. -/
theorem seqOk_piece {I : Nat → State → State → Prop} {f : Nat → Prog isa} (b : Nat → State → Bool) (limit : Nat)
    (hc : (Y p).ok (sc oOK 4) = true)
    (hctx : ∀ k s₀ s, TPre (Y p) s₀ → I k s₀ s → Ctx (Y p) s₀ s)
    (hok : ∀ k s₀ s, I k s₀ s → scw s₀ s oOK = if b k s₀ then 1 else 0)
    (hmem : ∀ k s₀ s s', TPre (Y p) s₀ → I k s₀ s → Ctx (Y p) s₀ s' → s'.mem=s.mem → I k s₀ s')
    (hpub : ∀ k, k≤limit → ∀ x y, TPre (Y p) x → TPre (Y p) y → SPub p x y → b k x=b k y) :
    ∀ (a n : Nat), (∀ k, a≤k → k<a+n → SP p (I k) (I (k+1)) (f k)) → a+n≤limit →
      SP p (I a) (fun s₀ s => ∃ k, a≤k ∧ k≤a+n ∧ I k s₀ s ∧ (k=a+n ∨ b k s₀=false)) (seqOk f a n)
  | a, 0, _, _ => nil_piece fun _ _ _ h => ⟨a, Nat.le_refl _, by omega, h, .inl (by omega)⟩
  | a, n+1, h, hbound => by
    rw [seqOk]
    refine Piece.seq (h a (Nat.le_refl _) (by omega)) ?_
    refine okIte_piece hc (b (a+1)) (fun s₀ s hp hi => ⟨hctx _ _ _ hp hi, hok _ _ _ hi⟩) (hpub (a+1) (by omega)) ?_ ?_
    · refine (seqOk_piece b limit hc hctx hok hmem hpub (a+1) n (fun k hk hk' => h k (by omega) (by omega)) (by omega)).mono
        (fun s₀ s hp h => ?_) (fun s₀ s hp ⟨k,ha,hb,hi,hd⟩ => ⟨k,by omega,by omega,hi,hd.imp (fun _ => by omega) id⟩)
      obtain ⟨⟨s',hi,ctx,hm⟩,_⟩ := h
      exact hmem _ _ _ _ hp hi ctx hm
    · refine nil_piece fun s₀ s hp h => ?_
      obtain ⟨⟨s',hi,ctx,hm⟩,hb⟩ := h
      exact ⟨a+1,by omega,by omega,hmem _ _ _ _ hp hi ctx hm,.inr hb⟩

/-- A complete phase continues only when every polynomial passed. -/
theorem until_piece {B : State → State → Prop} {J : Nat → State → State → Prop}
    {f : Nat → Prog isa} {cont : Prog isa} (b : Nat → State → Bool) (n : Nat)
    (hc : (Y p).ok (sc oOK 4)=true)
    (hctx : ∀ k s₀ s, TPre (Y p) s₀ → J k s₀ s → Ctx (Y p) s₀ s)
    (hok : ∀ k s₀ s, J k s₀ s → scw s₀ s oOK=if b k s₀ then 1 else 0)
    (hmem : ∀ k s₀ s s', TPre (Y p) s₀ → J k s₀ s → Ctx (Y p) s₀ s' → s'.mem=s.mem → J k s₀ s')
    (hpub : ∀ k, k≤n → ∀ x y, TPre (Y p) x → TPre (Y p) y → SPub p x y → b k x=b k y)
    (hmono : ∀ k s₀ s, k≤n → J k s₀ s → b n s₀=true → b k s₀=true)
    (hfail : ∀ k s₀ s, TPre (Y p) s₀ → k≤n → J k s₀ s → b k s₀=false → B s₀ s)
    (hstep : ∀ k, k<n → SP p (J k) (J (k+1)) (f k))
    (hcont : SP p (J n) B cont) :
    SP p (J 0) B (.seq (seqOk f 0 n) (ifOk cont)) := by
  refine Piece.seq (seqOk_piece b n hc hctx hok hmem hpub 0 n (fun k _ hk => hstep k (by omega)) (by omega)) ?_
  refine okIte_piece hc (b n) (fun s₀ s hp ⟨k,_,hk,hj,hd⟩ => ⟨hctx k _ _ hp hj,?_⟩) (hpub n (Nat.le_refl _)) ?_ ?_
  · rw [hok k _ _ hj]
    rcases hd with he|hb
    · simpa only [Nat.zero_add] using congrArg (fun k => if b k s₀ then (1 : BitVec 32) else 0) he
    · have hn : b n s₀=false := Bool.eq_false_iff.mpr (fun h => by
        have := hmono k _ _ (by omega) hj h; rw [hb] at this; cases this)
      rw [hb,hn]
  · refine hcont.mono (fun s₀ s hp h => ?_) (fun _ _ _ h => h)
    obtain ⟨⟨s',⟨k,_,hk,hj,hd⟩,ctx,hm⟩,hb⟩ := h
    have hk' : k=n := by
      rcases hd with hd|hd
      · omega
      · have := hmono k _ _ (by omega) hj hb; rw [hd] at this; cases this
    subst hk'
    exact hmem _ _ _ _ hp hj ctx hm
  · refine nil_piece fun s₀ s hp h => ?_
    obtain ⟨⟨s',⟨k,_,hk,hj,hd⟩,ctx,hm⟩,hb⟩ := h
    have hj' := hmem _ _ _ _ hp hj ctx hm
    apply hfail k _ _ hp (by omega) hj'
    rcases hd with hd|hd
    · simpa only [Nat.zero_add,hd] using hb
    · exact hd

/-- Prefix outcomes made total by requiring a reached iteration and a sampled challenge. -/
def prefixB (p : Params) (F : PrimsOk P) (t : Nat) (r0 : Bool) (k : Nat) (s₀ : State) : Bool :=
  decide (Run p F t s₀ ∧ F.ballF p.τ (CTv p s₀ (p.ℓ*t))=true) &&
    (if r0 then okZ p s₀ (p.ℓ*t) p.ℓ && okR p s₀ (p.ℓ*t) k else okZ p s₀ (p.ℓ*t) k)

theorem prefixB_eq {F : PrimsOk P} {t k : Nat} {r0 : Bool} (ps : PS p)
    (hk : k ≤ if r0 then p.k else p.ℓ) {x y : State} (hq : SPub p x y) :
    prefixB p F t r0 k x = prefixB p F t r0 k y := by
  unfold prefixB
  by_cases hr : Run p F t x
  · have hr' := (run_iff ps hq).mp hr
    have ect := (run_at ps hq hr).1
    by_cases hb : F.ballF p.τ (CTv p x (p.ℓ*t))=true
    · have hb' : F.ballF p.τ (CTv p y (p.ℓ*t))=true := by rw [←ect]; exact hb
      simp only [hr,hr',hb,hb',and_self,decide_true,Bool.true_and]
      have ha := run_agree ps hq hr (F.ballMax _ _ hb) (F.ballMax _ _ hb')
      apply Bool.eq_iff_iff.mpr
      cases r0 <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact (all_range_iff.trans ((ha.1 k hk).trans all_range_iff.symm))
      · simp only [Bool.and_eq_true,okZ,okR,all_range_iff]
        exact ha.2.1 k hk
    · have hb' : ¬ F.ballF p.τ (CTv p y (p.ℓ*t))=true := by rw [←ect]; exact hb
      simp [hr,hr',hb,hb']
  · have hr' : ¬ Run p F t y := fun h => hr ((run_iff ps hq).mpr h)
    simp only [hr,hr',false_and,decide_false,Bool.false_and]

abbrev Reached (p : Params) (F : PrimsOk P) (t : Nat) (s₀ : State) : Prop :=
  Run p F t s₀ ∧ F.ballF p.τ (CTv p s₀ (p.ℓ*t))=true
abbrev ZCS (p : Params) (F : PrimsOk P) (t r : Nat) (s₀ s : State) : Prop :=
  CS p t (zY p t r) (fun s₀=>Wv p s₀ (p.ℓ*t)) 0 (fun s₀=>okZ p s₀ (p.ℓ*t) r) (fun _=>0) s₀ s ∧ Reached p F t s₀
abbrev RCS (p : Params) (F : PrimsOk P) (t i : Nat) (s₀ s : State) : Prop :=
  CS p t (zY p t p.ℓ) (rW p t i) 0 (fun s₀=>okZ p s₀ (p.ℓ*t) p.ℓ && okR p s₀ (p.ℓ*t) i) (fun _=>0) s₀ s ∧ Reached p F t s₀

/-- Full passing prefixes imply each earlier prefix passes. -/
theorem prefixB_mono {F : PrimsOk P} {t k n : Nat} {r0 : Bool} {s₀ : State} (hk : k≤n) :
    prefixB p F t r0 n s₀=true → prefixB p F t r0 k s₀=true := by
  simp only [prefixB,Bool.and_eq_true]
  rintro ⟨hr,hb⟩
  refine ⟨hr,?_⟩
  cases r0 <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hb ⊢
  · exact all_range_iff.mpr (fun j hj => all_range_iff.mp hb j (by omega))
  · obtain ⟨hz,hb⟩ := Bool.and_eq_true_iff.mp hb
    exact Bool.and_eq_true_iff.mpr ⟨hz,all_range_iff.mpr fun j hj=>all_range_iff.mp hb j (by omega)⟩

theorem rejectedCE {F : PrimsOk P} {t nh : Nat} {fy fw : State→Nat→Poly} {okb : State→Bool} {ones : State→Nat}
    {s₀ s : State} (h : CS p t fy fw nh okb ones s₀ s) (hr : Reached p F t s₀)
    (hno : ¬ passS p t s₀) (hb : okb s₀=false) : CE p F t s₀ s :=
  ⟨h.it,hr.1,hr.2,by rw [h.ok,hb,decide_eq_false hno],fun hp=>absurd hp hno⟩

theorem hints_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (RCS p F t p.k) (CE p F t) (.seq (seqR (hR P p) 0 p.k) (.block (onesOk p))) := by
  have hk := ps.hk
  have hl := ps.hl
  let φ := Reached p F t
  refine Piece.seq (B := fun s₀ s=>CS p t (zY p t p.ℓ) (hW p t p.k) p.k (okH p t p.k)
    (fun s₀=>onesS p s₀ (p.ℓ*t) p.k) s₀ s ∧ φ s₀) (sp_pure φ ?_) ?_
  · have h := seqR_piece (p:=p) (I:=fun i=>CS p t (zY p t p.ℓ) (hW p t i) i (okH p t i)
      (fun s₀=>onesS p s₀ (p.ℓ*t) i)) 0 p.k fun i _ hi=>hR_piece F ps t i (by omega)
    simp only [Nat.zero_add] at h
    refine h.mono (fun s₀ s _ h=>?_) (fun _ _ _ h=>h)
    have h' := h.congr (fY':=zY p t p.ℓ) (fW':=hW p t 0) (okb':=okH p t 0) (fun _ _=>rfl)
      (fun j hj=>by rw [rW_lt hj,hW_ge (Nat.not_lt_zero j)]) (by simp [okH,okT])
    exact {h' with fh:=fun j hj=>absurd hj (Nat.not_lt_zero _),ones:=by rw [h'.ones];rfl,nh:=Nat.zero_le _}
  · refine (sp_pure φ (onesOk_piece ps t)).mono (fun _ _ _ h=>h) (fun s₀ s _ h=>?_)
    exact ⟨h.1.it,h.2.1,h.2.2,by rw [h.1.ok,okAll_eq],fun _=>
      ⟨h.1.fy.congr (fun j hj=>zY_lt hj),h.1.fh,h.1.ct⟩⟩

theorem r0checks_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (RCS p F t 0) (CE p F t) (checksR0 P p) := by
  have hk := ps.hk
  have hl := ps.hl
  unfold checksR0
  apply until_piece (J:=RCS p F t) (prefixB p F t true) p.k (sc_ok' ps (by decide) (by decide))
    (fun _ _ _ _ h=>h.1.it.kd.ctx)
    (fun k s₀ s h=>by rw [h.1.ok]; simp only [prefixB,h.2.1,h.2.2,true_and,decide_true,Bool.true_and,ite_true])
    (fun _ _ _ _ hp h ctx hm=>⟨h.1.ofMem hp ps ctx hm,h.2⟩)
    (fun k hk _ _ _ _ hq=>prefixB_eq ps (by simpa using hk) hq)
    (fun k _ _ hk _ hb=>prefixB_mono hk hb) ?_ ?_ (hints_piece F ps t)
  · intro k s₀ s hp hk h hb
    have raw : (okZ p s₀ (p.ℓ*t) p.ℓ && okR p s₀ (p.ℓ*t) k)=false := by
      simpa only [prefixB,h.2.1,h.2.2,true_and,decide_true,Bool.true_and,ite_true] using hb
    refine rejectedCE h.1 h.2 (fun hpass=>?_) raw
    have hz : okZ p s₀ (p.ℓ*t) p.ℓ=true := all_range_iff.mpr hpass.1
    have hr : okR p s₀ (p.ℓ*t) k=true := all_range_iff.mpr (fun j hj=>hpass.2.1 j (by omega))
    rw [hz,hr] at raw; cases raw
  · intro i hi
    exact sp_pure (Reached p F t) (r0R_piece F ps t i hi)

theorem zchecks_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (ZCS p F t 0) (CE p F t) (.seq (seqOk (zR P p) 0 p.ℓ) (ifOk (checksR0 P p))) := by
  have hk := ps.hk
  have hl := ps.hl
  apply until_piece (J:=ZCS p F t) (prefixB p F t false) p.ℓ (sc_ok' ps (by decide) (by decide))
    (fun _ _ _ _ h=>h.1.it.kd.ctx)
    (fun k s₀ s h=>by rw [h.1.ok]; simp only [prefixB,h.2.1,h.2.2,true_and,decide_true,Bool.true_and,Bool.false_eq_true,ite_false])
    (fun _ _ _ _ hp h ctx hm=>⟨h.1.ofMem hp ps ctx hm,h.2⟩)
    (fun k hk _ _ _ _ hq=>prefixB_eq ps (by simpa using hk) hq)
    (fun k _ _ hk _ hb=>prefixB_mono hk hb) ?_ ?_ ?_
  · intro k s₀ s hp hk h hb
    have raw : okZ p s₀ (p.ℓ*t) k=false := by
      simpa only [prefixB,h.2.1,h.2.2,true_and,decide_true,Bool.true_and,Bool.false_eq_true,ite_false] using hb
    refine rejectedCE h.1 h.2 (fun hpass=>?_) raw
    have hz : okZ p s₀ (p.ℓ*t) k=true := all_range_iff.mpr (fun j hj=>hpass.1 j (by omega))
    rw [hz] at raw; cases raw
  · intro i hi
    exact sp_pure (Reached p F t) (zR_piece F ps t i hi)
  · refine (r0checks_piece F ps t).mono (fun s₀ s _ h=>⟨?_,h.2⟩) (fun _ _ _ h=>h)
    exact h.1.congr (fun _ _=>rfl) (fun j _=>(rW_ge (Nat.not_lt_zero j)).symm) (by simp [okR])

/-! ## The checks -/

/-- The checks of iteration `t`, once `SampleInBall` succeeded. -/
theorem checks_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (fun s₀ s => KP p F t s₀ s ∧ PolyIs s.mem (Buf.addr s₀ cP) (toRq (Cv p s₀ (p.ℓ * t)))) (ED p F t)
      (checks P p) := by
  have hk := ps.hk
  have hl := ps.hl
  let φ : State → Prop := fun s₀ => Run p F t s₀ ∧ F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true
  unfold checks
  refine Piece.seq (B := fun s₀ s => (CC p t s₀ s ∧ PolyIs s.mem (Buf.addr s₀ cP) (chF (Cv p s₀ (p.ℓ * t)))) ∧ φ s₀)
    ((inPlace_piece (t := ntt) F.ntt (F.ok _ (by simp)) cP rfl (by ofsd) (fun _ _ _ h => ⟨h.1.cc.cw.cm.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.cc.keep hp ps c' (by decide) fr (by ofsd), by rw [h.2.2] at hq; exact hq⟩).mono
        (fun _ _ _ h => h) (fun _ _ _ h => h) |> sp_pure φ |>.mono (fun _ _ _ h => ⟨h, h.1.run, h.1.ball⟩)
        fun _ _ _ h => h) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t 0) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) 0) (fun _ => 0) s₀ s ∧ φ s₀) (sp_pure φ (checksInit_piece ps t)) ?_
  exact Piece.seq (zchecks_piece F ps t) (checksEnd_piece F ps t)

end VG.Proof.MlDsa.X86.Sign
