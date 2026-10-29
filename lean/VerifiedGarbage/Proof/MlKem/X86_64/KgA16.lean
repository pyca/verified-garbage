module

public import VerifiedGarbage.Proof.MlKem.X86_64.KgA
public import VerifiedGarbage.Impl.MlKem.X86_64.Frag16

/-!
# ML-KEM on x86-64: sampling a matrix of polynomials with 16-bit coefficients

As `KgA.lean`'s `MatB`, `ents_ok` and `ents_tr`, for the matrix `Â` (`k × k`)
whose entry `e = k i + j` is the 512 bytes at `sc (oa + 512 e)` (`ents16`):
after the first `e` entries, `r15` is 1 exactly when all of them succeeded
within 280 iterations (`allOk`), and each one that did holds its polynomial
(`MatB16`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay rbs wbs s) {ws : List (Ptr × Nat)} {p : Ptr}
include L

/-- A polynomial of 16-bit coefficients that a piece does not write is kept. -/
theorem Lay.keepPoly16 {f : Poly} (hP : PPostB s s' ws) (hc : keepB (rbs ++ wbs) ws p 512 = true)
    (h : PolyIsW 16 s.mem (pa s p) f) : PolyIsW 16 s'.mem (pa s' p) f := by
  rw [hP.pa (keepB_cs hc)]
  exact polyIsW_frame true hP.frame (L.fdisj hc) h

end

/-- After the first `e` entries of the `k × k` matrix at `sc oa`: `r15`, and
the entries sampled, for the seed `ρ`. -/
structure MatB16 (k oa : Nat) (ρ : List Byte) (e : Nat) (s : State) : Prop where
  r15 : s.gpr .r15 = if allOk k ρ e then 1 else 0
  mat : ∀ e' < e, ∀ f, sampleNTT minIterations (matSeed ρ (e' / k) (e' % k)) = some f →
    PolyIsW 16 s.mem (pa s (sc (oa + 512 * e'))) f

/-- The step of one entry. -/
theorem MatB16.single {k oa : Nat} {ρ : List Byte} {e : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (h : MatB16 k oa ρ e s) (hsb : bytesAt s.mem (pa s (sc oSB)) 32 = ρ) (Lx : Lay rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (kA : ∀ e' < e, keepB (rbs ++ wbs) ws (sc (oa + 512 * e')) 512 = true)
    (h15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) (e / k) (e % k))).isSome
          then 1 else 0)))
    (hres : ∀ f, sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) (e / k) (e % k)) = some f →
        PolyIsW 16 s'.mem (pa s (sc (oa + 512 * e))) f) : MatB16 k oa ρ (e + 1) s' := by
  refine ⟨?_, fun e' he' f hf => ?_⟩
  · rw [h15, hsb, and_acc h.r15]
    exact ite_congr (propext allOk_succ.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · exact Lx.keepPoly16 hP (kA e' he') (h.mat e' he' f hf)
    · rw [hP.pa rbx_bases]
      exact hres f (by rw [hsb]; exact hf)

/-- The step of four entries. -/
theorem MatB16.four {k oa : Nat} {ρ : List Byte} {e : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (h : MatB16 k oa ρ e s) (hsb : bytesAt s.mem (pa s (sc oSB)) 32 = ρ) (Lx : Lay rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (kA : ∀ e' < e, keepB (rbs ++ wbs) ws (sc (oa + 512 * e')) 512 = true)
    (h15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (List.range 4).all (fun t => (sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e + t) / k) ((e + t) % k))).isSome) then 1 else 0)))
    (hres : ∀ t < 4, ∀ f, sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e + t) / k) ((e + t) % k)) = some f →
        PolyIsW 16 s'.mem (pa s (sc (oa + 512 * e + 512 * t))) f) : MatB16 k oa ρ (e + 4) s' := by
  refine ⟨?_, fun e' he' f hf => ?_⟩
  · rw [h15, hsb, and_acc h.r15]
    exact ite_congr (propext allOk_add4.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e ≤ e') with he'' | he''
    · exact Lx.keepPoly16 hP (kA e' he'') (h.mat e' he'' f hf)
    · have := hres (e' - e) (by omega) f (by rw [hsb, Nat.add_sub_cancel' he'']; exact hf)
      rw [hP.pa rbx_bases]
      rwa [show oa + 512 * e + 512 * (e' - e) = oa + 512 * e' by omega] at this

theorem MatB16.zero (k oa : Nat) (ρ : List Byte) {s : State} (h15 : s.gpr .r15 = 1) : MatB16 k oa ρ 0 s :=
  ⟨by rw [h15, ifp (allOk_zero _ _)], fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- Every entry of `Â`, once all were sampled. -/
theorem MatB16.all {k oa : Nat} {ρ : List Byte} {s : State} (h : MatB16 k oa ρ (k * k) s)
    (ho : allOk k ρ (k * k)) : ∀ i < k, ∀ j < k, PolyIsW 16 s.mem (pa s (sc (oa + 512 * (k * i + j)))) (aHat ρ i j) :=
  fun i hi j hj => by
    have := h.mat (k * i + j) (ij_lt hi hj) (aHat ρ i j)
    rw [(divmod_ij hj).1, (divmod_ij hj).2] at this
    exact this (aHat_eq ho hi hj)

/-- The entries `e, …, e + n - 1`, from any invariant `I e` whose steps are
those of one entry and of four (`ents16`). -/
theorem ents16_ok (p : String × Prog isa) (k oa : Nat) (scr : Ptr) {I : Nat → State → Prop}
    (h1 : ∀ e < k * k, 4 * (k * k / 4) ≤ e → ∀ s, I e s →
      WP isa (sampleIJ16 (sc (oa + 512 * e)) (e / k) (e % k) scr) s (I (e + 1)))
    (h4 : ∀ q < k * k / 4, ∀ s, I (4 * q) s →
      WP isa (quad16 p k (4 * q) (sc (oa + 512 * (4 * q))) scr) s (I (4 * q + 4))) :
    ∀ n e, e + n = k * k → (e % 4 = 0 ∨ 4 * (k * k / 4) ≤ e) → ∀ s, I e s →
      WP isa (ents16 p k oa scr e n) s (I (e + n))
  | 0, e, _, _, s, hs => by simp only [ents16]; exact WP.block_nil hs
  | 1, e, he, hq, s, hs => by
    simp only [ents16]; exact h1 e (by omega) (by omega) s hs
  | 2, e, he, hq, s, hs => by
    simp only [ents16]
    exact WP.seq (WP.mono (h1 e (by omega) (by omega) s hs) fun s₁ h₁ =>
      ents16_ok p k oa scr h1 h4 1 (e + 1) (by omega) (by omega) s₁ h₁)
  | 3, e, he, hq, s, hs => by
    simp only [ents16]
    refine WP.seq (WP.mono (h1 e (by omega) (by omega) s hs) fun s₁ h₁ => ?_)
    have := ents16_ok p k oa scr h1 h4 2 (e + 1) (by omega) (by omega) s₁ h₁
    rwa [show e + 1 + 2 = e + 3 by omega] at this
  | 4, e, he, hq, s, hs => by
    simp only [ents16]
    have := h4 (e / 4) (by omega) s (by rwa [show 4 * (e / 4) = e by omega])
    rwa [show 4 * (e / 4) = e by omega] at this
  | n + 5, e, he, hq, s, hs => by
    simp only [ents16]
    have := h4 (e / 4) (by omega) s (by rwa [show 4 * (e / 4) = e by omega])
    rw [show 4 * (e / 4) = e by omega] at this
    refine WP.seq (WP.mono this fun s₁ h₁ => ?_)
    have := ents16_ok p k oa scr h1 h4 (n + 1) (e + 4) (by omega) (by omega) s₁ h₁
    rwa [show e + 4 + (n + 1) = e + (n + 5) by omega] at this

theorem samples16_ok' (p : String × Prog isa) (k oa : Nat) (scr : Ptr) {I : Nat → State → Prop}
    (h1 : ∀ e < k * k, 4 * (k * k / 4) ≤ e → ∀ s, I e s →
      WP isa (sampleIJ16 (sc (oa + 512 * e)) (e / k) (e % k) scr) s (I (e + 1)))
    (h4 : ∀ q < k * k / 4, ∀ s, I (4 * q) s →
      WP isa (quad16 p k (4 * q) (sc (oa + 512 * (4 * q))) scr) s (I (4 * q + 4)))
    {s : State} (h : I 0 s) : WP isa (samples16 p k oa scr) s (I (k * k)) := by
  have := ents16_ok p k oa scr h1 h4 (k * k) 0 (by omega) (by omega) s h
  rwa [Nat.zero_add] at this

/-- `ents16_ok`, for constant time. -/
theorem ents16_tr (p : String × Prog isa) (k oa : Nat) (scr : Ptr) {R : Nat → State → State → Prop}
    (h1 : ∀ e < k * k, 4 * (k * k / 4) ≤ e →
      RelCT isa (R e) (sampleIJ16 (sc (oa + 512 * e)) (e / k) (e % k) scr) (R (e + 1)))
    (h4 : ∀ q < k * k / 4,
      RelCT isa (R (4 * q)) (quad16 p k (4 * q) (sc (oa + 512 * (4 * q))) scr) (R (4 * q + 4))) :
    ∀ n e, e + n = k * k → (e % 4 = 0 ∨ 4 * (k * k / 4) ≤ e) → RelCT isa (R e) (ents16 p k oa scr e n) (R (e + n))
  | 0, e, _, _ => by simp only [ents16]; exact nil_tr
  | 1, e, he, hq => by simp only [ents16]; exact h1 e (by omega) (by omega)
  | 2, e, he, hq => by
    simp only [ents16]
    exact RelCT.seq (h1 e (by omega) (by omega)) (ents16_tr p k oa scr h1 h4 1 (e + 1) (by omega) (by omega))
  | 3, e, he, hq => by
    simp only [ents16]
    have := ents16_tr p k oa scr h1 h4 2 (e + 1) (by omega) (by omega)
    rw [show e + 1 + 2 = e + 3 by omega] at this
    exact RelCT.seq (h1 e (by omega) (by omega)) this
  | 4, e, he, hq => by
    simp only [ents16]
    have := h4 (e / 4) (by omega)
    rwa [show 4 * (e / 4) = e by omega] at this
  | n + 5, e, he, hq => by
    simp only [ents16]
    have := h4 (e / 4) (by omega)
    rw [show 4 * (e / 4) = e by omega] at this
    have h' := ents16_tr p k oa scr h1 h4 (n + 1) (e + 4) (by omega) (by omega)
    rw [show e + 4 + (n + 1) = e + (n + 5) by omega] at h'
    exact RelCT.seq this h'

theorem samples16_tr' (p : String × Prog isa) (k oa : Nat) (scr : Ptr) {R : Nat → State → State → Prop}
    (h1 : ∀ e < k * k, 4 * (k * k / 4) ≤ e →
      RelCT isa (R e) (sampleIJ16 (sc (oa + 512 * e)) (e / k) (e % k) scr) (R (e + 1)))
    (h4 : ∀ q < k * k / 4,
      RelCT isa (R (4 * q)) (quad16 p k (4 * q) (sc (oa + 512 * (4 * q))) scr) (R (4 * q + 4))) :
    RelCT isa (R 0) (samples16 p k oa scr) (R (k * k)) := by
  have := ents16_tr p k oa scr h1 h4 (k * k) 0 (by omega) (by omega)
  rwa [Nat.zero_add] at this

end VG.Proof.MlKem.X86_64
