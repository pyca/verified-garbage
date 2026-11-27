module

public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.AArch64.KemOps
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# ML-KEM on AArch64: the matrix `Â` of `encaps` and `decaps`

`Â[i, j]` for the `k²` entries `(i, j)` (entry `e = k i + j`), from the seed `ρ` at
`SB`, each with `sample_ntt`'s stronger contract: it is reduced, and the
result is 1 exactly when `SampleNTT` with 280 iterations succeeds; `x24` is
the AND of the results. The matrix writes only the last two bytes of the seed,
`Â`, `sample_ntt`'s working space and the stack below the stack pointer
(`bW`).

-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay} {L : Layout}

/-- Whether the first `n` `SampleNTT`s from `ρ` succeed. -/
def okR (P : KemLay) (ρ : List Byte) (n : Nat) : Prop :=
  ∀ e < n, (sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k))).isSome

instance (ρ : List Byte) (n : Nat) : Decidable (okR P ρ n) := by unfold okR; infer_instance

theorem okR_succ {ρ : List Byte} {k : Nat} :
    okR P ρ (k + 1) ↔ okR P ρ k ∧ (sampleNTT 280 (matSeed ρ (k / P.k) (k % P.k))).isSome := by
  constructor
  · intro h; exact ⟨fun e he => h e (by omega_using [he]), h k (by omega_using [])⟩
  · rintro ⟨h, hk⟩ e he
    rcases (by omega_using [he] : e < k ∨ e = k) with he | rfl
    · exact h e he
    · exact hk

/-- What the matrix writes. -/
abbrev bW (P : KemLay) (L : Layout) (s₀ : State) : List Region :=
  [R (kA s₀) L.sc (SB + 32) 2, R (kA s₀) L.sc AH (1024 * (P.k * P.k)), R (kA s₀) L.sc SS 2048, below s₀.sp 16]

/-- Entry `e` of `Â`. -/
abbrev aP (L : Layout) (s₀ : State) (e : Nat) : Addr := sA L s₀ (AH + 1024 * e)

/-- After `n` entries of `Â`, from memory `mA`, with `Â` stored with 16-bit
coefficients (`w16`) or 32-bit ones. -/
structure BInvW (w16 : Bool) (P : KemLay) (L : Layout) (s₀ : State) (mA : Mem) (ρ : List Byte) (n : Nat)
    (s : State) : Prop where
  kb : KB P L s₀ s
  fr : Frame (bW P L s₀) mA s.mem
  rho : bytesAt s.mem (sA L s₀ SB) 32 = ρ
  acc : s.gpr .x24 = if okR P ρ n then 1 else 0
  red : ∀ e < n, ReducedW (cw w16) s.mem (aP L s₀ e)
  res : ∀ e < n, sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k)) = none ∨
    sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k)) = some (polyAtW (cw w16) s.mem (aP L s₀ e))

theorem BInvW.zero {w16 : Bool} {s₀ s : State} {ρ : List Byte} (hk : KB P L s₀ s) (h24 : s.gpr .x24 = 1)
    (hρ : bytesAt s.mem (sA L s₀ SB) 32 = ρ) : BInvW w16 P L s₀ s.mem ρ 0 s :=
  ⟨hk, Frame.refl _ _, hρ, by rw [h24, ite_eq_left (show okR P ρ 0 from fun e he => absurd he (Nat.not_lt_zero e))],
    fun e he => absurd he (Nat.not_lt_zero e), fun e he => absurd he (Nat.not_lt_zero e)⟩

/-! ## After the matrix -/

/-- `SampleNTT` succeeds on every entry exactly when `x24` is 1; then its
entries are `Â`'s. -/
theorem BInvW.outcome {w16 : Bool} {s₀ : State} {mA : Mem} {ρ : List Byte} {s : State}
    (h : BInvW w16 P L s₀ mA ρ (P.k * P.k) s) :
    (s.gpr .x24 = 1 ∧ ∀ i < P.k, ∀ j < P.k,
      sampleNTT 280 (matSeed ρ i j) = some (polyAtW (cw w16) s.mem (sA L s₀ (aOff P i j)))) ∨
    (s.gpr .x24 = 0 ∧ ∃ i < P.k, ∃ j < P.k, sampleNTT 280 (matSeed ρ i j) = none) := by
  by_cases hA : okR P ρ (P.k * P.k)
  · refine .inl ⟨by rw [h.acc, ite_eq_left hA], fun i hi j hj => ?_⟩
    have he : P.k * i + j < P.k * P.k := ij_lt hi hj
    have hke := ij_div (i := i) hj
    have r := h.res (P.k * i + j) he
    have ok := hA (P.k * i + j) he
    rw [hke.1, hke.2] at r ok
    rcases r with r | r
    · rw [r] at ok; simp at ok
    · exact r
  · refine .inr ⟨by rw [h.acc, ite_eq_right hA], ?_⟩
    obtain ⟨e, he, hn⟩ : ∃ e, e < P.k * P.k ∧ ¬ (sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k))).isSome :=
      Classical.byContradiction fun hc => hA fun e he => Classical.byContradiction fun hn => hc ⟨e, he, hn⟩
    exact ⟨e / P.k, div_lt he, e % P.k, mod_lt he, Option.not_isSome_iff_eq_none.mp hn⟩

theorem BInvW.reduced {w16 : Bool} {s₀ : State} {mA : Mem} {ρ : List Byte} {s : State}
    (h : BInvW w16 P L s₀ mA ρ (P.k * P.k) s) {i j : Nat} (hi : i < P.k) (hj : j < P.k) :
    ReducedW (cw w16) s.mem (sA L s₀ (aOff P i j)) :=
  h.red (P.k * i + j) (ij_lt hi hj)

end VG.Proof.MlKem.AArch64.Kem
