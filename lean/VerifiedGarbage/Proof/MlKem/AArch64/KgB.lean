module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgA
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM on AArch64: `keygen`, the matrix `Â`

`Â[i, j]` for the `k²` entries `(i, j)` (entry `e = k i + j`), each with `sample_ntt`'s
stronger contract: it is reduced, and the result is 1 exactly when `SampleNTT`
with 280 iterations succeeds; `x24` is the AND of the results.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- `ρ`. -/
abbrev rhoK (P : KemLay) (s₀ : State) : List Byte := KPke.kgRho P.params (dB s₀)

/-- Whether the first `n` `SampleNTT`s succeed. -/
def allOk (P : KemLay) (s₀ : State) (n : Nat) : Prop :=
  ∀ e < n, (sampleNTT 280 (matSeed (rhoK P s₀) (e / P.k) (e % P.k))).isSome

instance (s₀ : State) (n : Nat) : Decidable (allOk P s₀ n) := by unfold allOk; infer_instance

/-- Entry `e` of `Â`, at `s`, stored with 16-bit coefficients (`w16`) or 32-bit ones. -/
abbrev aAtW (w16 : Bool) (s₀ : State) (m : Mem) (e : Nat) : Poly :=
  polyAtW (cw w16) m (kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e))

/-- After `n` entries of `Â`, stored with 16-bit coefficients (`w16`) or 32-bit ones. -/
structure BInvW (w16 : Bool) (P : KemLay) (s₀ : State) (n : Nat) (s : State) : Prop where
  kb : KB P s₀ s
  rho : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SB) 32 = rhoK P s₀
  sig : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SG) 32 = KPke.kgSigma P.params (dB s₀)
  acc : s.gpr .x24 = if allOk P s₀ n then 1 else 0
  red : ∀ e < n, ReducedW (cw w16) s.mem (kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e))
  res : ∀ e < n, sampleNTT 280 (matSeed (rhoK P s₀) (e / P.k) (e % P.k)) = none ∨
    sampleNTT 280 (matSeed (rhoK P s₀) (e / P.k) (e % P.k)) = some (aAtW w16 s₀ s.mem e)

theorem allOk_succ {s₀ : State} {k : Nat} :
    allOk P s₀ (k + 1) ↔ allOk P s₀ k ∧ (sampleNTT 280 (matSeed (rhoK P s₀) (k / P.k) (k % P.k))).isSome := by
  constructor
  · intro h; exact ⟨fun e he => h e (by omega_using [he]), h k (by omega_using [])⟩
  · rintro ⟨h, hk⟩ e he
    rcases (by omega_using [he] : e < k ∨ e = k) with he | rfl
    · exact h e he
    · exact hk

end VG.Proof.MlKem.AArch64.KeyGen
