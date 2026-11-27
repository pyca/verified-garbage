module

import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.MlKem.Scrubbed
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.KgA
import VerifiedGarbage.Proof.Framework.WriteBytes
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.MlKem.AArch64.KgA
meta import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `MlKem.AArch64.KeyGen`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.KgEnd`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.KgC`, which only this module used -/

section

/-!
# ML-KEM on AArch64: `keygen`, the polynomial buffers of `ŝ`, `ê` and `t̂`

Where a polynomial buffer of the computation of `ŝ`, `ê` and `t̂` may be in
`scratch` (`PolyOff`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- A polynomial buffer in `scratch` for phase C: past `Â`'s start, below
the saved registers. -/
def PolyOff (P : KemLay) (off : Nat) : Prop := AH ≤ off ∧ off + 1024 ≤ SV P

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! ### `MlKem.AArch64.KgB`, which this module and modules that import it used -/

section

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

end

end

/-! ### `MlKem.AArch64.KgT`, which only this module used -/

section

/-! ### `MlKem.AArch64.KgC2`, which only this module used -/

section

/-!
# ML-KEM on AArch64: `keygen`, `ŝ` and `t̂`

`Â[e]`'s buffer (`AR`), and a buffer apart from `ρ`, `σ` and `Â`
(`one_far`), for `ŝ[j]`, `ê[i]` and `t̂[i]` and their encodings into `ek` and
`dk`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- `Â[e]`'s buffer. -/
abbrev AR (s₀ : State) (e : Nat) : Addr := kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e)

/-- A single buffer of `ek`, `dk` or past `Â` in `scratch` is apart from `ρ`, `σ` and `Â`. -/
theorem one_far {s₀ : State} (hp : Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL P b)
    (h : b ≠ 3 ∨ SH P ≤ o) :
    ∀ r ∈ [R (kA s₀) b o l], (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
      (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨hp.args.rdisj (by decide) hb (by kl) f (by kl),
    hp.args.rdisj (by decide) hb (by kl) f (by kl),
    hp.args.rdisj (by decide) hb (by kl) f (by kl)⟩

end VG.Proof.MlKem.AArch64.KeyGen

end

end


/-!
# ML-KEM on AArch64: `keygen`, `t̂`

The buffers `ê[i]`, `t̂[i]` and its encodings are written to are apart
(`Apart`) from the facts established before (`TLW`, `Kem16/KgCommon.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- A region apart from what `TLW … i` describes. -/
def Apart (P : KemLay) (s₀ : State) (i : Nat) (r : Region) : Prop :=
  (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
    (R (kA s₀) 3 AH (1024 * (P.k * P.k) + 1024 * P.k)).Disjoint r ∧
    (R (kA s₀) 1 0 (384 * i)).Disjoint r ∧ (R (kA s₀) 2 0 (384 * P.k + 384 * i)).Disjoint r

/-- A buffer of `scratch` past `ŝ`, or the NTT's working space. -/
theorem apart_scr {s₀ : State} (hp : Pre P s₀) {i o l : Nat} (hi : i < P.k) (f : o + l ≤ kL P 3)
    (h : EP P ≤ o ∨ (o = 3104 ∧ l = 1024)) : Apart P s₀ i (R (kA s₀) 3 o l) := by
  have hi' : 0 + 384 * i ≤ kL P 1 := by kl
  have hi'' : 0 + (384 * P.k + 384 * i) ≤ kL P 2 := by kl
  refine ⟨hp.args.rdisj (by decide) (by decide) (by kl) f (by kl),
    hp.args.rdisj (by decide) (by decide) (by kl) f (by kl),
    hp.args.rdisj (by decide) (by decide) (by kl) f (by kl),
    hp.args.rdisj (by decide) (by decide) hi' f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) hi'' f (.inl (by decide))⟩

theorem apart_ek {s₀ : State} (hp : Pre P s₀) {i : Nat} (hi : i < P.k) :
    Apart P s₀ i (R (kA s₀) 1 (384 * i) 384) := by
  have f : 384 * i + 384 ≤ kL P 1 := by kl
  refine ⟨hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inr (.inl (by omega_using []))),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide))⟩

theorem apart_dk {s₀ : State} (hp : Pre P s₀) {i : Nat} (hi : i < P.k) :
    Apart P s₀ i (R (kA s₀) 2 (384 * P.k + 384 * i) 384) := by
  have f : 384 * P.k + 384 * i + 384 ≤ kL P 2 := by kl
  refine ⟨hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inr (.inl (by omega_using [])))⟩

theorem po_s (hP : P.Wf) {j : Nat} (hj : j < P.k) : PolyOff P (sOff P j) := ⟨by lom, by lom⟩
theorem po_TP (hP : P.Wf) : PolyOff P (TP P) := ⟨by lom, by lom⟩

theorem apart_TP {s₀ : State} (hp : Pre P s₀) {i : Nat} (hi : i < P.k) :
    ∀ r ∈ [R (kA s₀) 3 (TP P) 1024], Apart P s₀ i r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact apart_scr hp hi (by kl) (.inl (by kl))

end VG.Proof.MlKem.AArch64.KeyGen

end

end


/-!
# ML-KEM on AArch64: `keygen`, the end

The bytes of `ek` and `dk` as the standard puts them together (`ek_at`,
`dk_at`), our caller's registers back (`restore_ok`), and the regions apart
from what holds from the copies of `ρ` on (`Far`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-! ## The bytes of `ek` and `dk` -/

/-- `n` encoded polynomials at `p`. -/
theorem cat_at {m : Mem} {p : Addr} {T : Nat → Poly} : ∀ {n : Nat},
    (∀ i < n, bytesAt m (p + BitVec.ofNat 64 (384 * i)) 384 = encode12 (T i)) →
    bytesAt m p (384 * n) = KPke.catK (fun i => encode12 (T i)) n
  | 0, _ => rfl
  | n + 1, h => by
    rw [Nat.mul_succ, bytesAt_add, cat_at fun i hi => h i (by omega_using [hi]), h n (by omega_using [])]
    exact (KPke.foldK_succ (op := fun a b => a ++ b) (fun x => List.nil_append x) _ n).symm

variable {P : KemLay}

/-- `ek`'s bytes: the `k` `t̂[i]` and `ρ`, at `p`. -/
theorem ek_at {m : Mem} {p : Addr} {T : Nat → Poly} {ρ : List Byte}
    (h : ∀ i < P.k, bytesAt m (p + BitVec.ofNat 64 (384 * i)) 384 = encode12 (T i))
    (hr : bytesAt m (p + BitVec.ofNat 64 (384 * P.k)) 32 = ρ) :
    bytesAt m p P.ekLen = KPke.catK (fun i => encode12 (T i)) P.k ++ ρ := by
  rw [KemLay.ekLen, bytesAt_add, cat_at h, hr]

/-- `dk`'s bytes: `dk_PKE ‖ ek ‖ h ‖ z`, at `p`. -/
theorem dk_at {m : Mem} {p : Addr} {a b c d : List Byte} (ha : bytesAt m p (384 * P.k) = a)
    (hb : bytesAt m (p + BitVec.ofNat 64 (384 * P.k)) P.ekLen = b)
    (hc : bytesAt m (p + BitVec.ofNat 64 (768 * P.k + 32)) 32 = c)
    (hd : bytesAt m (p + BitVec.ofNat 64 (768 * P.k + 64)) 32 = d) : bytesAt m p P.dkLen = a ++ b ++ c ++ d := by
  have hc' : bytesAt m (p + BitVec.ofNat 64 (384 * P.k + P.ekLen)) 32 = c := by
    rw [show 384 * P.k + P.ekLen = 768 * P.k + 32 by simp only [KemLay.ekLen]; omega_using []]; exact hc
  have hd' : bytesAt m (p + BitVec.ofNat 64 (384 * P.k + P.ekLen + 32)) 32 = d := by
    rw [show 384 * P.k + P.ekLen + 32 = 768 * P.k + 64 by simp only [KemLay.ekLen]; omega_using []]; exact hd
  rw [show P.dkLen = 384 * P.k + P.ekLen + 32 + 32 by simp only [KemLay.ekLen, KemLay.dkLen]; omega_using [],
    bytesAt_add, bytesAt_add, bytesAt_add, ha, hb, hc', hd']

/-! ## Regions -/

/-- A buffer apart from what `TLW … i` describes. -/
theorem apart_R {s₀ : State} (hp : Pre P s₀) {i b o l : Nat} (hi : i ≤ P.k) (hb : b < 4) (f : o + l ≤ kL P b)
    (h3 : b = 3 → o + l ≤ 840 ∨ EP P ≤ o) (h1 : b = 1 → 384 * i ≤ o) (h2 : b = 2 → 384 * P.k + 384 * i ≤ o) :
    Apart P s₀ i (R (kA s₀) b o l) := by
  have hi' : 0 + 384 * i ≤ kL P 1 := by kl
  have hi'' : 0 + (384 * P.k + 384 * i) ≤ kL P 2 := by kl
  refine ⟨hp.args.rdisj (by decide) hb (by kl) f ?_, hp.args.rdisj (by decide) hb (by kl) f ?_,
    hp.args.rdisj (by decide) hb (by kl) f ?_, hp.args.rdisj (by decide) hb hi' f ?_,
    hp.args.rdisj (by decide) hb hi'' f ?_⟩ <;>
  · by_cases e : b = 3
    · have := h3 e; subst e; kl
    · by_cases e1 : b = 1
      · have := h1 e1; subst e1; kl
      · by_cases e2 : b = 2
        · have := h2 e2; subst e2; kl
        · kl

/-! ## The end -/

theorem pres_own : ∀ r ∈ preserved, r ∉ own → r ∉ [Reg.x0, .x30, .x24, .x25, .x26, .x27, .x28] := by decide

/-- Our caller's registers back, and the result. -/
theorem restore_ok {s₀ : State} (hp : Pre P s₀) {u : State} (hk : KB P s₀ u) :
    WP isa (.block [mov .x0 .x24, .ldr .x .x30 .x28 (SV P + 40), .ldr .x .x24 .x28 (SV P),
      .ldr .x .x25 .x28 (SV P + 8), .ldr .x .x26 .x28 (SV P + 16), .ldr .x .x27 .x28 (SV P + 24),
      .ldr .x .x28 .x28 (SV P + 32)]) u fun u' =>
      abiPreserved s₀ u' ∧ u'.gpr .x0 = u.gpr .x24 ∧ u'.mem = u.mem := by
  have hw := hp.wf
  have hsv : SV P % 8 = 0 ∧ SV P + 48 ≤ 32768 := by lom
  have cv := cov_r hp hk (b := 3) (o := SV P) (l := 48) (by decide) hp.sv
  have ld : ∀ k < 6, ∀ {w : State}, w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = kA s₀ 3 →
      w.gpr .x28 + BitVec.ofNat 64 (SV P + 8 * k) = kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k) ∧
      InRegions (w.rd ++ w.wr) (kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k)) 8 ∧
      w.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k)) 64 = s₀.gpr (own.getD k .x0) :=
    fun k hk' {w} ⟨hr, hw, hm, h28⟩ =>
      ⟨by rw [h28], by rw [hr, hw]; exact in_R cv (by omega_using [hk']) (by decide), by rw [hm]; exact hk.sv k hk'⟩
  have st : ∀ {w w' : State} {r : Reg}, Only [r] w w' → r ≠ .x28 →
      w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = kA s₀ 3 →
      w'.rd = u.rd ∧ w'.wr = u.wr ∧ w'.mem = u.mem ∧ w'.gpr .x28 = kA s₀ 3 :=
    fun h hr ⟨a, b, c, d⟩ => ⟨by rw [h.rd, a], by rw [h.wr, b], by rw [h.mem, c],
      by rw [h.get .x28 (by simpa using Ne.symm hr), d]⟩
  refine wp_mov fun s₁ h₁ e₁ => ?_
  have g₁ := st h₁ (by decide) ⟨rfl, rfl, rfl, hk.x28⟩
  have l₁ := ld 5 (by decide) g₁
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 5)) (by kl) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  have g₂ := st h₂ (by decide) g₁
  have l₂ := ld 0 (by decide) g₂
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 0)) (by kl) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  have g₃ := st h₃ (by decide) g₂
  have l₃ := ld 1 (by decide) g₃
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 1)) (by kl) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  have g₄ := st h₄ (by decide) g₃
  have l₄ := ld 2 (by decide) g₄
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 2)) (by kl) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  have g₅ := st h₅ (by decide) g₄
  have l₅ := ld 3 (by decide) g₅
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 3)) (by kl) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  have g₆ := st h₆ (by decide) g₅
  have l₆ := ld 4 (by decide) g₆
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 4)) (by kl) l₆.1 l₆.2.1 fun s₇ h₇ e₇ =>
    wp_nil ?_
  have o₇ : Only [.x0, .x30, .x24, .x25, .x26, .x27, .x28] u s₇ :=
    ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₇.sp, hk.sp], fun r hr => (o₇.vcs r hr).trans (hk.vcs r hr)⟩, ?_, o₇.mem⟩
  · by_cases ho : r ∈ own
    · rcases mem6 ho with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₇.get .x24, h₆.get .x24, h₅.get .x24, h₄.get .x24, e₃]; exact l₂.2.2
      · rw [h₇.get .x25, h₆.get .x25, h₅.get .x25, e₄]; exact l₃.2.2
      · rw [h₇.get .x26, h₆.get .x26, e₅]; exact l₄.2.2
      · rw [h₇.get .x27, e₆]; exact l₅.2.2
      · rw [e₇]; exact l₆.2.2
      · rw [h₇.get .x30, h₆.get .x30, h₅.get .x30, h₄.get .x30, h₃.get .x30, e₂]; exact l₁.2.2
    · rw [o₇.get r (pres_own r hr ho), hk.cs r hr ho]
  · rw [h₇.get .x0, h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁]

/-- A region apart from what `EndInvW` (`Kem16/KgCommon.lean`) describes. -/
abbrev Far (P : KemLay) (s₀ : State) (r : Region) : Prop :=
  Apart P s₀ P.k r ∧ (R (kA s₀) 1 (384 * P.k) 32).Disjoint r ∧ (R (kA s₀) 2 (768 * P.k) 32).Disjoint r

theorem far_R {s₀ : State} (hp : Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL P b)
    (h3 : b = 3 → o + l ≤ 840 ∨ EP P ≤ o) (h1 : b ≠ 1) (h2 : b = 2 → 768 * P.k + 32 ≤ o) :
    Far P s₀ (R (kA s₀) b o l) :=
  ⟨apart_R hp (Nat.le_refl _) hb f h3 (fun e => absurd e h1) (fun e => by have := h2 e; omega_using [this]),
    hp.args.rdisj (by decide) hb (by kl) f (.inl (Ne.symm h1)),
    hp.args.rdisj (by decide) hb (by kl) f (by
      by_cases e : b = 2
      · have := h2 e; subst e; omega_using [this]
      · exact .inl (Ne.symm e))⟩

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-!
# ML-KEM on AArch64: `keygen`, ML-KEM-768's parameter set

ML-KEM-768's layout is well formed (`wf768`), and a state satisfying the
precondition of `keygen` (`sat`), for the functions of `Kem16/` and `KgH/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-! ## Constant time -/

variable (hP : P.Wf)
include hP

omit hP

/-! ## ML-KEM-768 -/

theorem wf768 : lay768.Wf := ⟨by decide⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1184⟩, ⟨0x3000, 2400⟩, ⟨0x10000, 32768⟩]

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-!
# ML-KEM on AArch64: what the proofs of `encaps` and `decaps` share

For a well-formed parameter set `P` (`KemLay.Wf`), stated once.

A function's buffers (`Layout`): its `nb` pointer arguments (`kA`), the first
`nrd` read and the others written, and the four it keeps in `x25`–`x28`
(`slot`, with `scratch` in `x28`). What holds from the prologue to the
epilogue (`KB`): the pointers, our caller's registers saved in `scratch`, the
other callee-saved registers, and the buffers the function only reads. Then
the region facts the calls need, reduced to arithmetic on offsets, and the
prologue and epilogue.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- A function's buffers: `nb` pointer arguments of lengths `len`, the
first `nrd` read and the others written; argument `slot k` is kept in
`slotReg k` (`scratch` is `slot 3`). -/
structure Layout where
  nb : Nat
  nrd : Nat
  len : Nat → Nat
  slot : Nat → Nat

/-- `scratch`. -/
abbrev Layout.sc (L : Layout) : Nat := L.slot 3

/-- Argument `b`. -/
def kA (s₀ : State) (b : Nat) : Addr := s₀.gpr (argReg b)

/-- The arguments' regions `⟨A b, len b⟩` (for `b < nb`) are disjoint if one
of them is written (`nrd ≤ b`), less than 64 KiB, and apart from the 16 bytes
below `sp`. -/
structure KArgs (A : Nat → Addr) (ln : Nat → Nat) (nb nrd : Nat) (sp : Addr) : Prop where
  disj : ∀ b < nb, ∀ c < nb, b ≠ c → nrd ≤ b ∨ nrd ≤ c → Region.Disjoint ⟨A b, ln b⟩ ⟨A c, ln c⟩
  len : ∀ b < nb, ln b < 65536
  stk : ∀ b < nb, Region.Disjoint ⟨sp - 16, 16⟩ ⟨A b, ln b⟩

theorem KArgs.rdisj {A : Nat → Addr} {ln : Nat → Nat} {nb nrd : Nat} {sp : Addr} (h : KArgs A ln nb nrd sp)
    {b₁ o₁ l₁ b₂ o₂ l₂ : Nat} (hb₁ : b₁ < nb) (hb₂ : b₂ < nb) (f₁ : o₁ + l₁ ≤ ln b₁)
    (f₂ : o₂ + l₂ ≤ ln b₂) (hw : b₁ = b₂ ∨ nrd ≤ b₁ ∨ nrd ≤ b₂) (hs : b₁ ≠ b₂ ∨ o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (R A b₁ o₁ l₁).Disjoint (R A b₂ o₂ l₂) := by
  by_cases hb : b₁ = b₂
  · subst hb
    obtain hl := h.len b₁ hb₁
    obtain hs' : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁ := hs.resolve_left (fun h => h rfl)
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    exact sep_off (A b₁) hs' (by omega_arith) (by omega_arith) x (Nat.lt_of_succ_le h₁) (Nat.lt_of_succ_le h₂)
  · exact ((h.disj b₁ hb₁ b₂ hb₂ hb (hw.resolve_left hb)).sub_left (R.sub f₁)).sub_right (R.sub f₂)

theorem KArgs.stkR {A : Nat → Addr} {ln : Nat → Nat} {nb nrd : Nat} {sp : Addr} (h : KArgs A ln nb nrd sp)
    {b o l : Nat} (hb : b < nb) (f : o + l ≤ ln b) : Region.Disjoint ⟨sp - 16, 16⟩ (R A b o l) :=
  (h.stk b hb).sub_right (R.sub f)

structure Pre (P : KemLay) (L : Layout) (s₀ : State) : Prop where
  rd : ∀ b < L.nrd, (⟨kA s₀ b, L.len b⟩ : Region) ∈ s₀.rd
  wr : s₀.wr = (List.range' L.nrd (L.nb - L.nrd)).map fun b => ⟨kA s₀ b, L.len b⟩
  args : KArgs (kA s₀) L.len L.nb L.nrd s₀.sp
  sp16 : 16 ≤ s₀.sp.toNat
  slots : ∀ k < 4, L.slot k < L.nb
  scw : L.nrd ≤ L.sc
  scl : L.len L.sc = P.scl
  wf : P.Wf

/-- Our caller's `x24`–`x28` and `x30`, saved in `scratch`. -/
def Saved (P : KemLay) (L : Layout) (s₀ : State) (m : Mem) : Prop :=
  ∀ k < 6, m.readW (kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * k)) 64 = s₀.gpr (kemOwn.getD k .x0)

/-- From the prologue on. -/
structure KB (P : KemLay) (L : Layout) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ptr : ∀ k < 4, s.gpr (slotReg k) = kA s₀ (L.slot k)
  cs : ∀ r ∈ preserved, r ∉ kemOwn → s.gpr r = s₀.gpr r
  sv : Saved P L s₀ s.mem
  ro : ∀ b < L.nrd, bytesAt s.mem (kA s₀ b) (L.len b) = bytesAt s₀.mem (kA s₀ b) (L.len b)
  lens : ∀ b < L.nb, L.len b < 65536
  nrd : ∀ {b}, b < L.nrd → b < L.nb
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

variable {L : Layout}

theorem KB.x28 {s₀ s : State} (h : KB P L s₀ s) : s.gpr .x28 = kA s₀ L.sc := h.ptr 3 (by decide)
theorem KB.x25 {s₀ s : State} (h : KB P L s₀ s) : s.gpr .x25 = kA s₀ (L.slot 0) := h.ptr 0 (by decide)
theorem KB.x26 {s₀ s : State} (h : KB P L s₀ s) : s.gpr .x26 = kA s₀ (L.slot 1) := h.ptr 1 (by decide)
theorem KB.x27 {s₀ s : State} (h : KB P L s₀ s) : s.gpr .x27 = kA s₀ (L.slot 2) := h.ptr 2 (by decide)

theorem slot_pres {k : Nat} (hk : k < 4) : slotReg k ∈ preserved ∧ slotReg k ≠ .x30 := by
  rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> decide

/-- The saved registers are bytes `[SV, SV + 48)` of `scratch`. -/
abbrev svR (P : KemLay) (L : Layout) (s₀ : State) : Region := R (kA s₀) L.sc (SV P) 48

theorem Saved.frame {s₀ : State} {m m' : Mem} (h : Saved P L s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (svR P L s₀).Disjoint r) : Saved P L s₀ m' := fun k hk => by
  rw [← h k hk]
  refine hf.readW (r := svR P L s₀) ?_ hd (by decide)
  rw [show kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * k) = kA s₀ L.sc + BitVec.ofNat 64 (SV P) + BitVec.ofNat 64 (8 * k)
    by rw [ptr_add]]
  exact contains_off (by omega_arith) (by decide)

/-- A region apart from the saved registers and from the buffers the function only reads. -/
abbrev Safe (P : KemLay) (L : Layout) (s₀ : State) (r : Region) : Prop :=
  (svR P L s₀).Disjoint r ∧ ∀ b < L.nrd, Region.Disjoint ⟨kA s₀ b, L.len b⟩ r

/-- The callee-saved registers but `x24` and `x30`. -/
abbrev keptK : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

theorem pres_keptK : ∀ r ∈ preserved, r ∉ kemOwn → r ∈ keptK := by decide

theorem slot_keptK : ∀ k < 4, slotReg k ∈ keptK := by decide

/-- Memory changes only in safe regions, and no register the function keeps. -/
theorem KB.frame {s₀ s s' : State} (h : KB P L s₀ s) {rs : List Region} {regs : List Reg}
    (hk : Keep regs s s') (hf : Frame rs s.mem s'.mem) (hr : ∀ r ∈ keptK, r ∉ regs)
    (hd : ∀ r ∈ rs, Safe P L s₀ r) : KB P L s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    fun k hk' => by rw [hk.get _ (hr _ (slot_keptK k hk')), h.ptr k hk'],
    fun r hp ho => by rw [hk.get r (hr r (pres_keptK r hp ho)), h.cs r hp ho],
    h.sv.frame hf fun r hr => (hd r hr).1,
    fun b hb => by
      rw [bytesAt_frame hf (fun r hr => (hd r hr).2 b hb) (by have := h.lens b (h.nrd hb); omega_arith), h.ro b hb],
    h.lens, h.nrd, fun r hr => (hk.vcs r hr).trans (h.vcs r hr)⟩

theorem KB.block {s₀ s s' : State} (h : KB P L s₀ s) {regs : List Reg} (hk : Keep regs s s')
    (hm : s'.mem = s.mem) (hr : ∀ r ∈ keptK, r ∉ regs) : KB P L s₀ s' :=
  h.frame (rs := []) hk (by rw [hm]; exact Frame.refl _ _) hr (fun _ h => by cases h)

/-- A call, which changes only memory in safe regions and registers that are
not callee-saved. -/
theorem KB.call {s₀ s s' : State} (h : KB P L s₀ s) {rs : List Region} (hk : Kept rs s s')
    (hd : ∀ r ∈ rs, Safe P L s₀ r) : KB P L s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    fun k hk' => by rw [hk.cs _ (slot_pres hk').1 (slot_pres hk').2, h.ptr k hk'],
    fun r hp ho => by rw [hk.cs r hp (fun e => ho (by rw [e]; decide)), h.cs r hp ho],
    h.sv.frame hk.frame fun r hr => (hd r hr).1,
    fun b hb => by
      rw [bytesAt_frame hk.frame (fun r hr => (hd r hr).2 b hb) (by have := h.lens b (h.nrd hb); omega_arith),
        h.ro b hb],
    h.lens, h.nrd, fun r hr => (hk.vcs r hr).trans (h.vcs r hr)⟩

/-- Arithmetic on the offsets, with the facts of `‹Pre _ _ _›`. -/
macro "kom" : tactic => `(tactic| ((try have := (‹Pre _ _ _›).wf.facts); lom))

/-! ## Regions -/

theorem Pre.lt {s₀ : State} (hp : Pre P L s₀) {k : Nat} (hk : k < 4) : L.slot k < L.nb := hp.slots k hk

theorem Pre.scb {s₀ : State} (hp : Pre P L s₀) : L.sc < L.nb := hp.slots 3 (by decide)

/-- The saved registers are in `scratch`. -/
theorem Pre.sv {s₀ : State} (hp : Pre P L s₀) : SV P + 48 ≤ L.len L.sc := by
  have := hp.wf; rw [hp.scl]; lom

/-- A buffer of `scratch`. -/
theorem Pre.fs {s₀ : State} (hp : Pre P L s₀) {o l : Nat} (h : o + l ≤ SV P + 48) : o + l ≤ L.len L.sc :=
  Nat.le_trans h hp.sv

/-- A written buffer is safe, if apart from the saved registers. -/
theorem safe_R {s₀ : State} (hp : Pre P L s₀) {b o l : Nat} (hb : L.nrd ≤ b ∧ b < L.nb) (f : o + l ≤ L.len b)
    (hs : b ≠ L.sc ∨ SV P + 48 ≤ o ∨ o + l ≤ SV P) : Safe P L s₀ (R (kA s₀) b o l) :=
  ⟨hp.args.rdisj hp.scb hb.2 hp.sv f (.inr (.inl hp.scw)) (by
      rcases hs with hs | hs
      · exact .inl (Ne.symm hs)
      · exact .inr (by omega_arith)),
    fun c hc => (hp.args.disj c (by omega_arith) b hb.2 (by omega_arith) (.inr hb.1)).sub_right (R.sub f)⟩

theorem below_R {s₀ : State} (hp : Pre P L s₀) {b o l : Nat} (hb : b < L.nb) (f : o + l ≤ L.len b) :
    (R (kA s₀) b o l).Disjoint (below s₀.sp 16) := by
  rw [below16]; exact (hp.args.stkR hb f).symm

theorem safe_below {s₀ : State} (hp : Pre P L s₀) : Safe P L s₀ (below s₀.sp 16) :=
  ⟨below_R hp hp.scb hp.sv, fun c hc => by
    rw [below16]; exact (hp.args.stk c (by have := hp.scw; have := hp.scb; omega_arith)).symm⟩

/-- A buffer of `scratch` below the saved registers is safe. -/
theorem safe_scr {s₀ : State} (hp : Pre P L s₀) {o l : Nat} (h : o + l ≤ SV P) : Safe P L s₀ (R (kA s₀) L.sc o l) :=
  safe_R hp ⟨hp.scw, hp.scb⟩ (hp.fs (by omega_arith)) (.inr (.inr h))

theorem stk_R {s₀ s : State} (hp : Pre P L s₀) (h : KB P L s₀ s) {b o l : Nat} (hb : b < L.nb)
    (f : o + l ≤ L.len b) : (stk s).Disjoint (R (kA s₀) b o l) := by
  rw [stk_sp h.sp]; exact hp.args.stkR hb f

/-- Regions a callee may write. -/
theorem cov_w {s₀ s : State} (hp : Pre P L s₀) (h : KB P L s₀ s) {b o l : Nat} (hb : L.nrd ≤ b ∧ b < L.nb)
    (f : o + l ≤ L.len b) : Covers [R (kA s₀) b o l] s.wr := by
  rw [h.wr, hp.wr]
  exact R.cov (List.mem_map.mpr ⟨b, List.mem_range'_1.mpr ⟨hb.1, by omega_arith⟩, rfl⟩) f

/-- Regions a callee may read. -/
theorem cov_r {s₀ s : State} (hp : Pre P L s₀) (h : KB P L s₀ s) {b o l : Nat} (hb : b < L.nb)
    (f : o + l ≤ L.len b) : Covers [R (kA s₀) b o l] (s.rd ++ s.wr) := by
  rw [h.rd, h.wr, hp.wr]
  by_cases hr : b < L.nrd
  · exact R.cov (List.mem_append_left _ (hp.rd b hr)) f
  · exact R.cov (List.mem_append_right _
      (List.mem_map.mpr ⟨b, List.mem_range'_1.mpr ⟨by omega_arith, by omega_arith⟩, rfl⟩)) f

/-- Scratch buffers. -/
theorem cov_s {s₀ s : State} (hp : Pre P L s₀) (h : KB P L s₀ s) {o l : Nat} (f : o + l ≤ SV P + 48) :
    Covers [R (kA s₀) L.sc o l] s.wr :=
  cov_w hp h ⟨hp.scw, hp.scb⟩ (hp.fs f)

theorem cov_sr {s₀ s : State} (hp : Pre P L s₀) (h : KB P L s₀ s) {o l : Nat} (f : o + l ≤ SV P + 48) :
    Covers [R (kA s₀) L.sc o l] (s.rd ++ s.wr) :=
  cov_r hp h hp.scb (hp.fs f)

/-- Two buffers of `scratch`. -/
theorem sdisj {s₀ : State} (hp : Pre P L s₀) {o₁ l₁ o₂ l₂ : Nat} (f₁ : o₁ + l₁ ≤ SV P + 48)
    (f₂ : o₂ + l₂ ≤ SV P + 48) (h : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (R (kA s₀) L.sc o₁ l₁).Disjoint (R (kA s₀) L.sc o₂ l₂) :=
  hp.args.rdisj hp.scb hp.scb (hp.fs f₁) (hp.fs f₂) (.inl rfl) (.inr h)

theorem hsetup {s₀ s : State} (hp : Pre P L s₀) (h : KB P L s₀ s) {rate : Nat} (hr : rate ∈ Spec.Sha3.rates) :
    HSetup .x28 ST WK rate s := by
  have hw := hp.wf
  obtain f : ∀ {o l : Nat}, o + l ≤ 840 → o + l ≤ SV P + 48 := fun h => by lom
  obtain e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) L.sc o l := fun o l => by
    rw [h.x28]
  refine ⟨by decide, by decide, by decide, hr, ?_, by rw [h.sp]; exact hp.sp16, ?_, ?_, ?_⟩
  · rw [e, e]; exact sdisj hp (f (by decide)) (f (by decide)) (by decide)
  · rw [e]; exact stk_R hp h hp.scb (hp.fs (f (by decide)))
  · rw [e]; exact stk_R hp h hp.scb (hp.fs (f (by decide)))
  · rw [e, e]; exact covers_cons (cov_s hp h (f (by decide))) (cov_s hp h (f (by decide)))

/-- A piece at bytes `[o, o + l)` of the buffer in `slotReg k`, apart from the
Keccak state and working space. -/
theorem pieceOk {s₀ s : State} (hp : Pre P L s₀) (h : KB P L s₀ s) {w : Bool} {k o l : Nat} (hk : k < 4)
    (f : o + l ≤ L.len (L.slot k)) (hs : L.slot k ≠ L.sc ∨ 840 ≤ o) (hl : l < 65536)
    (hw : w = true → L.nrd ≤ L.slot k) : PieceOk .x28 ST WK s w ⟨slotReg k, o, l⟩ := by
  obtain hb := hp.lt hk
  obtain eb : preg s ⟨slotReg k, o, l⟩ = R (kA s₀) (L.slot k) o l := by simp only [preg, h.ptr k hk]
  obtain e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) L.sc o l := fun o l => by
    rw [h.x28]
  obtain ho : o < 65536 := by have := hp.args.len _ hb; omega_arith
  obtain fs : ∀ {o l : Nat}, o + l ≤ 840 → o + l ≤ L.len L.sc := fun h => hp.fs (by have := hp.wf; lom)
  refine ⟨slot_pres hk, ho, hl, ?_, ?_, ?_, ?_⟩
  · rw [eb, VG.Proof.MlKem.AArch64.STr, e]
    exact hp.args.rdisj hb hp.scb f (fs (by decide)) (.inr (.inr hp.scw)) (by
      rcases hs with hs | hs
      · exact .inl hs
      · exact .inr (.inr (by simp only [KEM.ST]; omega_arith)))
  · rw [eb, VG.Proof.MlKem.AArch64.WKr, e]
    exact hp.args.rdisj hb hp.scb f (fs (by decide)) (.inr (.inr hp.scw)) (by
      rcases hs with hs | hs
      · exact .inl hs
      · exact .inr (.inr (by simp only [KEM.WK]; omega_arith)))
  · rw [eb]; exact stk_R hp h hb f
  · rw [eb]
    cases w
    · exact cov_r hp h hb f
    · exact cov_w hp h ⟨hw rfl, hb⟩ f

/-- An output of a hash: bytes `[o, o + l)` of a written buffer, apart from
the saved registers. -/
def OutOk (P : KemLay) (L : Layout) (p : Piece) : Prop :=
  ∃ k o l, p = ⟨slotReg k, o, l⟩ ∧ k < 4 ∧ L.nrd ≤ L.slot k ∧ o + l ≤ L.len (L.slot k) ∧
    (L.slot k ≠ L.sc ∨ SV P + 48 ≤ o ∨ o + l ≤ SV P)

/-- A hash keeps what holds throughout. -/
theorem KB.hash {s₀ s s' : State} (hp : Pre P L s₀) (h : KB P L s₀ s) {outs : List Piece}
    (hk : Kept (STr .x28 ST s :: WKr .x28 WK s :: below s.sp 16 :: outs.map (preg s)) s s')
    (ho : ∀ p ∈ outs, OutOk P L p) : KB P L s₀ s' := by
  have hw := hp.wf
  refine h.call hk fun r hr => ?_
  obtain e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) L.sc o l := fun o l => by
    rw [h.x28]
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [VG.Proof.MlKem.AArch64.STr, e]; exact safe_scr hp (by lom)
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [VG.Proof.MlKem.AArch64.WKr, e]; exact safe_scr hp (by lom)
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [h.sp]; exact safe_below hp
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
  obtain ⟨k, o, l, rfl, hk, hw, f, hs⟩ := ho p hp'
  simp only [preg, h.ptr k hk]
  exact safe_R hp ⟨hw, hp.lt hk⟩ f hs

/-! ## The prologue and the epilogue -/

theorem argReg_not (b : Nat) : argReg b ≠ .x24 ∧ argReg b ≠ .x25 ∧ argReg b ≠ .x26 ∧ argReg b ≠ .x27 ∧
    argReg b ≠ .x28 := by
  unfold argReg
  rcases b with _ | _ | _ | _ | _ | b <;> simp

theorem cov_w₀ {s₀ : State} (hp : Pre P L s₀) {b o l : Nat} (hb : L.nrd ≤ b ∧ b < L.nb)
    (f : o + l ≤ L.len b) : Covers [R (kA s₀) b o l] s₀.wr := by
  rw [hp.wr]
  exact R.cov (List.mem_map.mpr ⟨b, List.mem_range'_1.mpr ⟨hb.1, by omega_arith⟩, rfl⟩) f

/-- What the prologue leaves. -/
structure AfterPro (P : KemLay) (L : Layout) (s₀ s : State) : Prop where
  kb : KB P L s₀ s
  x24 : s.gpr .x24 = 1
  keep : Keep [.x25, .x26, .x27, .x28, .x24] s₀ s
  mem : s.mem = s₀.mem ∨ Frame [svR P L s₀] s₀.mem s.mem

theorem pres_pro : ∀ r ∈ preserved, r ∉ kemOwn → r ∉ [Reg.x25, .x26, .x27, .x28, .x24] := by decide

theorem prologue_ok {s₀ : State} (hp : Pre P L s₀) :
    WP isa (.block (P.kemPrologue L.sc [L.slot 0, L.slot 1, L.slot 2, L.slot 3])) s₀ (AfterPro P L s₀) := by
  have hw := hp.wf
  rw [KemLay.kemPrologue, List.append_assoc, WP.block_append_iff]
  obtain hin : ∀ k < kemOwn.length, InRegions s₀.wr (kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * k)) 8 :=
    fun k hk => in_R (cov_w₀ hp ⟨hp.scw, hp.scb⟩ (o := SV P) (l := 48) hp.sv) (k := 8 * k)
      (n := 8) (by simp only [kemOwn, List.length_cons, List.length_nil] at hk; omega_arith) (by decide)
  obtain hsv : SV P + 8 * kemOwn.length ≤ 32768 := by simp only [kemOwn, List.length_cons, List.length_nil]; lom
  refine WP.mono (WP.preservedV (KeyGen.saves_ok (kA s₀ L.sc) (argReg L.sc) (SV P) kemOwn hsv (by lom) 6
    (by decide) rfl hin) (hc := rfl))
    fun s₁ ⟨⟨g₁, r₁, w₁, p₁, z₁, f₁⟩, hv₁⟩ => ?_
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_zero,
    List.getD_cons_succ]
  refine wp_mov fun s₂ h₂ e₂ => wp_mov fun s₃ h₃ e₃ => wp_mov fun s₄ h₄ e₄ => wp_mov fun s₅ h₅ e₅ =>
    wp_movz fun s₆ h₆ e₆ => wp_nil ?_
  obtain o₆ : Only [.x25, .x26, .x27, .x28, .x24] s₁ s₆ := ((((h₂.trans h₃).trans h₄).trans h₅).trans h₆).mono
  obtain k₆ : Keep [.x25, .x26, .x27, .x28, .x24] s₀ s₆ :=
    ⟨fun r hr => by rw [o₆.get r hr, g₁], by rw [o₆.rd, r₁], by rw [o₆.wr, w₁], by rw [o₆.sp, p₁], fun r hr => (o₆.vcs r hr).trans (hv₁ r hr)⟩
  obtain a : ∀ (b : Nat) {w w' : State} {r : Reg}, Only [r] w w' → r ∈ [Reg.x24, .x25, .x26, .x27, .x28] →
      w'.gpr (argReg b) = w.gpr (argReg b) := fun b _ _ r h hr => h.get _ fun h' => by
    obtain e := List.mem_singleton.mp h'
    have := argReg_not b
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    exacts [this.1 e, this.2.1 e, this.2.2.1 e, this.2.2.2.1 e, this.2.2.2.2 e]
  obtain v₁ : ∀ b, s₁.gpr (argReg b) = kA s₀ b := fun b => by rw [g₁]; rfl
  refine ⟨⟨k₆.rd, k₆.wr, k₆.sp, fun k hk => ?_, fun r hr ho => k₆.get r (pres_pro r hr ho), fun k hk => ?_,
    fun b hb => ?_, hp.args.len, (fun hb => by have := hp.scw; have := hp.scb; omega_arith), k₆.vcs⟩, by rw [e₆]; rfl, k₆,
    .inr (by rw [o₆.mem]; exact f₁)⟩
  · rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [h₆.get (slotReg 0) (by decide), h₅.get (slotReg 0) (by decide), h₄.get (slotReg 0) (by decide),
        h₃.get (slotReg 0) (by decide), e₂, v₁]
    · rw [h₆.get (slotReg 1) (by decide), h₅.get (slotReg 1) (by decide), h₄.get (slotReg 1) (by decide),
        e₃, a _ h₂ (by decide), v₁]
    · rw [h₆.get (slotReg 2) (by decide), h₅.get (slotReg 2) (by decide), e₄, a _ h₃ (by decide),
        a _ h₂ (by decide), v₁]
    · rw [h₆.get (slotReg 3) (by decide), e₅, a _ h₄ (by decide), a _ h₃ (by decide), a _ h₂ (by decide), v₁]
  · rw [o₆.mem]; exact z₁ k hk
  · rw [o₆.mem]
    exact bytesAt_frame f₁ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hp.args.disj b (by have := hp.scw; have := hp.scb; omega_arith) L.sc hp.scb
        (by have := hp.scw; omega_arith) (.inr hp.scw)).sub_right (R.sub hp.sv)) (by
          have := hp.args.len b (by have := hp.scw; have := hp.scb; omega_arith); omega_arith)

/-- Our caller's registers back, and the result. -/
theorem epilogue_ok {s₀ : State} (hp : Pre P L s₀) {u : State} (hk : KB P L s₀ u) :
    WP isa (.block P.kemEpilogue) u fun u' =>
      abiPreserved s₀ u' ∧ u'.gpr .x0 = u.gpr .x24 ∧ u'.mem = u.mem := by
  have hw := hp.wf
  obtain h8 : SV P % 8 = 0 ∧ SV P + 48 ≤ 32768 := by lom
  obtain cv := cov_sr hp hk (o := SV P) (l := 48) (Nat.le_refl _)
  obtain ld : ∀ k < 6, ∀ {w : State}, w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = kA s₀ L.sc →
      w.gpr .x28 + BitVec.ofNat 64 (SV P + 8 * k) = kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * k) ∧
      InRegions (w.rd ++ w.wr) (kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * k)) 8 ∧
      w.mem.readW (kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * k)) 64 = s₀.gpr (kemOwn.getD k .x0) :=
    fun k hk' {w} ⟨hr, hw, hm, h28⟩ =>
      ⟨by rw [h28], by rw [hr, hw]; exact in_R cv (by omega_arith) (by decide), by rw [hm]; exact hk.sv k hk'⟩
  obtain st : ∀ {w w' : State} {r : Reg}, Only [r] w w' → r ≠ .x28 →
      w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = kA s₀ L.sc →
      w'.rd = u.rd ∧ w'.wr = u.wr ∧ w'.mem = u.mem ∧ w'.gpr .x28 = kA s₀ L.sc :=
    fun h hr ⟨a, b, c, d⟩ => ⟨by rw [h.rd, a], by rw [h.wr, b], by rw [h.mem, c],
      by rw [h.get .x28 (by simpa using Ne.symm hr), d]⟩
  rw [KemLay.kemEpilogue, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
  simp only [List.map_cons, List.map_nil]
  refine wp_mov fun s₁ h₁ e₁ => ?_
  obtain g₁ := st h₁ (by decide) ⟨rfl, rfl, rfl, hk.x28⟩
  obtain l₁ := ld 0 (by decide) g₁
  refine wp_ldrx (a := kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * 0)) (by lom) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  obtain g₂ := st h₂ (by decide) g₁
  obtain l₂ := ld 1 (by decide) g₂
  refine wp_ldrx (a := kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * 1)) (by lom) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  obtain g₃ := st h₃ (by decide) g₂
  obtain l₃ := ld 2 (by decide) g₃
  refine wp_ldrx (a := kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * 2)) (by lom) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  obtain g₄ := st h₄ (by decide) g₃
  obtain l₄ := ld 3 (by decide) g₄
  refine wp_ldrx (a := kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * 3)) (by lom) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  obtain g₅ := st h₅ (by decide) g₄
  obtain l₅ := ld 4 (by decide) g₅
  refine wp_ldrx (a := kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * 4)) (by lom) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  obtain g₆ := st h₆ (by decide) g₅
  obtain l₆ := ld 5 (by decide) g₆
  refine wp_ldrx (a := kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * 5)) (by lom) l₆.1 l₆.2.1 fun s₇ h₇ e₇ =>
    wp_nil ?_
  obtain o₇ : Only [.x0, .x24, .x30, .x25, .x26, .x27, .x28] u s₇ :=
    ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₇.sp, hk.sp], fun r hr => (o₇.vcs r hr).trans (hk.vcs r hr)⟩, ?_, o₇.mem⟩
  · by_cases ho : r ∈ kemOwn
    · rcases mem6 ho with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₇.get .x24 (by decide), h₆.get .x24 (by decide), h₅.get .x24 (by decide),
          h₄.get .x24 (by decide), h₃.get .x24 (by decide)]
        exact e₂.trans l₁.2.2
      · rw [h₇.get .x30 (by decide), h₆.get .x30 (by decide), h₅.get .x30 (by decide),
          h₄.get .x30 (by decide)]
        exact e₃.trans l₂.2.2
      · rw [h₇.get .x25 (by decide), h₆.get .x25 (by decide), h₅.get .x25 (by decide)]
        exact e₄.trans l₃.2.2
      · rw [h₇.get .x26 (by decide), h₆.get .x26 (by decide)]
        exact e₅.trans l₄.2.2
      · rw [h₇.get .x27 (by decide)]
        exact e₆.trans l₅.2.2
      · exact e₇.trans l₆.2.2
    · rw [o₇.get r (by revert r; decide), hk.cs r hr ho]
  · rw [h₇.get .x0 (by decide), h₆.get .x0 (by decide), h₅.get .x0 (by decide), h₄.get .x0 (by decide),
      h₃.get .x0 (by decide), h₂.get .x0 (by decide), e₁]

end VG.Proof.MlKem.AArch64.Kem
