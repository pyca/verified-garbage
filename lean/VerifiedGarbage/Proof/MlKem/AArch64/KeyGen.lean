module

public import VerifiedGarbage.Proof.MlKem.Scrubbed
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.MlKem.AArch64.KgA
import VerifiedGarbage.Proof.Framework.WriteBytes
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.MlKem.AArch64.KgA
meta import VerifiedGarbage.Proof.Framework.WriteBytes

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
