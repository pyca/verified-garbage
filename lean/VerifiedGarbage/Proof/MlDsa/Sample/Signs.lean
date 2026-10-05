import VerifiedGarbage.Spec.MlDsa
import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
import VerifiedGarbage.Proof.MlKem.KPke1024

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.Hash`. -/
section

/-!
# ML-DSA: `H` and `G` through the streaming sponge

`H` and `G` (SHAKE256 and SHAKE128) are the output of `squeezeFrom` from
position 0 of the state that padding the message leaves (`H_eq`, `G_eq`),
which is what a caller of `vg_keccak_absorb`, `vg_keccak_pad` and
`vg_keccak_squeeze` computes; and a shorter output is a prefix of a longer one
(`H_take`, `G_take`), so a bound larger than another draws the same first
bytes.
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa
open VG.Spec.Sha3
open VG.Proof.Sha3 (length_squeeze squeeze_getElem)

/-- The state after absorbing `m` padded with `suffix`, for the rate `rate`:
what `vg_keccak_pad` leaves. -/
abbrev padded (rate : Nat) (suffix : Byte) (m : List Byte) : State := absorb rate (pad rate suffix m)

theorem squeezeFrom_zero (rate : Nat) (S : State) (d : Nat) : squeezeFrom rate S 0 d = squeeze rate S d := by
  simp only [squeezeFrom, squeeze, Nat.zero_add, List.drop_zero]

/-- `H(s, d)`: rate 136, suffix `0x1f`. -/
theorem H_eq (s : List Byte) (d : Nat) : VG.Spec.MlDsa.H s d = squeezeFrom 136 (VG.Proof.MlDsa.Sample.padded 136 shakeSuffix s) 0 d := by
  rw [VG.Proof.MlDsa.Sample.squeezeFrom_zero]; rfl

/-- `G(s, d)`: rate 168, suffix `0x1f`. -/
theorem G_eq (s : List Byte) (d : Nat) : VG.Spec.MlDsa.G s d = squeezeFrom 168 (VG.Proof.MlDsa.Sample.padded 168 shakeSuffix s) 0 d := by
  rw [VG.Proof.MlDsa.Sample.squeezeFrom_zero]; rfl

/-- The first `d` bytes of a longer output. -/
theorem squeeze_take {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) {d d' : Nat}
    (h : d ≤ d') : (squeeze rate S d').take d = squeeze rate S d := by
  refine List.ext_getElem (by simp [length_squeeze hr hr']; omega) fun i h₁ h₂ => ?_
  rw [length_squeeze hr hr'] at h₂
  rw [List.getElem_take, squeeze_getElem hr hr' _ h₂, squeeze_getElem hr hr' _ (by omega)]

theorem H_length (s : List Byte) (d : Nat) : (VG.Spec.MlDsa.H s d).length = d := length_squeeze (by decide) (by decide) _ _

theorem G_length (s : List Byte) (d : Nat) : (VG.Spec.MlDsa.G s d).length = d := length_squeeze (by decide) (by decide) _ _

theorem H_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (VG.Spec.MlDsa.H s d').take d = VG.Spec.MlDsa.H s d :=
  VG.Proof.MlDsa.Sample.squeeze_take (by decide) (by decide) _ h

theorem G_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (VG.Spec.MlDsa.G s d').take d = VG.Spec.MlDsa.G s d :=
  VG.Proof.MlDsa.Sample.squeeze_take (by decide) (by decide) _ h

end VG.Proof.MlDsa.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.Mem`. -/
section

/-!
# ML-DSA: polynomials sampled into memory, for every target

The sampling functions store the coefficients of a polynomial one at a time:
`Stored m p L` says that the first `L.length` coefficients at `p` are those of
the list `L` (each as its representative less than `q`), and a polynomial
stored this way in full is `PolyIs` of the vector of the list
(`stored_polyIs`). A polynomial whose every coefficient holds a value is
`PolyIs` of it (`polyIs_of_coeffAt`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

theorem ifT {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ifF {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-- The address of coefficient `i` of the polynomial at `p`. -/
abbrev coeffAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (4 * i)

/-- The 1024 bytes of a polynomial at `p`. -/
abbrev polyR (p : Addr) : Region := ⟨p, 1024⟩

theorem coeffAt_eq (m : Mem) (p : Addr) (i : Nat) : VG.Spec.MlDsa.coeffAt m p i = m.readW (VG.Proof.MlDsa.Sample.coeffAddr p i) 32 := rfl

theorem coeff_contains (p : Addr) {i : Nat} (hi : i < 256) : (VG.Proof.MlDsa.Sample.polyR p).Contains (VG.Proof.MlDsa.Sample.coeffAddr p i) 4 :=
  Offset.contains_base p (by omega) (by omega)

theorem coeff_sep (p : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (h : i ≠ j) :
    Mem.Sep (VG.Proof.MlDsa.Sample.coeffAddr p i) 4 (VG.Proof.MlDsa.Sample.coeffAddr p j) 4 :=
  Offset.sep p (by omega) (by omega) (by omega)

/-- Writing coefficient `j` of the polynomial at `p`. -/
theorem coeffAt_writeW (m : Mem) (p : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (v : BitVec 32) :
    VG.Spec.MlDsa.coeffAt (m.writeW (VG.Proof.MlDsa.Sample.coeffAddr p j) v) p i = if j = i then v else VG.Spec.MlDsa.coeffAt m p i := by
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (VG.Proof.MlDsa.Sample.coeff_sep p hi hj (Ne.symm ‹_›)) (by decide)

/-- The word that represents `x`. -/
abbrev zw (x : VG.Spec.MlDsa.Zq) : BitVec 32 := BitVec.ofNat 32 x.val

theorem zw_toNat (x : VG.Spec.MlDsa.Zq) : (VG.Proof.MlDsa.Sample.zw x).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

/-- The coefficients `L` are stored at `p`. -/
def Stored (m : Mem) (p : Addr) (L : List VG.Spec.MlDsa.Zq) : Prop :=
  ∀ k < L.length, VG.Spec.MlDsa.coeffAt m p k = VG.Proof.MlDsa.Sample.zw (L.getD k 0)

theorem stored_nil (m : Mem) (p : Addr) : VG.Proof.MlDsa.Sample.Stored m p [] := fun _ h => absurd h (Nat.not_lt_zero _)

/-- Storing the next coefficient. -/
theorem stored_snoc {m : Mem} {p : Addr} {L : List VG.Spec.MlDsa.Zq} (h : VG.Proof.MlDsa.Sample.Stored m p L) (hL : L.length < 256) (x : VG.Spec.MlDsa.Zq) :
    VG.Proof.MlDsa.Sample.Stored (m.writeW (VG.Proof.MlDsa.Sample.coeffAddr p L.length) (VG.Proof.MlDsa.Sample.zw x)) p (L ++ [x]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  rw [VG.Proof.MlDsa.Sample.coeffAt_writeW _ _ (show k < 256 by omega) hL]
  by_cases e : L.length = k
  · subst e
    simp only [↓reduceIte]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · simp only [e, ↓reduceIte]
    rw [h k (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]

/-- `Fin.ofNat` of the word that represents `x` is `x`. -/
theorem ofNat_zw (x : VG.Spec.MlDsa.Zq) : Fin.ofNat VG.Spec.MlDsa.q (VG.Proof.MlDsa.Sample.zw x).toNat = x := by
  rw [VG.Proof.MlDsa.Sample.zw_toNat]; exact Fin.ext (Nat.mod_eq_of_lt x.isLt)

/-- The polynomial `f` is stored at `p` if each of its coefficients is. -/
theorem polyIs_of_coeffAt {m : Mem} {p : Addr} {f : VG.Spec.MlDsa.Poly} (h : ∀ i < VG.Spec.MlDsa.n, VG.Spec.MlDsa.coeffAt m p i = VG.Proof.MlDsa.Sample.zw f[i]!) :
    VG.Spec.MlDsa.PolyIs m p f := by
  refine ⟨fun i hi => by rw [h i hi, VG.Proof.MlDsa.Sample.zw_toNat]; exact (f[i]!).isLt, ?_⟩
  apply Vector.ext
  intro i hi
  simp only [VG.Spec.MlDsa.polyAt, Vector.getElem_ofFn]
  rw [h i hi, VG.Proof.MlDsa.Sample.ofNat_zw, getElem!_pos f i hi]

/-- The polynomial of a list of coefficients (0 past its end). -/
abbrev toPoly (L : List VG.Spec.MlDsa.Zq) : VG.Spec.MlDsa.Poly := Vector.ofFn fun i => L.getD i.val 0

/-- 256 coefficients stored: the polynomial. -/
theorem stored_polyIs {m : Mem} {p : Addr} {L : List VG.Spec.MlDsa.Zq} (h : VG.Proof.MlDsa.Sample.Stored m p L) (hL : L.length = 256) :
    VG.Spec.MlDsa.PolyIs m p (VG.Proof.MlDsa.Sample.toPoly L) :=
  VG.Proof.MlDsa.Sample.polyIs_of_coeffAt fun i hi => by
    rw [h i (by simp only [VG.Spec.MlDsa.n] at hi; omega), getElem!_pos (VG.Proof.MlDsa.Sample.toPoly L) i hi]
    simp only [VG.Proof.MlDsa.Sample.toPoly, Vector.getElem_ofFn]

/-- A stored list is unchanged by writes apart from the polynomial. -/
theorem stored_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (VG.Proof.MlDsa.Sample.polyR p).Disjoint r) {L : List VG.Spec.MlDsa.Zq} (h : VG.Proof.MlDsa.Sample.Stored m p L) (hL : L.length ≤ 256) :
    VG.Proof.MlDsa.Sample.Stored m' p L := fun k hk => by
  rw [VG.Proof.MlDsa.Sample.coeffAt_eq, hf.readW (VG.Proof.MlDsa.Sample.coeff_contains p (by omega)) hd (by decide)]
  exact h k hk

end VG.Proof.MlDsa.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.Ball`. -/
section

/-!
# ML-DSA: `SampleInBall` a byte at a time

An implementation that runs the loop of `SampleInBall` (Algorithm 29) over a
fixed number of bytes of output, doing nothing once `i = 256`, leaves `bFold τ
h (c, i) out` (`bStep` is one iteration): the polynomial and `i`. It computes
`SampleInBall` if `i` reaches 256 (`sampleInBall_some`), and otherwise so does
no shorter output (`sampleInBall_none`). The sign bits `h` are the bits of the
first 8 bytes of output (`bytesToBits_getD`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- One iteration of the loop of `SampleInBall` (lines 7–12 of Algorithm
29) on the polynomial and `i`, which does nothing once `i = 256`. -/
def bStep (τ : Nat) (h : Array Bool) (st : IPoly × Nat) (j : Byte) : IPoly × Nat :=
  if st.2 < VG.Spec.MlDsa.n then
    (if j.toNat > st.2 then st
    else ((st.1.set! st.2 st.1[j.toNat]!).set! j.toNat (if h.getD (st.2 + τ - 256) false then -1 else 1),
      st.2 + 1))
  else st

/-- The polynomial and `i` after the loop over the bytes of `L`. -/
def bFold (τ : Nat) (h : Array Bool) : IPoly × Nat → List Byte → IPoly × Nat
  | st, j :: L => VG.Proof.MlDsa.Sample.bFold τ h (VG.Proof.MlDsa.Sample.bStep τ h st j) L
  | st, [] => st

theorem bStep_le {τ : Nat} {h : Array Bool} {st : IPoly × Nat} (hs : st.2 ≤ VG.Spec.MlDsa.n) (j : Byte) :
    (VG.Proof.MlDsa.Sample.bStep τ h st j).2 ≤ VG.Spec.MlDsa.n := by
  unfold VG.Proof.MlDsa.Sample.bStep; split
  · split
    · exact hs
    · rename_i h1 _; exact h1
  · exact hs

theorem bStep_full {τ : Nat} {h : Array Bool} {st : IPoly × Nat} (hs : st.2 = VG.Spec.MlDsa.n) (j : Byte) :
    VG.Proof.MlDsa.Sample.bStep τ h st j = st := by
  unfold VG.Proof.MlDsa.Sample.bStep; rw [VG.Proof.MlDsa.Sample.ifF (by omega)]

theorem bFold_full {τ : Nat} {h : Array Bool} {st : IPoly × Nat} (hs : st.2 = VG.Spec.MlDsa.n) : ∀ L, VG.Proof.MlDsa.Sample.bFold τ h st L = st
  | j :: L => by rw [VG.Proof.MlDsa.Sample.bFold, VG.Proof.MlDsa.Sample.bStep_full hs, VG.Proof.MlDsa.Sample.bFold_full hs L]
  | [] => rfl

theorem bFold_le {τ : Nat} {h : Array Bool} {st : IPoly × Nat} (hs : st.2 ≤ VG.Spec.MlDsa.n) : ∀ L, (VG.Proof.MlDsa.Sample.bFold τ h st L).2 ≤ VG.Spec.MlDsa.n
  | j :: L => by rw [VG.Proof.MlDsa.Sample.bFold]; exact VG.Proof.MlDsa.Sample.bFold_le (VG.Proof.MlDsa.Sample.bStep_le hs j) L
  | [] => hs

theorem bFold_append (τ : Nat) (h : Array Bool) (st : IPoly × Nat) : ∀ L₁ L₂ : List Byte,
    VG.Proof.MlDsa.Sample.bFold τ h st (L₁ ++ L₂) = VG.Proof.MlDsa.Sample.bFold τ h (VG.Proof.MlDsa.Sample.bFold τ h st L₁) L₂
  | [], _ => rfl
  | j :: L₁, L₂ => by simp only [List.cons_append, VG.Proof.MlDsa.Sample.bFold]; exact VG.Proof.MlDsa.Sample.bFold_append τ h _ L₁ L₂

theorem bFold_snoc (τ : Nat) (h : Array Bool) (st : IPoly × Nat) (L : List Byte) (j : Byte) :
    VG.Proof.MlDsa.Sample.bFold τ h st (L ++ [j]) = VG.Proof.MlDsa.Sample.bStep τ h (VG.Proof.MlDsa.Sample.bFold τ h st L) j := by
  rw [VG.Proof.MlDsa.Sample.bFold_append]; rfl

/-- The loop, as `bFold`: it succeeds when `i` reaches 256. -/
theorem ballLoop_eq (τ : Nat) (h : Array Bool) {c : IPoly} {i : Nat} (hi : i ≤ VG.Spec.MlDsa.n) :
    ∀ L, ballLoop τ h c i L = if (VG.Proof.MlDsa.Sample.bFold τ h (c, i) L).2 = VG.Spec.MlDsa.n then some (VG.Proof.MlDsa.Sample.bFold τ h (c, i) L).1 else none
  | j :: L => by
    rw [ballLoop, VG.Proof.MlDsa.Sample.bFold]
    by_cases hn : i ≥ VG.Spec.MlDsa.n
    · rw [VG.Proof.MlDsa.Sample.ifT hn, VG.Proof.MlDsa.Sample.bStep_full (by simp only; omega), VG.Proof.MlDsa.Sample.bFold_full (by simp only; omega), VG.Proof.MlDsa.Sample.ifT (by simp only; omega)]
    · rw [VG.Proof.MlDsa.Sample.ifF hn]
      unfold VG.Proof.MlDsa.Sample.bStep
      dsimp only
      rw [VG.Proof.MlDsa.Sample.ifT (show i < VG.Spec.MlDsa.n by omega)]
      by_cases hj : j.toNat > i
      · rw [VG.Proof.MlDsa.Sample.ifT hj, VG.Proof.MlDsa.Sample.ifT hj]; exact VG.Proof.MlDsa.Sample.ballLoop_eq τ h hi L
      · rw [VG.Proof.MlDsa.Sample.ifF hj, VG.Proof.MlDsa.Sample.ifF hj]; exact VG.Proof.MlDsa.Sample.ballLoop_eq τ h (by omega) L
  | [] => by
    show (if i ≥ VG.Spec.MlDsa.n then some c else none) = if i = VG.Spec.MlDsa.n then some c else none
    by_cases hn : i = VG.Spec.MlDsa.n
    · rw [VG.Proof.MlDsa.Sample.ifT (by omega), VG.Proof.MlDsa.Sample.ifT hn]
    · rw [VG.Proof.MlDsa.Sample.ifF (by omega), VG.Proof.MlDsa.Sample.ifF hn]

/-- The sign bits of the output `out`. -/
abbrev signs (out : List Byte) : Array Bool := VG.Spec.MlDsa.bytesToBits (out.take 8)

/-- The polynomial and `i` after the loop over the bytes after the first 8. -/
abbrev ballFold (τ : Nat) (out : List Byte) : IPoly × Nat :=
  VG.Proof.MlDsa.Sample.bFold τ (VG.Proof.MlDsa.Sample.signs out) (Vector.replicate VG.Spec.MlDsa.n 0, 256 - τ) (out.drop 8)

theorem sampleInBall_eq (τ : Nat) {ρ : List Byte} {B : Nat} (hB : 8 ≤ B) :
    sampleInBall τ B ρ =
      if (VG.Proof.MlDsa.Sample.ballFold τ (VG.Spec.MlDsa.H ρ B)).2 = VG.Spec.MlDsa.n then some (VG.Proof.MlDsa.Sample.ballFold τ (VG.Spec.MlDsa.H ρ B)).1 else none := by
  rw [sampleInBall]
  rw [VG.Proof.MlDsa.Sample.ifF (by rw [VG.Proof.MlDsa.Sample.H_length]; omega), VG.Proof.MlDsa.Sample.ballLoop_eq τ _ (Nat.sub_le _ _)]

/-- `SampleInBall(ρ)` when `i` reaches 256 in the loop over the `B` bytes of
output. -/
theorem sampleInBall_some (τ : Nat) {ρ : List Byte} {B : Nat} (hB : 8 ≤ B) (h : (VG.Proof.MlDsa.Sample.ballFold τ (VG.Spec.MlDsa.H ρ B)).2 = 256) :
    sampleInBall τ B ρ = some (VG.Proof.MlDsa.Sample.ballFold τ (VG.Spec.MlDsa.H ρ B)).1 := by
  rw [VG.Proof.MlDsa.Sample.sampleInBall_eq τ hB, VG.Proof.MlDsa.Sample.ifT h]

/-- If `i` does not reach 256 in the loop over `B` bytes of output, neither
does it over the first `B'` bytes. -/
theorem sampleInBall_none (τ : Nat) {ρ : List Byte} {B B' : Nat} (h8 : 8 ≤ B') (hB : B' ≤ B)
    (h : (VG.Proof.MlDsa.Sample.ballFold τ (VG.Spec.MlDsa.H ρ B)).2 ≠ 256) : sampleInBall τ B' ρ = none := by
  rw [VG.Proof.MlDsa.Sample.sampleInBall_eq τ h8]
  have e : VG.Spec.MlDsa.H ρ B = VG.Spec.MlDsa.H ρ B' ++ (VG.Spec.MlDsa.H ρ B).drop B' := by rw [← VG.Proof.MlDsa.Sample.H_take ρ hB, List.take_append_drop]
  have et : (VG.Spec.MlDsa.H ρ B).take 8 = (VG.Spec.MlDsa.H ρ B').take 8 := by rw [e, List.take_append_of_le_length (by rw [VG.Proof.MlDsa.Sample.H_length]; omega)]
  have ed : (VG.Spec.MlDsa.H ρ B).drop 8 = (VG.Spec.MlDsa.H ρ B').drop 8 ++ (VG.Spec.MlDsa.H ρ B).drop B' := by
    rw [e, List.drop_append_of_le_length (by rw [VG.Proof.MlDsa.Sample.H_length]; omega), ← e]
  simp only [VG.Proof.MlDsa.Sample.ballFold, VG.Proof.MlDsa.Sample.signs, et, ed, VG.Proof.MlDsa.Sample.bFold_append] at h
  by_cases hf : (VG.Proof.MlDsa.Sample.ballFold τ (VG.Spec.MlDsa.H ρ B')).2 = VG.Spec.MlDsa.n
  · simp only [VG.Proof.MlDsa.Sample.ballFold, VG.Proof.MlDsa.Sample.signs] at hf
    exact absurd (by rw [VG.Proof.MlDsa.Sample.bFold_full hf]; exact hf) h
  · rw [VG.Proof.MlDsa.Sample.ifF hf]

/-! ## The sign bits -/

theorem testBit_eq (x k : Nat) : x.testBit k = decide (x / 2 ^ k % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  by_cases h : x / 2 ^ k % 2 = 1 <;> simp [h]

/-- Bit `k` of the bytes `z` (for `k < 8 |z|`), as a list. -/
theorem flatBits_getD (z : List Byte) {k : Nat} (hk : k < 8 * z.length) :
    (z.flatMap fun c => (List.range 8).map fun j => decide (c.toNat / 2 ^ j % 2 = 1)).getD k false =
      (z.getD (k / 8) 0).getLsbD (k % 8) := by
  induction z generalizing k with
  | nil => simp at hk
  | cons c z ih =>
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD]
    by_cases h8 : k < 8
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range h8]
      simp only [Option.map_some, Option.getD_some, Nat.div_eq_of_lt h8, List.getD_cons_zero,
        Nat.mod_eq_of_lt h8, BitVec.getLsbD, VG.Proof.MlDsa.Sample.testBit_eq]
    · rw [List.getElem?_append_right (by simp; omega), List.length_map, List.length_range,
        ← List.getD_eq_getElem?_getD, ih (by simp at hk; omega), show k / 8 = (k - 8) / 8 + 1 by omega,
        List.getD_cons_succ, show k % 8 = (k - 8) % 8 by omega]

/-- Bit `k` of the bytes `z` (for `k < 8 |z|`). -/
theorem bytesToBits_getD (z : List Byte) {k : Nat} (hk : k < 8 * z.length) :
    (VG.Spec.MlDsa.bytesToBits z).getD k false = (z.getD (k / 8) 0).getLsbD (k % 8) := by
  rw [VG.Spec.MlDsa.bytesToBits, Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  exact VG.Proof.MlDsa.Sample.flatBits_getD z hk

end VG.Proof.MlDsa.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask`. -/
section

/-!
# ML-DSA: `BitUnpack` as arithmetic on the bytes

The bits of a byte string `v` (`bytesToBits`) are those of the integer `leNat
v` whose little-endian encoding it is (`bytesToBits_getD_testBit`); so the `c`
bits of coefficient `i` of `BitUnpack` are `⌊leNat v / 2^(ic)⌋ mod 2^c`
(`bitUnpack_getElem`), which an implementation computes from the few bytes
that hold them.
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- The integer whose little-endian encoding is `v`. -/
def leNat : List Byte → Nat
  | [] => 0
  | c :: v => c.toNat + 2 ^ 8 * VG.Proof.MlDsa.Sample.leNat v

/-- Bit `k` of `leNat v`: bit `k mod 8` of byte `⌊k/8⌋` (0 past the end). -/
theorem testBit_leNat : ∀ (v : List Byte) (k : Nat), (VG.Proof.MlDsa.Sample.leNat v).testBit k = (v.getD (k / 8) 0).getLsbD (k % 8)
  | [], k => by simp [VG.Proof.MlDsa.Sample.leNat]
  | c :: v, k => by
    rw [VG.Proof.MlDsa.Sample.leNat, Nat.add_comm, Nat.testBit_two_pow_mul_add _ c.isLt]
    split
    · rename_i h
      rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      rfl
    · rename_i h
      rw [VG.Proof.MlDsa.Sample.testBit_leNat v, show k / 8 = (k - 8) / 8 + 1 by omega, List.getD_cons_succ,
        show k % 8 = (k - 8) % 8 by omega]

theorem bytesToBits_size (v : List Byte) : (VG.Spec.MlDsa.bytesToBits v).size = 8 * v.length := by
  simp only [VG.Spec.MlDsa.bytesToBits, List.size_toArray]
  induction v with
  | nil => rfl
  | cons c v ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih, List.length_cons]
    omega

/-- Bit `k` of the bits of `v`. -/
theorem bytesToBits_getD_testBit (v : List Byte) (k : Nat) :
    (VG.Spec.MlDsa.bytesToBits v).getD k false = (VG.Proof.MlDsa.Sample.leNat v).testBit k := by
  rw [VG.Proof.MlDsa.Sample.testBit_leNat]
  by_cases hk : k < 8 * v.length
  · exact VG.Proof.MlDsa.Sample.bytesToBits_getD v hk
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [VG.Proof.MlDsa.Sample.bytesToBits_size]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

/-- The integer of `c` bits of `X` from bit `P`. -/
theorem bitsToInteger_testBit (X : Nat) : ∀ (c P : Nat),
    bitsToInteger ((List.range c).map fun j => X.testBit (P + j)) = X / 2 ^ P % 2 ^ c
  | 0, P => by simp [bitsToInteger, Nat.mod_one]
  | c + 1, P => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have ih := VG.Proof.MlDsa.Sample.bitsToInteger_testBit X c (P + 1)
    have e : ((fun j => X.testBit (P + j)) ∘ Nat.succ) = fun j => X.testBit (P + 1 + j) := by
      funext j; simp only [Function.comp]; congr 1; omega
    simp only [bitsToInteger, List.foldr_cons] at ih ⊢
    rw [e, ih, Nat.add_zero]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [show 2 * (X / 2 ^ (P + 1) % 2 ^ c) = 2 ^ 1 * (X / 2 ^ (P + 1) % 2 ^ c) by rfl,
      Nat.testBit_two_pow_mul_add _ (by cases X.testBit P <;> decide), Nat.testBit_mod_two_pow,
      Nat.testBit_div_two_pow]
    split
    · rename_i h
      have : i = 0 := by omega
      subst this
      have := VG.Proof.MlDsa.Sample.testBit_eq X P
      cases hb : X.testBit P <;> rw [hb] at this <;> simp at this <;> simp <;> omega
    · rename_i h
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, show i - 1 + (P + 1) = i + P by omega]
      congr 1
      exact decide_eq_decide.mpr (by omega)

/-- Coefficient `i` of `BitUnpack(v, a, b)`: `b` minus the `c` bits of
`leNat v` from bit `ic`, for `c = bitlen (a + b)`. -/
theorem bitUnpack_getElem (v : List Byte) (a b : Nat) {i : Nat} (hi : i < VG.Spec.MlDsa.n) :
    (bitUnpack v a b)[i] = (b : Int) - (VG.Proof.MlDsa.Sample.leNat v / 2 ^ (i * bitlen (a + b)) % 2 ^ bitlen (a + b) : Nat) := by
  simp only [bitUnpack, Vector.getElem_ofFn, VG.Proof.MlDsa.Sample.bytesToBits_getD_testBit]
  rw [VG.Proof.MlDsa.Sample.bitsToInteger_testBit]

/-- The bits of a prefix are those of the whole. -/
theorem leNat_take_bits (L : List Byte) {k P c : Nat} (h : P + c ≤ 8 * k) :
    VG.Proof.MlDsa.Sample.leNat (L.take k) / 2 ^ P % 2 ^ c = VG.Proof.MlDsa.Sample.leNat L / 2 ^ P % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow,
    VG.Proof.MlDsa.Sample.testBit_leNat, VG.Proof.MlDsa.Sample.testBit_leNat]
  by_cases hj : j < c
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  · simp [hj]

/-- The width `c = 1 + bitlen (γ₁ - 1)` of the coefficients of `ExpandMask`. -/
def emC (γ : Nat) : Nat := if γ = 2 ^ 17 then 18 else 20

theorem emC_eq {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) :
    1 + bitlen (γ - 1) = VG.Proof.MlDsa.Sample.emC γ ∧ bitlen (γ - 1 + γ) = VG.Proof.MlDsa.Sample.emC γ ∧ γ = 2 ^ (VG.Proof.MlDsa.Sample.emC γ - 1) := by
  rcases hγ with rfl | rfl <;> decide

/-- Coefficient `i` of the polynomial of `ExpandMask`, from the first 640
bytes `X` of the output (at least the `32c` it unpacks). -/
theorem expandMask_getElem (ρ : List Byte) {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) {i : Nat} (hi : i < 256) :
    (toRq (bitUnpack (VG.Spec.MlDsa.H ρ (32 * (1 + bitlen (γ - 1)))) (γ - 1) γ))[i]! =
      ofInt ((γ : Int) - (VG.Proof.MlDsa.Sample.leNat (VG.Spec.MlDsa.H ρ 640) / 2 ^ (i * VG.Proof.MlDsa.Sample.emC γ) % 2 ^ VG.Proof.MlDsa.Sample.emC γ : Nat)) := by
  obtain ⟨e1, e2, _⟩ := VG.Proof.MlDsa.Sample.emC_eq hγ
  have hc : VG.Proof.MlDsa.Sample.emC γ ≤ 20 := by unfold VG.Proof.MlDsa.Sample.emC; split <;> omega
  rw [getElem!_pos _ i hi]
  simp only [toRq, Vector.getElem_map]
  rw [VG.Proof.MlDsa.Sample.bitUnpack_getElem _ _ _ hi, e1, e2,
    ← VG.Proof.MlDsa.Sample.H_take ρ (show 32 * VG.Proof.MlDsa.Sample.emC γ ≤ 640 by omega), VG.Proof.MlDsa.Sample.leNat_take_bits _ (by
      have : i * VG.Proof.MlDsa.Sample.emC γ + VG.Proof.MlDsa.Sample.emC γ ≤ 256 * VG.Proof.MlDsa.Sample.emC γ := by
        have := Nat.mul_le_mul_right (VG.Proof.MlDsa.Sample.emC γ) (show i + 1 ≤ 256 by omega); rw [Nat.add_mul] at this; omega
      omega)]

/-! ## The sign bits of `SampleInBall` -/

/-- Bit `k` of the sign bits: bit `k` of the first 8 bytes of the output, as
a little-endian integer. -/
theorem signs_getD (X : List Byte) (k : Nat) :
    (VG.Proof.MlDsa.Sample.signs X).getD k false = (VG.Proof.MlDsa.Sample.leNat (X.take 8)).testBit k := by
  rw [VG.Proof.MlDsa.Sample.signs, VG.Proof.MlDsa.Sample.bytesToBits_getD_testBit]

theorem bStep_ge {τ : Nat} {h : Array Bool} (st : IPoly × Nat) (j : Byte) : st.2 ≤ (VG.Proof.MlDsa.Sample.bStep τ h st j).2 := by
  unfold VG.Proof.MlDsa.Sample.bStep; split
  · split <;> simp
  · exact Nat.le_refl _

theorem bFold_ge {τ : Nat} {h : Array Bool} : ∀ (st : IPoly × Nat) (L : List Byte), st.2 ≤ (VG.Proof.MlDsa.Sample.bFold τ h st L).2
  | st, j :: L => by rw [VG.Proof.MlDsa.Sample.bFold]; exact Nat.le_trans (VG.Proof.MlDsa.Sample.bStep_ge st j) (VG.Proof.MlDsa.Sample.bFold_ge _ L)
  | _, [] => Nat.le_refl _

/-- Coefficient `k` after setting coefficient `i`. -/
theorem ipoly_set!_get (c : IPoly) {k : Nat} (i : Nat) (hk : k < VG.Spec.MlDsa.n) (x : Int) :
    (c.set! i x)[k]! = if i = k then x else c[k]! := by
  rw [getElem!_pos _ k hk, getElem!_pos _ k hk, Vector.getElem_set!]

end VG.Proof.MlDsa.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.RejBounded`. -/
section

/-!
# ML-DSA: `RejBoundedPoly` a byte at a time

An implementation that runs the loop of `RejBoundedPoly` (Algorithm 31) over a
fixed number of bytes of XOF output, doing nothing once it has 256
coefficients, samples `rbFold η [] out` (`rbStep` is one iteration, `hbTry` a
half-byte), as elements of `ℤ_q`. It computes `RejBoundedPoly` if that has 256
coefficients (`rejBounded_some`), and otherwise so does no shorter output
(`rejBounded_none`).

How many coefficients it has sampled depends only on which half-bytes it
accepted (`rbFold_length_congr`), which is what the contract lets it leak
(`rejBoundedLeak`, `leak_hbOks`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- The half-byte `b`, tried: its coefficient appended if it is accepted. -/
def hbTry (η : Nat) (a : List VG.Spec.MlDsa.Zq) (b : Nat) : List VG.Spec.MlDsa.Zq :=
  match coeffFromHalfByte η b with
  | some c => a ++ [ofInt c]
  | none => a

/-- One iteration of the loop of `RejBoundedPoly` (lines 5–15 of
Algorithm 31), which does nothing once there are 256 coefficients. -/
def rbStep (η : Nat) (a : List VG.Spec.MlDsa.Zq) (z : Byte) : List VG.Spec.MlDsa.Zq :=
  if a.length < VG.Spec.MlDsa.n then
    (if (VG.Proof.MlDsa.Sample.hbTry η a (z.toNat % 16)).length < VG.Spec.MlDsa.n then VG.Proof.MlDsa.Sample.hbTry η (VG.Proof.MlDsa.Sample.hbTry η a (z.toNat % 16)) (z.toNat / 16)
      else VG.Proof.MlDsa.Sample.hbTry η a (z.toNat % 16))
  else a

/-- The coefficients after the loop over the bytes of `L`. -/
def rbFold (η : Nat) : List VG.Spec.MlDsa.Zq → List Byte → List VG.Spec.MlDsa.Zq
  | a, z :: L => VG.Proof.MlDsa.Sample.rbFold η (VG.Proof.MlDsa.Sample.rbStep η a z) L
  | a, [] => a

theorem hbTry_length (η : Nat) (a : List VG.Spec.MlDsa.Zq) (b : Nat) :
    (VG.Proof.MlDsa.Sample.hbTry η a b).length = a.length + halfByteOk η b := by
  unfold VG.Proof.MlDsa.Sample.hbTry halfByteOk
  split <;> rename_i h <;> simp [h]

theorem halfByteOk_le (η b : Nat) : halfByteOk η b ≤ 1 := by
  unfold halfByteOk; split <;> omega

theorem rbStep_length (η : Nat) (a : List VG.Spec.MlDsa.Zq) (z : Byte) :
    (VG.Proof.MlDsa.Sample.rbStep η a z).length =
      if a.length < VG.Spec.MlDsa.n then
        (if a.length + halfByteOk η (z.toNat % 16) < VG.Spec.MlDsa.n then
          a.length + halfByteOk η (z.toNat % 16) + halfByteOk η (z.toNat / 16)
        else a.length + halfByteOk η (z.toNat % 16))
      else a.length := by
  unfold VG.Proof.MlDsa.Sample.rbStep
  simp only [VG.Proof.MlDsa.Sample.hbTry_length]
  split
  · split <;> simp only [VG.Proof.MlDsa.Sample.hbTry_length]
  · rfl

theorem rbStep_length_le {η : Nat} {a : List VG.Spec.MlDsa.Zq} (ha : a.length ≤ VG.Spec.MlDsa.n) (z : Byte) : (VG.Proof.MlDsa.Sample.rbStep η a z).length ≤ VG.Spec.MlDsa.n := by
  rw [VG.Proof.MlDsa.Sample.rbStep_length]
  have := VG.Proof.MlDsa.Sample.halfByteOk_le η (z.toNat % 16)
  have := VG.Proof.MlDsa.Sample.halfByteOk_le η (z.toNat / 16)
  split
  · split <;> omega
  · exact ha

theorem rbStep_full {η : Nat} {a : List VG.Spec.MlDsa.Zq} (ha : a.length = VG.Spec.MlDsa.n) (z : Byte) : VG.Proof.MlDsa.Sample.rbStep η a z = a := by
  unfold VG.Proof.MlDsa.Sample.rbStep; rw [VG.Proof.MlDsa.Sample.ifF (by omega)]

theorem rbFold_full {η : Nat} {a : List VG.Spec.MlDsa.Zq} (ha : a.length = VG.Spec.MlDsa.n) : ∀ L, VG.Proof.MlDsa.Sample.rbFold η a L = a
  | z :: L => by rw [VG.Proof.MlDsa.Sample.rbFold, VG.Proof.MlDsa.Sample.rbStep_full ha, VG.Proof.MlDsa.Sample.rbFold_full ha L]
  | [] => rfl

theorem rbFold_length_le {η : Nat} {a : List VG.Spec.MlDsa.Zq} (ha : a.length ≤ VG.Spec.MlDsa.n) : ∀ L, (VG.Proof.MlDsa.Sample.rbFold η a L).length ≤ VG.Spec.MlDsa.n
  | z :: L => by rw [VG.Proof.MlDsa.Sample.rbFold]; exact VG.Proof.MlDsa.Sample.rbFold_length_le (VG.Proof.MlDsa.Sample.rbStep_length_le ha z) L
  | [] => ha

theorem rbFold_append (η : Nat) (a : List VG.Spec.MlDsa.Zq) : ∀ L₁ L₂ : List Byte,
    VG.Proof.MlDsa.Sample.rbFold η a (L₁ ++ L₂) = VG.Proof.MlDsa.Sample.rbFold η (VG.Proof.MlDsa.Sample.rbFold η a L₁) L₂
  | [], _ => rfl
  | z :: L₁, L₂ => by simp only [List.cons_append, VG.Proof.MlDsa.Sample.rbFold]; exact VG.Proof.MlDsa.Sample.rbFold_append η _ L₁ L₂

theorem rbFold_snoc (η : Nat) (a : List VG.Spec.MlDsa.Zq) (L : List Byte) (z : Byte) :
    VG.Proof.MlDsa.Sample.rbFold η a (L ++ [z]) = VG.Proof.MlDsa.Sample.rbStep η (VG.Proof.MlDsa.Sample.rbFold η a L) z := by
  rw [VG.Proof.MlDsa.Sample.rbFold_append]; rfl

/-! ## The loop of the standard -/

/-- The half-byte `b`, tried as the standard does, on integers. -/
def hbTryI (η : Nat) (a : List Int) (b : Nat) : List Int :=
  match coeffFromHalfByte η b with
  | some c => a ++ [c]
  | none => a

theorem hbTryI_map (η : Nat) (a : List Int) (b : Nat) :
    (VG.Proof.MlDsa.Sample.hbTryI η a b).map ofInt = VG.Proof.MlDsa.Sample.hbTry η (a.map ofInt) b := by
  unfold VG.Proof.MlDsa.Sample.hbTryI VG.Proof.MlDsa.Sample.hbTry; split <;> simp

theorem rejBoundedLoop_step (η : Nat) {a : List Int} (ha : a.length < VG.Spec.MlDsa.n) (z : Byte) (L : List Byte) :
    rejBoundedLoop η a (z :: L) =
      rejBoundedLoop η (if (VG.Proof.MlDsa.Sample.hbTryI η a (z.toNat % 16)).length < VG.Spec.MlDsa.n then
        VG.Proof.MlDsa.Sample.hbTryI η (VG.Proof.MlDsa.Sample.hbTryI η a (z.toNat % 16)) (z.toNat / 16) else VG.Proof.MlDsa.Sample.hbTryI η a (z.toNat % 16)) L := by
  rw [rejBoundedLoop, VG.Proof.MlDsa.Sample.ifF (by omega)]
  dsimp only
  congr 1
  unfold VG.Proof.MlDsa.Sample.hbTryI
  cases coeffFromHalfByte η (z.toNat / 16) with
  | none => exact (ite_self _).symm
  | some c => rfl

/-- The loop, as `rbFold` on the coefficients as elements of `ℤ_q`: it
succeeds when that has 256 coefficients. -/
theorem rejBoundedLoop_map (η : Nat) {a : List Int} (ha : a.length ≤ VG.Spec.MlDsa.n) :
    ∀ L, (rejBoundedLoop η a L).map (·.map ofInt) =
      if (VG.Proof.MlDsa.Sample.rbFold η (a.map ofInt) L).length = VG.Spec.MlDsa.n then some (VG.Proof.MlDsa.Sample.rbFold η (a.map ofInt) L) else none
  | z :: L => by
    by_cases h : a.length ≥ VG.Spec.MlDsa.n
    · rw [rejBoundedLoop, VG.Proof.MlDsa.Sample.ifT h, VG.Proof.MlDsa.Sample.rbFold, VG.Proof.MlDsa.Sample.rbStep_full (by simp; omega), VG.Proof.MlDsa.Sample.rbFold_full (by simp; omega),
        VG.Proof.MlDsa.Sample.ifT (by simp; omega)]
      rfl
    · rw [VG.Proof.MlDsa.Sample.rejBoundedLoop_step η (by omega)]
      have e1 := VG.Proof.MlDsa.Sample.hbTryI_map η a (z.toNat % 16)
      have l1 : (VG.Proof.MlDsa.Sample.hbTryI η a (z.toNat % 16)).length = (VG.Proof.MlDsa.Sample.hbTry η (a.map ofInt) (z.toNat % 16)).length := by
        rw [← e1, List.length_map]
      have l1' : (VG.Proof.MlDsa.Sample.hbTryI η a (z.toNat % 16)).length ≤ VG.Spec.MlDsa.n := by
        rw [l1, VG.Proof.MlDsa.Sample.hbTry_length, List.length_map]; have := VG.Proof.MlDsa.Sample.halfByteOk_le η (z.toNat % 16); omega
      have e2 : (if (VG.Proof.MlDsa.Sample.hbTryI η a (z.toNat % 16)).length < VG.Spec.MlDsa.n then
            VG.Proof.MlDsa.Sample.hbTryI η (VG.Proof.MlDsa.Sample.hbTryI η a (z.toNat % 16)) (z.toNat / 16) else VG.Proof.MlDsa.Sample.hbTryI η a (z.toNat % 16)).map ofInt =
          VG.Proof.MlDsa.Sample.rbStep η (a.map ofInt) z := by
        have hlen : (List.map ofInt a).length < VG.Spec.MlDsa.n := by rw [List.length_map]; omega
        by_cases hl : (VG.Proof.MlDsa.Sample.hbTryI η a (z.toNat % 16)).length < VG.Spec.MlDsa.n
        · have hl' : (VG.Proof.MlDsa.Sample.hbTry η (a.map ofInt) (z.toNat % 16)).length < VG.Spec.MlDsa.n := by rw [← l1]; exact hl
          rw [VG.Proof.MlDsa.Sample.ifT hl, VG.Proof.MlDsa.Sample.rbStep, VG.Proof.MlDsa.Sample.ifT hlen, VG.Proof.MlDsa.Sample.ifT hl', VG.Proof.MlDsa.Sample.hbTryI_map, e1]
        · have hl' : ¬ (VG.Proof.MlDsa.Sample.hbTry η (a.map ofInt) (z.toNat % 16)).length < VG.Spec.MlDsa.n := by rw [← l1]; exact hl
          rw [VG.Proof.MlDsa.Sample.ifF hl, VG.Proof.MlDsa.Sample.rbStep, VG.Proof.MlDsa.Sample.ifT hlen, VG.Proof.MlDsa.Sample.ifF hl', e1]
      have l2 : (if (VG.Proof.MlDsa.Sample.hbTryI η a (z.toNat % 16)).length < VG.Spec.MlDsa.n then
            VG.Proof.MlDsa.Sample.hbTryI η (VG.Proof.MlDsa.Sample.hbTryI η a (z.toNat % 16)) (z.toNat / 16) else VG.Proof.MlDsa.Sample.hbTryI η a (z.toNat % 16)).length ≤ VG.Spec.MlDsa.n := by
        have := congrArg List.length e2
        rw [List.length_map] at this
        rw [this]; exact VG.Proof.MlDsa.Sample.rbStep_length_le (by simp; omega) z
      rw [VG.Proof.MlDsa.Sample.rejBoundedLoop_map η l2 L, e2]
      rfl
  | [] => by
    show Option.map _ (if a.length ≥ VG.Spec.MlDsa.n then some a else none) = _
    rw [VG.Proof.MlDsa.Sample.rbFold, List.length_map]
    by_cases h : a.length = VG.Spec.MlDsa.n
    · rw [VG.Proof.MlDsa.Sample.ifT (by omega), VG.Proof.MlDsa.Sample.ifT h]; rfl
    · rw [VG.Proof.MlDsa.Sample.ifF (by omega), VG.Proof.MlDsa.Sample.ifF h]; rfl

/-- `RejBoundedPoly(ρ)` as a polynomial of `R_q`, when the loop over the
`B` bytes of output samples 256 coefficients. -/
theorem rejBounded_some (η : Nat) {ρ : List Byte} {B : Nat} (h : (VG.Proof.MlDsa.Sample.rbFold η [] (VG.Spec.MlDsa.H ρ B)).length = 256) :
    (rejBoundedPoly η B ρ).map toRq = some (VG.Proof.MlDsa.Sample.toPoly (VG.Proof.MlDsa.Sample.rbFold η [] (VG.Spec.MlDsa.H ρ B))) := by
  have e := VG.Proof.MlDsa.Sample.rejBoundedLoop_map η (a := []) (by simp) (VG.Spec.MlDsa.H ρ B)
  simp only [List.map_nil] at e
  rw [VG.Proof.MlDsa.Sample.ifT h] at e
  simp only [rejBoundedPoly, Option.map_map]
  cases hl : rejBoundedLoop η [] (VG.Spec.MlDsa.H ρ B) with
  | none => rw [hl] at e; cases e
  | some a =>
    rw [hl] at e
    simp only [Option.map_some, Option.some.injEq] at e
    simp only [Option.map_some, Function.comp, Option.some.injEq]
    apply Vector.ext
    intro i hi
    simp only [toRq, Vector.getElem_map, Vector.getElem_ofFn, ← e, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases a[i]? <;> rfl

/-- If the loop over `B` bytes of output does not sample 256 coefficients,
neither does it over the first `B'` bytes. -/
theorem rejBounded_none (η : Nat) {ρ : List Byte} {B B' : Nat} (hB : B' ≤ B)
    (h : (VG.Proof.MlDsa.Sample.rbFold η [] (VG.Spec.MlDsa.H ρ B)).length ≠ 256) : rejBoundedPoly η B' ρ = none := by
  have e : VG.Spec.MlDsa.H ρ B = VG.Spec.MlDsa.H ρ B' ++ (VG.Spec.MlDsa.H ρ B).drop B' := by rw [← VG.Proof.MlDsa.Sample.H_take ρ hB, List.take_append_drop]
  rw [e, VG.Proof.MlDsa.Sample.rbFold_append] at h
  have e' := VG.Proof.MlDsa.Sample.rejBoundedLoop_map η (a := []) (by simp) (VG.Spec.MlDsa.H ρ B')
  simp only [List.map_nil] at e'
  by_cases hf : (VG.Proof.MlDsa.Sample.rbFold η [] (VG.Spec.MlDsa.H ρ B')).length = VG.Spec.MlDsa.n
  · exact absurd (by rw [VG.Proof.MlDsa.Sample.rbFold_full hf]; exact hf) h
  · rw [VG.Proof.MlDsa.Sample.ifF hf] at e'
    rw [rejBoundedPoly]
    cases hl : rejBoundedLoop η [] (VG.Spec.MlDsa.H ρ B') with
    | none => rfl
    | some a => rw [hl] at e'; cases e'

/-! ## What the lengths depend on -/

/-- Whether the loop accepts the half-bytes of the byte `z`. -/
def hbOks (η : Nat) (z : Byte) : Nat × Nat := (halfByteOk η (z.toNat % 16), halfByteOk η (z.toNat / 16))

theorem rbStep_length_congr {η : Nat} {a₁ a₂ : List VG.Spec.MlDsa.Zq} (ha : a₁.length = a₂.length) {z₁ z₂ : Byte}
    (hz : VG.Proof.MlDsa.Sample.hbOks η z₁ = VG.Proof.MlDsa.Sample.hbOks η z₂) : (VG.Proof.MlDsa.Sample.rbStep η a₁ z₁).length = (VG.Proof.MlDsa.Sample.rbStep η a₂ z₂).length := by
  simp only [VG.Proof.MlDsa.Sample.hbOks, Prod.mk.injEq] at hz
  rw [VG.Proof.MlDsa.Sample.rbStep_length, VG.Proof.MlDsa.Sample.rbStep_length, ha, hz.1, hz.2]

/-- The number of coefficients sampled from bytes accepted alike. -/
theorem rbFold_length_congr {η : Nat} : ∀ {a₁ a₂ : List VG.Spec.MlDsa.Zq} {L₁ L₂ : List Byte}, a₁.length = a₂.length →
    List.map (VG.Proof.MlDsa.Sample.hbOks η) L₁ = List.map (VG.Proof.MlDsa.Sample.hbOks η) L₂ → (VG.Proof.MlDsa.Sample.rbFold η a₁ L₁).length = (VG.Proof.MlDsa.Sample.rbFold η a₂ L₂).length
  | _, _, [], [], ha, _ => ha
  | _, _, z₁ :: L₁, z₂ :: L₂, ha, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [VG.Proof.MlDsa.Sample.rbFold, VG.Proof.MlDsa.Sample.rbFold]
    exact VG.Proof.MlDsa.Sample.rbFold_length_congr (VG.Proof.MlDsa.Sample.rbStep_length_congr ha h.1) h.2
  | _, _, [], _ :: _, _, h | _, _, _ :: _, [], _, h => by simp at h

/-- The leak, byte by byte. -/
theorem leak_eq (η : Nat) (L : List Byte) :
    L.flatMap (fun z => [halfByteOk η (z.toNat % 16), halfByteOk η (z.toNat / 16)]) =
      (L.map (VG.Proof.MlDsa.Sample.hbOks η)).flatMap fun p => [p.1, p.2] := by
  simp [List.flatMap_map, VG.Proof.MlDsa.Sample.hbOks]

theorem flatMap_pair_inj : ∀ {A B : List (Nat × Nat)},
    A.flatMap (fun p => [p.1, p.2]) = B.flatMap (fun p => [p.1, p.2]) → A = B
  | [], [], _ => rfl
  | a :: A, b :: B, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
    rw [Prod.ext h.1 h.2.1, VG.Proof.MlDsa.Sample.flatMap_pair_inj h.2.2]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- Two seeds with the same leak: their outputs' first `B` bytes (`B` at most
the bytes the leak covers) are accepted alike. -/
theorem leak_hbOks {η : Nat} {ρ₁ ρ₂ : List Byte} (h : rejBoundedLeak η ρ₁ = rejBoundedLeak η ρ₂) {B : Nat}
    (hB : B ≤ maxBounds.rejBounded) : (VG.Spec.MlDsa.H ρ₁ B).map (VG.Proof.MlDsa.Sample.hbOks η) = (VG.Spec.MlDsa.H ρ₂ B).map (VG.Proof.MlDsa.Sample.hbOks η) := by
  simp only [rejBoundedLeak, VG.Proof.MlDsa.Sample.leak_eq] at h
  have := congrArg (List.take B) (VG.Proof.MlDsa.Sample.flatMap_pair_inj h)
  rwa [← List.map_take, ← List.map_take, VG.Proof.MlDsa.Sample.H_take _ hB, VG.Proof.MlDsa.Sample.H_take _ hB] at this

end VG.Proof.MlDsa.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.HalfByte`. -/
section

/-!
# ML-DSA: `CoeffFromHalfByte` as a bound and a formula, for every target

For `η = 2` or `4`, `CoeffFromHalfByte` accepts the half-bytes less than `rbB
η` and gives `rbC η b` for them (`coeffFromHalfByte_eq`), so a try appends
that coefficient exactly when the half-byte is less than the bound
(`hbTry_eq`), and whether it does is `halfByteOk` (`halfByteOk_eq`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def rbB (η : Nat) : Nat := if η = 2 then 15 else 9

/-- The coefficient of an accepted half-byte. -/
def rbC (η b : Nat) : Int := if η = 2 then 2 - (b % 5 : Nat) else 4 - b

theorem coeffFromHalfByte_eq {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    coeffFromHalfByte η b = if b < VG.Proof.MlDsa.Sample.rbB η then some (VG.Proof.MlDsa.Sample.rbC η b) else none := by
  rcases hη with rfl | rfl <;> simp [coeffFromHalfByte, VG.Proof.MlDsa.Sample.rbB, VG.Proof.MlDsa.Sample.rbC]

theorem hbTry_eq {η : Nat} (hη : η = 2 ∨ η = 4) (L : List VG.Spec.MlDsa.Zq) (b : Nat) :
    VG.Proof.MlDsa.Sample.hbTry η L b = if b < VG.Proof.MlDsa.Sample.rbB η then L ++ [ofInt (VG.Proof.MlDsa.Sample.rbC η b)] else L := by
  unfold VG.Proof.MlDsa.Sample.hbTry
  rw [VG.Proof.MlDsa.Sample.coeffFromHalfByte_eq hη]
  by_cases h : b < VG.Proof.MlDsa.Sample.rbB η <;> simp [h]

theorem halfByteOk_eq {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    halfByteOk η b = if b < VG.Proof.MlDsa.Sample.rbB η then 1 else 0 := by
  unfold halfByteOk
  rw [VG.Proof.MlDsa.Sample.coeffFromHalfByte_eq hη]
  by_cases h : b < VG.Proof.MlDsa.Sample.rbB η <;> simp [h]

end VG.Proof.MlDsa.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.HalfByteVal`. -/
section

/-!
# ML-DSA: the coefficient of a half-byte, without a branch

An implementation can compute the coefficient `rbC η b` of an accepted
half-byte (`HalfByte.lean`) modulo `q` without a branch or a table (`hbVal`):
`b mod 5` by subtracting 10 and then 5 where they are no greater (`csubV`, a
subtraction plus the subtrahend masked by its borrow), and `(η - b') mod q` as
`η - b'` plus `q` masked by the borrow (`etaV`); `hbVal_eq` checks it on the
accepted half-bytes by evaluation.
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- `x - s` if `s ≤ x`: `x - s` plus `s` masked by the borrow. -/
def csubV (s x : BitVec 32) : BitVec 32 :=
  x - s + (0#32 - (BitVec.ofBool (decide (x.toNat < s.toNat))).setWidth 32 &&& s)

/-- `(η - x) mod q`: `η - x` plus `q` masked by the borrow. -/
def etaV (η x : BitVec 32) : BitVec 32 :=
  η - x + (0#32 - (BitVec.ofBool (decide (η.toNat < x.toNat))).setWidth 32 &&& 8380417#32)

/-- The coefficient of the half-byte `x`, modulo `q`, computed without a
branch: `η - (x mod 5)` for `η = 2`, `η - x` for `η = 4`. -/
def hbVal : Nat → BitVec 32 → BitVec 32
  | 2, x => VG.Proof.MlDsa.Sample.etaV 2 (VG.Proof.MlDsa.Sample.csubV 5 (VG.Proof.MlDsa.Sample.csubV 10 x))
  | _, x => VG.Proof.MlDsa.Sample.etaV 4 x

theorem hbVal_eq2 : ∀ b < 15, VG.Proof.MlDsa.Sample.hbVal 2 (BitVec.ofNat 32 b) = VG.Proof.MlDsa.Sample.zw (ofInt (VG.Proof.MlDsa.Sample.rbC 2 b)) := by decide

theorem hbVal_eq4 : ∀ b < 9, VG.Proof.MlDsa.Sample.hbVal 4 (BitVec.ofNat 32 b) = VG.Proof.MlDsa.Sample.zw (ofInt (VG.Proof.MlDsa.Sample.rbC 4 b)) := by decide

theorem hbVal_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b : Nat} (hb : b < VG.Proof.MlDsa.Sample.rbB η) :
    VG.Proof.MlDsa.Sample.hbVal η (BitVec.ofNat 32 b) = VG.Proof.MlDsa.Sample.zw (ofInt (VG.Proof.MlDsa.Sample.rbC η b)) := by
  rcases hη with rfl | rfl
  · exact VG.Proof.MlDsa.Sample.hbVal_eq2 b hb
  · exact VG.Proof.MlDsa.Sample.hbVal_eq4 b hb

end VG.Proof.MlDsa.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.LeNat`. -/
section

/-!
# ML-DSA: the fields of a group of bytes, for every target

The `c`-bit fields of a byte string `L` (`leNat L / 2^(ic) mod 2^c`) as an
implementation reads them a group at a time: from byte `o` on, the string is
`leNat (L.drop o)` (`leNat_drop`); the fields in its first 8 bytes are those
of the `u64` of them (`field_low`); and a field that straddles the 8th byte is
the top bits of the `u64` plus the next bytes above them
(`leNat_take_succ`, `split_div`).
-/

namespace VG.Proof.MlDsa.Sample

theorem leNat_lt : ∀ L : List Byte, VG.Proof.MlDsa.Sample.leNat L < 2 ^ (8 * L.length)
  | [] => by simp [VG.Proof.MlDsa.Sample.leNat]
  | c :: L => by
    have := VG.Proof.MlDsa.Sample.leNat_lt L
    have := c.isLt
    rw [VG.Proof.MlDsa.Sample.leNat, List.length_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (8 * L.length))]
    have : c.toNat + 2 ^ 8 * VG.Proof.MlDsa.Sample.leNat L ≤ 2 ^ 8 - 1 + 2 ^ 8 * (2 ^ (8 * L.length) - 1) := by
      have := Nat.mul_le_mul_left (2 ^ 8) (Nat.le_sub_one_of_lt (VG.Proof.MlDsa.Sample.leNat_lt L))
      omega
    have h1 : 1 ≤ 2 ^ (8 * L.length) := Nat.one_le_two_pow
    rw [Nat.mul_sub_one] at this
    omega

/-- The string from byte `k` on. -/
theorem leNat_drop : ∀ (L : List Byte) (k : Nat), VG.Proof.MlDsa.Sample.leNat L / 2 ^ (8 * k) = VG.Proof.MlDsa.Sample.leNat (L.drop k)
  | L, 0 => by simp
  | [], k + 1 => by simp [VG.Proof.MlDsa.Sample.leNat]
  | c :: L, k + 1 => by
    rw [List.drop_succ_cons, ← VG.Proof.MlDsa.Sample.leNat_drop L k, VG.Proof.MlDsa.Sample.leNat, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (8 * k)),
      ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt c.isLt, Nat.zero_add]

/-- A field in the first 8 bytes. -/
theorem field_low (D : List Byte) {P c : Nat} (h : P + c ≤ 64) :
    VG.Proof.MlDsa.Sample.leNat (D.take 8) / 2 ^ P % 2 ^ c = VG.Proof.MlDsa.Sample.leNat D / 2 ^ P % 2 ^ c := VG.Proof.MlDsa.Sample.leNat_take_bits D (by omega)

/-- The first `k + 1` bytes: the first `k`, and byte `k` above them. -/
theorem leNat_take_succ (D : List Byte) {k : Nat} (hk : k < D.length) :
    VG.Proof.MlDsa.Sample.leNat (D.take (k + 1)) = VG.Proof.MlDsa.Sample.leNat (D.take k) + 2 ^ (8 * k) * (D.getD k 0).toNat := by
  induction D generalizing k with
  | nil => simp at hk
  | cons c D ih =>
    cases k with
    | zero => simp [VG.Proof.MlDsa.Sample.leNat]
    | succ k =>
      rw [List.take_succ_cons, List.take_succ_cons, VG.Proof.MlDsa.Sample.leNat, VG.Proof.MlDsa.Sample.leNat, ih (by simp at hk; omega), List.getD_cons_succ,
        Nat.mul_succ, Nat.pow_add, Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm (2 ^ 8), Nat.mul_assoc,
        Nat.mul_comm (2 ^ 8) (D.getD k 0).toNat]

/-- Dividing a number of two parts by a power of two below the split. -/
theorem split_div (A B : Nat) {P M : Nat} (hP : P ≤ M) : (A + 2 ^ M * B) / 2 ^ P = A / 2 ^ P + 2 ^ (M - P) * B := by
  rw [show 2 ^ M = 2 ^ P * 2 ^ (M - P) by rw [← Nat.pow_add]; congr 1; omega, Nat.mul_assoc,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos P)]

end VG.Proof.MlDsa.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.LeWord`. -/
section

/-!
# ML-DSA: little-endian words in memory, for every target

The `u64` a target loads from 8 bytes of memory is the little-endian integer
of those bytes (`readW_leNat`), bit by bit (`readW64_getLsbD`).
-/

namespace VG.Proof.MlDsa.Sample

theorem readW64_getLsbD (m : Mem) (a : Addr) {k : Nat} (hk : k < 64) :
    (m.readW a 64).getLsbD k = (m (a + BitVec.ofNat 64 (k / 8))).getLsbD (k % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 8) (j := k / 8) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, show k % 8 < 8 by omega, decide_true, Bool.true_and, hk]
  congr 1; omega

/-- The `u64` at `p`, from the bytes there. -/
theorem readW_leNat (m : Mem) (p : Addr) (L : List Byte) (h : ∀ k < 8, m (p + BitVec.ofNat 64 k) = L.getD k 0) :
    m.readW p 64 = BitVec.ofNat 64 (VG.Proof.MlDsa.Sample.leNat (L.take 8)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [VG.Proof.MlDsa.Sample.readW64_getLsbD m p hk, h _ (by omega), BitVec.getLsbD_ofNat, VG.Proof.MlDsa.Sample.testBit_leNat, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  simp [hk]

end VG.Proof.MlDsa.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.RejNtt`. -/
section

/-!
# ML-DSA: `RejNTTPoly` three bytes at a time

An implementation that runs the loop of `RejNTTPoly` (Algorithm 30) over a
fixed number of 3-byte arrays of XOF output, doing nothing once it has 256
coefficients, samples `rnFold [] out` (`rnStep` is one iteration). It computes
`RejNTTPoly` if that has 256 coefficients (`rejNTTLoop_eq`), and otherwise so
does no shorter output, the least bound of Appendix C included
(`rejNTT_none`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- The value of the 3 bytes `b₀, b₁, b₂` (Algorithm 14, line 2 and 3). -/
def rnZ (b₀ b₁ b₂ : Byte) : Nat := b₀.toNat + 256 * b₁.toNat + 65536 * (b₂.toNat % 128)

/-- One iteration of the loop of `RejNTTPoly` (lines 5–9 of Algorithm 30),
which does nothing once there are 256 coefficients. -/
def rnStep (a : List VG.Spec.MlDsa.Zq) (b₀ b₁ b₂ : Byte) : List VG.Spec.MlDsa.Zq :=
  if a.length < VG.Spec.MlDsa.n then (if VG.Proof.MlDsa.Sample.rnZ b₀ b₁ b₂ < VG.Spec.MlDsa.q then a ++ [Fin.ofNat VG.Spec.MlDsa.q (VG.Proof.MlDsa.Sample.rnZ b₀ b₁ b₂)] else a) else a

/-- The coefficients after the loop over the whole 3-byte arrays of `L`. -/
def rnFold : List VG.Spec.MlDsa.Zq → List Byte → List VG.Spec.MlDsa.Zq
  | a, b₀ :: b₁ :: b₂ :: L => VG.Proof.MlDsa.Sample.rnFold (VG.Proof.MlDsa.Sample.rnStep a b₀ b₁ b₂) L
  | a, _ => a

theorem coeffFromThreeBytes_eq (b₀ b₁ b₂ : Byte) :
    coeffFromThreeBytes b₀ b₁ b₂ =
      if VG.Proof.MlDsa.Sample.rnZ b₀ b₁ b₂ < VG.Spec.MlDsa.q then some (Fin.ofNat VG.Spec.MlDsa.q (VG.Proof.MlDsa.Sample.rnZ b₀ b₁ b₂)) else none := by
  have e : (2 ^ 16 * (if b₂.toNat > 127 then b₂.toNat - 128 else b₂.toNat) + 2 ^ 8 * b₁.toNat + b₀.toNat) =
      VG.Proof.MlDsa.Sample.rnZ b₀ b₁ b₂ := by
    have := b₂.isLt
    unfold VG.Proof.MlDsa.Sample.rnZ; split <;> omega
  simp only [coeffFromThreeBytes, e]
  split
  · rename_i h; exact congrArg some (Fin.ext (Nat.mod_eq_of_lt h).symm)
  · rfl

theorem rnStep_length_le {a : List VG.Spec.MlDsa.Zq} (ha : a.length ≤ VG.Spec.MlDsa.n) (b₀ b₁ b₂ : Byte) : (VG.Proof.MlDsa.Sample.rnStep a b₀ b₁ b₂).length ≤ VG.Spec.MlDsa.n := by
  unfold VG.Proof.MlDsa.Sample.rnStep; split
  · split <;> (try simp only [List.length_append, List.length_singleton]) <;> omega
  · exact ha

theorem rnStep_full {a : List VG.Spec.MlDsa.Zq} (ha : a.length = VG.Spec.MlDsa.n) (b₀ b₁ b₂ : Byte) : VG.Proof.MlDsa.Sample.rnStep a b₀ b₁ b₂ = a := by
  unfold VG.Proof.MlDsa.Sample.rnStep; rw [VG.Proof.MlDsa.Sample.ifF (by omega)]

theorem rnFold_full {a : List VG.Spec.MlDsa.Zq} (ha : a.length = VG.Spec.MlDsa.n) : ∀ L, VG.Proof.MlDsa.Sample.rnFold a L = a
  | _ :: _ :: _ :: L => by rw [VG.Proof.MlDsa.Sample.rnFold, VG.Proof.MlDsa.Sample.rnStep_full ha, VG.Proof.MlDsa.Sample.rnFold_full ha L]
  | [] | [_] | [_, _] => rfl

theorem rnFold_length_le {a : List VG.Spec.MlDsa.Zq} (ha : a.length ≤ VG.Spec.MlDsa.n) : ∀ L, (VG.Proof.MlDsa.Sample.rnFold a L).length ≤ VG.Spec.MlDsa.n
  | _ :: _ :: _ :: L => by rw [VG.Proof.MlDsa.Sample.rnFold]; exact VG.Proof.MlDsa.Sample.rnFold_length_le (VG.Proof.MlDsa.Sample.rnStep_length_le ha _ _ _) L
  | [] | [_] | [_, _] => ha

/-- The loop, as `rnFold`: it succeeds when that has 256 coefficients. -/
theorem rejNTTLoop_eq {a : List VG.Spec.MlDsa.Zq} (ha : a.length ≤ VG.Spec.MlDsa.n) :
    ∀ L, rejNTTLoop a L = if (VG.Proof.MlDsa.Sample.rnFold a L).length = VG.Spec.MlDsa.n then some (VG.Proof.MlDsa.Sample.rnFold a L) else none
  | b₀ :: b₁ :: b₂ :: L => by
    rw [rejNTTLoop, VG.Proof.MlDsa.Sample.rnFold]
    by_cases h : a.length ≥ VG.Spec.MlDsa.n
    · rw [VG.Proof.MlDsa.Sample.ifT h, VG.Proof.MlDsa.Sample.rnStep_full (by omega), VG.Proof.MlDsa.Sample.rnFold_full (by omega), VG.Proof.MlDsa.Sample.ifT (by omega)]
    · rw [VG.Proof.MlDsa.Sample.ifF h, ← VG.Proof.MlDsa.Sample.rejNTTLoop_eq (VG.Proof.MlDsa.Sample.rnStep_length_le ha _ _ _) L, VG.Proof.MlDsa.Sample.rnStep, VG.Proof.MlDsa.Sample.ifT (by omega),
        VG.Proof.MlDsa.Sample.coeffFromThreeBytes_eq]
      by_cases hz : VG.Proof.MlDsa.Sample.rnZ b₀ b₁ b₂ < VG.Spec.MlDsa.q <;> simp only [hz, ↓reduceIte]
  | [] | [_] | [_, _] => by
    show (if a.length ≥ VG.Spec.MlDsa.n then some a else none) = if a.length = VG.Spec.MlDsa.n then some a else none
    by_cases h : a.length = VG.Spec.MlDsa.n
    · rw [VG.Proof.MlDsa.Sample.ifT (by omega), VG.Proof.MlDsa.Sample.ifT h]
    · rw [VG.Proof.MlDsa.Sample.ifF (by omega), VG.Proof.MlDsa.Sample.ifF h]

/-- The loop over `L₁` then `L₂`, for `L₁` a whole number of 3-byte arrays. -/
theorem rnFold_append (a : List VG.Spec.MlDsa.Zq) : ∀ (L₁ L₂ : List Byte), L₁.length % 3 = 0 →
    VG.Proof.MlDsa.Sample.rnFold a (L₁ ++ L₂) = VG.Proof.MlDsa.Sample.rnFold (VG.Proof.MlDsa.Sample.rnFold a L₁) L₂
  | [], _, _ => rfl
  | b₀ :: b₁ :: b₂ :: L₁, L₂, h => by
    simp only [List.cons_append, VG.Proof.MlDsa.Sample.rnFold]
    exact VG.Proof.MlDsa.Sample.rnFold_append _ L₁ L₂ (by simp only [List.length_cons] at h; omega)
  | [_], _, h | [_, _], _, h => by simp at h

/-- One more iteration, on the 3 bytes after `L`. -/
theorem rnFold_snoc (a : List VG.Spec.MlDsa.Zq) {L : List Byte} (h : L.length % 3 = 0) (b₀ b₁ b₂ : Byte) :
    VG.Proof.MlDsa.Sample.rnFold a (L ++ [b₀, b₁, b₂]) = VG.Proof.MlDsa.Sample.rnStep (VG.Proof.MlDsa.Sample.rnFold a L) b₀ b₁ b₂ := by
  rw [VG.Proof.MlDsa.Sample.rnFold_append a L _ h]; rfl

/-- `RejNTTPoly(ρ)` with a bound `B`, when the loop over the `B` bytes of
output samples 256 coefficients. -/
theorem rejNTT_some {ρ : List Byte} {B : Nat} (h : (VG.Proof.MlDsa.Sample.rnFold [] (VG.Spec.MlDsa.G ρ B)).length = 256) :
    rejNTTPoly B ρ = some (VG.Proof.MlDsa.Sample.toPoly (VG.Proof.MlDsa.Sample.rnFold [] (VG.Spec.MlDsa.G ρ B))) := by
  rw [rejNTTPoly, VG.Proof.MlDsa.Sample.rejNTTLoop_eq (by simp) _, VG.Proof.MlDsa.Sample.ifT h]
  rfl

/-- If the loop over `B` bytes of output does not sample 256 coefficients,
neither does it over the first `B'` bytes. -/
theorem rejNTT_none {ρ : List Byte} {B B' : Nat} (hB : B' ≤ B) (h3 : B' % 3 = 0)
    (h : (VG.Proof.MlDsa.Sample.rnFold [] (VG.Spec.MlDsa.G ρ B)).length ≠ 256) : rejNTTPoly B' ρ = none := by
  have e : VG.Spec.MlDsa.G ρ B = VG.Spec.MlDsa.G ρ B' ++ (VG.Spec.MlDsa.G ρ B).drop B' := by rw [← VG.Proof.MlDsa.Sample.G_take ρ hB, List.take_append_drop]
  rw [e, VG.Proof.MlDsa.Sample.rnFold_append _ _ _ (by rw [VG.Proof.MlDsa.Sample.G_length]; exact h3)] at h
  rw [rejNTTPoly, VG.Proof.MlDsa.Sample.rejNTTLoop_eq (by simp) _]
  by_cases hf : (VG.Proof.MlDsa.Sample.rnFold [] (VG.Spec.MlDsa.G ρ B')).length = VG.Spec.MlDsa.n
  · exact absurd (by rw [VG.Proof.MlDsa.Sample.rnFold_full hf]; exact hf) h
  · rw [VG.Proof.MlDsa.Sample.ifF hf]; rfl

end VG.Proof.MlDsa.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.Rej4`. -/
section

namespace VG.Proof.MlDsa.Sample
open VG
open VG.Spec.MlDsa (G)
open VG.Spec.Sha3 (bytesAt)
/-- The result of either implementation: whether each seed has 256 coefficients in its first 1008
bytes of output. -/
def rej4Res (m : Mem) (a : Addr) : BitVec 32 :=
  if (List.range 4).all (fun k => (VG.Proof.MlDsa.Sample.rnFold [] (G (Spec.MlDsa.seed4 m a k) 1008)).length == 256) then 1 else 0

theorem seed4_of136 {m m' : Mem} {a a' : Addr} (h : bytesAt m a 136 = bytesAt m' a' 136) {k : Nat} (hk : k < 4) :
    Spec.MlDsa.seed4 m a k = Spec.MlDsa.seed4 m' a' k := by
  unfold Spec.MlDsa.seed4
  rw [← Proof.MlKem.bytesAt_slice m a (show 34 * k + 34 ≤ 136 by omega),
    ← Proof.MlKem.bytesAt_slice m' a' (show 34 * k + 34 ≤ 136 by omega), h]

/-- The result depends only on the 136 bytes of the seeds. -/
theorem rej4Res_congr {m m' : Mem} {a a' : Addr} (h : bytesAt m a 136 = bytesAt m' a' 136) :
    VG.Proof.MlDsa.Sample.rej4Res m a = VG.Proof.MlDsa.Sample.rej4Res m' a' := by
  have e : ((List.range 4).all fun k => (VG.Proof.MlDsa.Sample.rnFold [] (G (Spec.MlDsa.seed4 m a k) 1008)).length == 256) =
      ((List.range 4).all fun k => (VG.Proof.MlDsa.Sample.rnFold [] (G (Spec.MlDsa.seed4 m' a' k) 1008)).length == 256) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact ⟨fun H k hk => by rw [← VG.Proof.MlDsa.Sample.seed4_of136 h (List.mem_range.mp hk)]; exact H k hk,
      fun H k hk => by rw [VG.Proof.MlDsa.Sample.seed4_of136 h (List.mem_range.mp hk)]; exact H k hk⟩
  simp only [VG.Proof.MlDsa.Sample.rej4Res, e]

/-- Within the bound both implementations sample to, so within `maxBounds`'s. -/
theorem rej4Res_max {m : Mem} {a : Addr} (h : VG.Proof.MlDsa.Sample.rej4Res m a = 1) {k : Nat} (hk : k < 4) {B : Nat} (hB : 1008 ≤ B) :
    (Spec.MlDsa.rejNTTPoly B (Spec.MlDsa.seed4 m a k)).isSome := by
  unfold VG.Proof.MlDsa.Sample.rej4Res at h
  by_cases hall : ((List.range 4).all fun k => (VG.Proof.MlDsa.Sample.rnFold [] (G (Spec.MlDsa.seed4 m a k) 1008)).length == 256) = true
  · have hs : (VG.Proof.MlDsa.Sample.rnFold [] (G (Spec.MlDsa.seed4 m a k) 1008)).length = 256 := by
      simpa using List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    rw [Proof.MlDsa.KeyGen.rejNTTPoly_mono hB (VG.Proof.MlDsa.Sample.rejNTT_some hs)]; rfl
  · rw [ite_eq_right hall] at h; exact absurd h (by decide)

end VG.Proof.MlDsa.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.Word`. -/
section

/-!
# ML-DSA: fields of a little-endian word, and subtraction modulo `q`

For implementations that read a field of `c` bits of a byte string `X` as the
32-bit little-endian word at its first byte, shifted right and masked: the
bits of the word from bit `sh` on are those of `leNat X` from bit `8o + sh`
on, if its first three bytes are those of `X` from byte `o` (`wordBits`). And
`(g - x) mod q`, computed as `g - x` in 32 bits plus `q` masked by the borrow
of the subtraction (`subMask_eq`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- `g - x` modulo `q`, for `x < q + g`: `g - x` in 32 bits, plus `q` masked
by the borrow (`sbb d, d` with `d = x` makes the mask). -/
theorem subMask_eq {g x : BitVec 32} (hg : g.toNat < VG.Spec.MlDsa.q) (hx : x.toNat < VG.Spec.MlDsa.q + g.toNat) :
    g - x + ((x - x - (BitVec.ofBool (decide (g.toNat < x.toNat))).setWidth 32) &&& 8380417#32) =
      VG.Proof.MlDsa.Sample.zw (ofInt ((g.toNat : Int) - x.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.MlDsa.Sample.zw_toNat]
  simp only [ofInt, Fin.val_ofNat]
  simp only [VG.Spec.MlDsa.q] at hg hx ⊢
  by_cases h : g.toNat < x.toNat
  · rw [decide_eq_true h, BitVec.sub_self,
      show (0#32 - BitVec.setWidth 32 (BitVec.ofBool true) &&& 8380417#32) = 8380417#32 by decide,
      BitVec.toNat_add, BitVec.toNat_sub, show (8380417#32).toNat = 8380417 from rfl]
    omega
  · rw [decide_eq_false h, BitVec.sub_self,
      show (0#32 - BitVec.setWidth 32 (BitVec.ofBool false) &&& 8380417#32) = 0 by decide,
      BitVec.toNat_add, BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl]
    omega

/-- Bit `j` of a 32-bit little-endian word. -/
theorem readW32_getLsbD (m : Mem) (a : Addr) {j : Nat} (hj : j < 32) :
    (m.readW a 32).getLsbD j = (m (a + BitVec.ofNat 64 (j / 8))).getLsbD (j % 8) := by
  rw [Mem.readW_byte m a (by omega), BitVec.getLsbD_extractLsb']
  simp only [show j % 8 < 8 by omega, decide_true, Bool.true_and]
  congr 1; omega

/-- The `c` bits from bit `sh` of the word at `a` are those of `X` from bit
`8o + sh`, if its first 3 bytes are those of `X` from byte `o`. -/
theorem wordBits (m : Mem) (a : Addr) (X : List Byte) {o sh c : Nat} (hc : sh + c ≤ 24)
    (hb : ∀ b < 3, m (a + BitVec.ofNat 64 b) = X.getD (o + b) 0) :
    (m.readW a 32).toNat / 2 ^ sh % 2 ^ c = VG.Proof.MlDsa.Sample.leNat X / 2 ^ (8 * o + sh) % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < c
  · simp only [hj, decide_true, Bool.true_and]
    rw [← BitVec.getLsbD, VG.Proof.MlDsa.Sample.readW32_getLsbD m a (j := j + sh) (by omega), hb ((j + sh) / 8) (by omega),
      VG.Proof.MlDsa.Sample.testBit_leNat, show (j + (8 * o + sh)) / 8 = o + (j + sh) / 8 by omega,
      show (j + (8 * o + sh)) % 8 = (j + sh) % 8 by omega]
  · simp [hj]

end VG.Proof.MlDsa.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sample.Signs`. -/
section

/-!
# ML-DSA: the sign bits of `SampleInBall` in two 32-bit words

An implementation with 32-bit words keeps the sign bits of `SampleInBall` not
yet used, the first 8 bytes of the output as a little-endian integer `S`
shifted right by the number `t` of signs used, as two words: `S / 2^t` (modulo
`2³²`) and `S / 2^(t+32)`. They start as the two little-endian words of the
bytes (`readW_lo`, `readW_hi`); the next sign is the low bit of the first
(`signBit_eq`); and shifting the pair right by one bit is the first shifted
right by one plus the low bit of the second rotated to the top
(`signs_shift`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- A value less than `2ⁿ`, rotated right by `n`, is shifted left by `32 - n`. -/
theorem rotr_small32 (x : BitVec 32) {n : Nat} (h0 : 0 < n) (h : n < 32) (hx : x.toNat < 2 ^ n) :
    (x.rotateRight n).toNat = x.toNat * 2 ^ (32 - n) := by
  rw [BitVec.rotateRight_def, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  simp only [Nat.mod_eq_of_lt h]
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hx, Nat.zero_or, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have : x.toNat * 2 ^ (32 - n) < 2 ^ n * 2 ^ (32 - n) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
  rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)] at this
  exact this

theorem and_one_toNat (x : BitVec 32) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]

/-- The high word shifted right by one bit. -/
theorem signs_shift_hi {S : Nat} (hS : S < 2 ^ 64) (t : Nat) :
    BitVec.ofNat 32 (S / 2 ^ (t + 32)) >>> 1 = BitVec.ofNat 32 (S / 2 ^ (t + 1 + 32)) := by
  have e : S / 2 ^ (t + 1 + 32) = S / 2 ^ (t + 32) / 2 := by
    rw [show t + 1 + 32 = t + 32 + 1 by omega, Nat.pow_succ, Nat.div_div_eq_div_mul]
  have hl : S / 2 ^ (t + 32) < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide) (by omega))
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (by omega)]

/-- The word at `a` whose bits `j < 32` are the bits `o + j` of `X`. -/
theorem readW_bits (m : Mem) (a : Addr) (X : List Byte) (o : Nat)
    (hb : ∀ b < 4, m (a + BitVec.ofNat 64 b) = X.getD (o / 8 + b) 0) (ho : o % 8 = 0) :
    m.readW a 32 = BitVec.ofNat 32 (VG.Proof.MlDsa.Sample.leNat X / 2 ^ o) := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro j
  rw [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 32
  · rw [← BitVec.getLsbD, VG.Proof.MlDsa.Sample.readW32_getLsbD m a hj, hb (j / 8) (by omega), VG.Proof.MlDsa.Sample.testBit_leNat,
      show (j + o) / 8 = o / 8 + j / 8 by omega, show (j + o) % 8 = j % 8 by omega]
    simp [hj]
  · simp only [hj, decide_false, Bool.false_and]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (m.readW a 32).isLt (Nat.pow_le_pow_right (by decide) (by omega)))

/-- The first word of the first 8 bytes of `X`. -/
theorem readW_lo (m : Mem) (a : Addr) (X : List Byte) (hb : ∀ b < 8, m (a + BitVec.ofNat 64 b) = X.getD b 0) :
    m.readW a 32 = BitVec.ofNat 32 (VG.Proof.MlDsa.Sample.leNat (X.take 8) / 2 ^ 0) :=
  VG.Proof.MlDsa.Sample.readW_bits m a (X.take 8) 0 (fun b h => by
    rw [Nat.zero_div, Nat.zero_add, hb b (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)])
    rfl

/-- The second word of the first 8 bytes of `X`. -/
theorem readW_hi (m : Mem) (a : Addr) (X : List Byte) (hb : ∀ b < 8, m (a + BitVec.ofNat 64 b) = X.getD b 0) :
    m.readW (a + 4) 32 = BitVec.ofNat 32 (VG.Proof.MlDsa.Sample.leNat (X.take 8) / 2 ^ (0 + 32)) :=
  VG.Proof.MlDsa.Sample.readW_bits m (a + 4) (X.take 8) 32 (fun b h => by
    rw [BitVec.add_assoc, show (4 : BitVec 64) + BitVec.ofNat 64 b = BitVec.ofNat 64 (4 + b) by
      rw [BitVec.ofNat_add]; rfl, hb (4 + b) (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega)]) rfl

/-- The next sign: the low bit of the first word. -/
theorem signBit_eq (S t : Nat) :
    (BitVec.ofNat 32 (S / 2 ^ t) &&& 1 == 0) = !(S.testBit t) := by
  have e : (BitVec.ofNat 32 (S / 2 ^ t) &&& 1).toNat = S / 2 ^ t % 2 := by
    rw [VG.Proof.MlDsa.Sample.and_one_toNat, BitVec.toNat_ofNat]
    omega
  rw [VG.Proof.MlDsa.Sample.testBit_eq]
  by_cases h : S / 2 ^ t % 2 = 1
  · simp only [h, decide_true, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    intro h'; rw [h'] at e; simp at e; omega
  · simp only [h, decide_false, Bool.not_false, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [e]; simp; omega)

/-- The pair of words shifted right by one bit. -/
theorem signs_shift (S t : Nat) :
    BitVec.ofNat 32 (S / 2 ^ t) >>> 1 + (BitVec.ofNat 32 (S / 2 ^ (t + 32)) &&& 1).rotateRight 1 =
      BitVec.ofNat 32 (S / 2 ^ (t + 1)) := by
  have e1 : S / 2 ^ (t + 1) = S / 2 ^ t / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have e2 : S / 2 ^ (t + 32) = S / 2 ^ (t + 1) / 2 ^ 31 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  generalize S / 2 ^ t = A at e1
  rw [e2, e1]
  generalize hB : A / 2 = B
  have hm : (BitVec.ofNat 32 (B / 2 ^ 31) &&& 1).toNat = B / 2 ^ 31 % 2 := by
    rw [VG.Proof.MlDsa.Sample.and_one_toNat, BitVec.toNat_ofNat]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    VG.Proof.MlDsa.Sample.rotr_small32 _ (by decide) (by decide) (by rw [hm]; omega), hm, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

end VG.Proof.MlDsa.Sample

end
