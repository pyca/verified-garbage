module

public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Ffdh.Domain

/-!
# FFDH's key-generation context, row by row

The context `generationPrecompute` writes is `3 + 34 w` words: three public
words, then 34 rows of `w` words (`p`, `R² mod p` and the 32 comb entries),
row `j` at byte `24 + 8 w j`. `ctx_words` builds the context's words from
its parts; `rows_of_ctx` reads them back, and `value_of_row` a row's number,
also as 32-bit words (`val32_eq_wv`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.ContextRows

open VG VG.Proof.Bignum

/-- The words of row `j`. -/
def row (m : Mem) (cp : Addr) (w j : Nat) : List (BitVec 64) :=
  (List.range w).map fun i => word m cp (24 + 8 * w * j + 8 * i)

theorem row_length (m : Mem) (cp : Addr) (w j : Nat) : (row m cp w j).length = w := by
  simp only [row, List.length_map, List.length_range]

theorem row_congr {m m' : Mem} {cp : Addr} {w j : Nat}
    (h : ∀ i < w, word m' cp (24 + 8 * w * j + 8 * i) = word m cp (24 + 8 * w * j + 8 * i)) :
    row m' cp w j = row m cp w j := by
  unfold row
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- A row holds the words of its own number. -/
theorem row_self (m : Mem) (cp : Addr) (w j : Nat) :
    row m cp w j = Spec.Rsa.toWords (wv m cp (24 + 8 * w * j) w) w := by
  unfold row Spec.Rsa.toWords
  apply List.map_congr_left
  intro i hi
  exact word_eq_ofNat m cp _ w (List.mem_range.mp hi)

/-- The value of a row that holds `toWords V w`, for `V < 2^(64 w)`. -/
theorem value_of_row {m : Mem} {cp : Addr} {w j V : Nat} (h : row m cp w j = Spec.Rsa.toWords V w)
    (hV : V < 2 ^ (64 * w)) : wv m cp (24 + 8 * w * j) w = V := by
  rw [← Nat.mod_eq_of_lt hV]
  refine wv_of_words fun i hi => ?_
  have := congrArg (fun l => l[i]?) h
  simp only [row, Spec.Rsa.toWords, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] at this
  rw [this, BitVec.toNat_ofNat]

/-- A number of `2 W` 32-bit words is one of `W` 64-bit words. -/
theorem val32_eq_wv (m : Mem) (P : Addr) (d W : Nat) : Mont.val32 m P d (2 * W) = wv m P d W := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_wv, show 4 * (2 * W) = 8 * W by omega]

/-- The address of word `i` of row `j`, as a word of the context. -/
theorem rowOff {w j i : Nat} : 24 + 8 * w * j + 8 * i = 8 * (3 + w * j + i) := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_assoc]

theorem flatMap_congr' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ a ∈ l, f a = g a) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp), flatMap_congr' (fun x hx => h x (by simp [hx]))]

theorem range_mul_map {α : Type} (g : Nat → α) (w : Nat) : ∀ n,
    (List.range (w * n)).map g = (List.range n).flatMap fun j => (List.range w).map fun i => g (w * j + i)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.mul_succ, List.range_add, List.map_append, range_mul_map g w n, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.map_map]
    rfl

/-- The context's words: its three public words, then its 34 rows. -/
theorem wordsAt_rows (m : Mem) (cp : Addr) (w : Nat) :
    Spec.Rsa.wordsAt m cp (3 + 34 * w) =
      [word m cp 0, word m cp 8, word m cp 16] ++ (List.range 34).flatMap (row m cp w) := by
  unfold Spec.Rsa.wordsAt
  rw [List.range_add, List.map_append, show 34 * w = w * 34 from Nat.mul_comm _ _, List.map_map,
    range_mul_map _ w 34]
  have h3 : (List.range 3).map (fun i => m.readW (cp + BitVec.ofNat 64 (8 * i)) 64) =
      [word m cp 0, word m cp 8, word m cp 16] := rfl
  rw [h3]
  refine congrArg (_ ++ ·) (flatMap_congr' fun j _ => List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply, Bignum.word, off]
  rw [rowOff, show 3 + (w * j + i) = 3 + w * j + i by omega]

/-- The context's words from its parts. -/
theorem ctx_words {m : Mem} {cp : Addr} {w : Nat} {h₀ h₁ h₂ : BitVec 64} {r₀ r₁ : List (BitVec 64)}
    {ent : Nat → List (BitVec 64)} (e₀ : word m cp 0 = h₀) (e₁ : word m cp 8 = h₁) (e₂ : word m cp 16 = h₂)
    (f₀ : row m cp w 0 = r₀) (f₁ : row m cp w 1 = r₁) (fe : ∀ a < 32, row m cp w (2 + a) = ent a) :
    Spec.Rsa.wordsAt m cp (3 + 34 * w) = [h₀, h₁, h₂] ++ r₀ ++ r₁ ++ (List.range 32).flatMap ent := by
  rw [wordsAt_rows, e₀, e₁, e₂, show 34 = 2 + 32 from rfl, List.range_add, List.flatMap_append,
    show List.range 2 = [0, 1] from rfl, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, f₀, f₁,
    List.flatMap_map]
  simp only [List.append_nil, List.append_assoc]
  congr 3
  apply flatMap_congr'
  intro a ha
  exact fe a (List.mem_range.mp ha)

/-- Pieces of one length `w` from the same flattening are the same. -/
theorem flatMap_range_inj {α : Type} {f g : Nat → List α} {w : Nat} (hf : ∀ a, (f a).length = w)
    (hg : ∀ a, (g a).length = w) : ∀ {n : Nat}, (List.range n).flatMap f = (List.range n).flatMap g →
      ∀ a < n, f a = g a
  | 0, _, _, ha => absurd ha (Nat.not_lt_zero _)
  | n + 1, h, a, ha => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_singleton,
      List.flatMap_singleton] at h
    have hl : ((List.range n).flatMap f).length = ((List.range n).flatMap g).length := by
      simp only [List.length_flatMap, hf, hg]
    obtain ⟨h₁, h₂⟩ := List.append_inj h hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha with lt | rfl
    · exact flatMap_range_inj hf hg h₁ a lt
    · exact h₂

/-- The context's parts from its words. -/
theorem rows_of_ctx {m : Mem} {cp : Addr} {w : Nat} {h₀ h₁ h₂ : BitVec 64} {r₀ r₁ : List (BitVec 64)}
    {ent : Nat → List (BitVec 64)} (l₀ : r₀.length = w) (l₁ : r₁.length = w) (le : ∀ a, (ent a).length = w)
    (h : Spec.Rsa.wordsAt m cp (3 + 34 * w) = [h₀, h₁, h₂] ++ r₀ ++ r₁ ++ (List.range 32).flatMap ent) :
    word m cp 0 = h₀ ∧ word m cp 8 = h₁ ∧ word m cp 16 = h₂ ∧ row m cp w 0 = r₀ ∧ row m cp w 1 = r₁ ∧
      ∀ a < 32, row m cp w (2 + a) = ent a := by
  rw [wordsAt_rows, show 34 = 2 + 32 from rfl, List.range_add, List.flatMap_append,
    show List.range 2 = [0, 1] from rfl, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
    List.flatMap_map] at h
  simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨e₀, e₁, e₂, h⟩ := h
  obtain ⟨f₀, h⟩ := List.append_inj h (by rw [row_length, l₀])
  obtain ⟨f₁, h⟩ := List.append_inj h (by rw [row_length, l₁])
  refine ⟨e₀, e₁, e₂, f₀, f₁, fun a ha => ?_⟩
  exact flatMap_range_inj (f := fun a => row m cp w (2 + a)) (fun _ => row_length _ _ _ _) le h a ha

/-- `generationValues` in the parts `ctx_words` takes. -/
theorem generationValues_parts (pLen : Nat) (dom : List Byte) :
    let a := Spec.Ffdh.domainOf pLen dom
    let bits := Spec.Ffdh.generationScalarBits a
    let w := Spec.Rsa.modulusWords pLen
    generationValues pLen dom =
      [BitVec.ofNat 64 bits, BitVec.ofNat 64 ((bits + 7) / 8), BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)] ++
        Spec.Rsa.toWords a.p w ++ Spec.Rsa.toWords (2 ^ (128 * w) % a.p) w ++
        (List.range 32).flatMap fun d =>
          Spec.Rsa.toWords (Spec.Rsa.powMod a.g (Spec.Rsa.FixedBaseComb.exponent bits d) a.p * 2 ^ (64 * w) % a.p) w :=
  rfl

/-! ## The context's words as 32-bit words -/

/-- The low half of a 64-bit word. -/
theorem w32_of_word (m : Mem) (P : Addr) (d : Nat) : Mont.w32 m P d = (word m P d).toNat % 2 ^ 32 := by
  have h1 := VG.Proof.Bignum.read_eq_val32 m P 2 d
  have h2 := VG.Proof.Bignum.read_eq_wv m P d 1
  rw [show 8 * 1 = 4 * 2 from rfl, h1] at h2
  simp only [Mont.val32, wv, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add,
    Nat.mul_zero] at h2
  rw [← h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- The context's words, from `generationValues`: its public words and its 34 rows. -/
theorem ctx_of_values {m : Mem} {cp : Addr} {len : Nat} {dom : List Byte}
    (h : Spec.Rsa.wordsAt m cp (3 + 34 * Spec.Rsa.modulusWords len) = generationValues len dom) :
    let a := Spec.Ffdh.domainOf len dom
    let bits := Spec.Ffdh.generationScalarBits a
    let w := Spec.Rsa.modulusWords len
    word m cp 0 = BitVec.ofNat 64 bits ∧ word m cp 8 = BitVec.ofNat 64 ((bits + 7) / 8) ∧
      word m cp 16 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧
      row m cp w 0 = Spec.Rsa.toWords a.p w ∧ row m cp w 1 = Spec.Rsa.toWords (2 ^ (128 * w) % a.p) w ∧
      ∀ e < 32, row m cp w (2 + e) = Spec.Rsa.toWords
        (Spec.Rsa.powMod a.g (Spec.Rsa.FixedBaseComb.exponent bits e) a.p * 2 ^ (64 * w) % a.p) w := by
  rw [generationValues_parts] at h
  exact rows_of_ctx (by simp [Spec.Rsa.toWords]) (by simp [Spec.Rsa.toWords]) (fun _ => by simp [Spec.Rsa.toWords]) h

/-- A vetted width is not zero. -/
theorem recognized_nonzero {a : Spec.Ffdh.Parameters} {bits : Nat}
    (h : Spec.Ffdh.vettedExponentBits a = some bits) : bits ≠ 0 := by
  unfold Spec.Ffdh.vettedExponentBits at h
  repeat' split at h
  all_goals cases h
  all_goals decide

theorem bitLength_le_of_lt {x n : Nat} (h : x < 2 ^ n) : Spec.RsaKeyGen.bitLength x ≤ n := by
  by_cases hx : x = 0
  · subst hx; unfold Spec.RsaKeyGen.bitLength; simp
  · have hb := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds hx).1
    refine Classical.byContradiction fun hc => ?_
    have : 2 ^ n ≤ 2 ^ (Spec.RsaKeyGen.bitLength x - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- The public scalar width of valid parameters: at least 1 and at most p's bits. -/
theorem genBits_facts {k : Nat} {dom : List Byte} (hv : Spec.Ffdh.domainValid k dom = true) :
    1 ≤ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) ∧
      Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) ≤ 8 * k := by
  have hv' := (VG.Proof.Ffdh.domainValid_iff k dom).mp hv
  have hbnd : 2 ≤ Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv'.2.2 q hq).1.2.1; simp only [Option.getD_some]; omega
  have hle : Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≤ (Spec.Ffdh.domainOf k dom).p := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv'.2.2 q hq).1.2.2; simp only [Option.getD_some]; omega
  have hp : (Spec.Ffdh.domainOf k dom).p < 2 ^ (8 * k) := by
    have h1 := VG.Proof.Bignum.os2ip_lt (dom.take k)
    have h2 : 256 ^ (dom.take k).length ≤ 2 ^ (8 * k) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by simp only [List.length_take]; omega)
    change Spec.Rsa.os2ip (dom.take k) < _
    omega
  have hb := VG.Proof.Ffdh.VettedPolicy.bits_le_bound (Spec.Ffdh.domainOf k dom)
  have hbl : 1 ≤ Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) := by
    have := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds
      (show Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≠ 0 by omega)).2
    refine Classical.byContradiction fun hc => ?_
    have e : Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) = 0 := by omega
    rw [e] at this; omega
  refine ⟨?_, Nat.le_trans hb (bitLength_le_of_lt (Nat.lt_of_le_of_lt hle hp))⟩
  unfold Spec.Ffdh.generationScalarBits
  cases he : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom) with
  | none => simpa using hbl
  | some b => have := recognized_nonzero he; simp only; omega

end VG.Proof.Ffdh.ContextRows
