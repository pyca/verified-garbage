module

-- separate module: the specification's closed forms, which `forsPk`'s proofs use too

public import VerifiedGarbage.Spec.SlhDsa
public import VerifiedGarbage.Proof.SlhDsa.Internal
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA: the values verification's code computes

Target-independent facts the proofs of `xmssPk` and `forsPk`
(`Impl/SlhDsa/X86_64/Verify.lean`) need about the specification:

* `base2b_eq`: `base_2b(X, b, out_len)` (Algorithm 4) as bit fields: digit `j`
  is bits `jb` to `jb + b - 1` of `X`, most significant first, from the
  big-endian prefix of `X` (`pre`) through the byte that holds its last bit;
  so the WOTS⁺ digits are the halves of the message's bytes (`digit_even`,
  `digit_odd`), and a FORS index is three bytes shifted (`index_eq`);
* `chain_restore`: the value of a chain that verification's lanes run from
  the least digit of their group, a lane whose digit is above the step
  getting its signature value back after the step, is
  `chain(sig, digit, 15 - digit)` (Algorithm 8, line 9).
-/

@[expose] public section

namespace VG.Proof.SlhDsa

open VG VG.Spec.SlhDsa

/-! ## Base `2ᵇ` -/

/-- The big-endian integer of the first `i` bytes of `X` (bytes past its end
read as 0). -/
def pre (X : List Byte) : Nat → Nat
  | 0 => 0
  | i + 1 => 256 * pre X i + (X.getD i 0).toNat

/-- The bytes `base_2b` has read for its digit `j`: `⌈(j + 1)·b / 8⌉`. -/
def need (b j : Nat) : Nat := ((j + 1) * b + 7) / 8

/-- Lines 6–10 of Algorithm 4, from a state that has read `i` bytes and
holds `bits` of them, to the `c` bytes after which it holds at least `b`
(`8c - b < B + b ≤ 8c` for the bits `B = 8i - bits` it has used). -/
theorem base2bFill_eq (X : List Byte) {b : Nat} :
    ∀ (fuel i bits c : Nat), bits ≤ 8 * i → i ≤ c → 8 * c < 8 * i - bits + b + 8 → 8 * i - bits + b ≤ 8 * c →
      c - i ≤ fuel → base2bFill X b fuel i bits (pre X i) = (c, bits + 8 * (c - i), pre X c)
  | 0, i, bits, c, h₀, hi, h₁, h₂, hf => by
    have : i = c := by omega
    subst this
    simp only [base2bFill, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
  | fuel + 1, i, bits, c, h₀, hi, h₁, h₂, hf => by
    simp only [base2bFill]
    by_cases hb : bits < b
    · rw [ite_eq_left hb, show 256 * pre X i + (X.getD i 0).toNat = pre X (i + 1) from rfl,
        base2bFill_eq X fuel (i + 1) (bits + 8) c (by omega) (by omega) (by omega) (by omega) (by omega)]
      congr 2; omega
    · have : i = c := by omega
      subst this
      rw [ite_eq_right hb]
      simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]

/-- Digit `j` of `base_2b(X, b, ·)`, `0 < b`. -/
def digitAt (X : List Byte) (b j : Nat) : Nat := pre X (need b j) / 2 ^ (8 * need b j - (j + 1) * b) % 2 ^ b

/-- `⌈B/8⌉` bytes hold the first `B` bits. -/
theorem ceil8 (B : Nat) : B ≤ 8 * ((B + 7) / 8) ∧ 8 * ((B + 7) / 8) < B + 8 := by
  have := Nat.div_add_mod (B + 7) 8; have := Nat.mod_lt (B + 7) (show 0 < 8 by decide); omega

theorem need_bounds (b j : Nat) : (j + 1) * b ≤ 8 * need b j ∧ 8 * need b j < (j + 1) * b + 8 :=
  ceil8 _

/-- Algorithm 4 as bit fields: digit `j` is `digitAt X b j`. -/
theorem base2b_eq (X : List Byte) (b outLen : Nat) :
    base2b X b outLen = (List.range outLen).map (digitAt X b) := by
  -- the state before digit `j`: `⌈jb/8⌉` bytes read
  let S : Nat → Nat × Nat × Nat × List Nat := fun j =>
    let i := (j * b + 7) / 8
    (i, 8 * i - j * b, pre X i, (List.range j).map (digitAt X b))
  have hS : (List.range outLen).foldl (fun (st : Nat × Nat × Nat × List Nat) _ =>
      let (i, bits, total, out) := st
      let (i, bits, total) := base2bFill X b (b / 8 + 1) i bits total
      let bits := bits - b
      (i, bits, total, out ++ [total / 2 ^ bits % 2 ^ b])) (S 0) = S outLen := by
    refine foldl_range_inv fun j _ => ?_
    obtain ⟨n₁, n₂⟩ := need_bounds b j
    obtain ⟨c₁, c₂⟩ := ceil8 (j * b)
    have hn : need b j = ((j + 1) * b + 7) / 8 := rfl
    have e : (j + 1) * b = j * b + b := Nat.succ_mul j b
    have hb8 := Nat.div_add_mod b 8
    dsimp only [S]
    rw [base2bFill_eq X (b / 8 + 1) _ _ (need b j) (by omega) (by rw [hn, e]; exact Nat.div_le_div_right (by omega))
      (by omega) (by omega) (by omega)]
    dsimp only
    rw [← hn]
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
    · simp only; omega
    · simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, digitAt]
      congr 4; congr 1; omega
  have h0 : S 0 = (0, 0, 0, []) := by simp [S, pre]
  simp only [base2b]
  rw [← h0, hS]

theorem pre_succ (X : List Byte) (i : Nat) : pre X (i + 1) = 256 * pre X i + (X.getD i 0).toNat := rfl

theorem byte_lt (x : Byte) : x.toNat < 256 := x.isLt

/-- Digit `2q` of the base-16 digits: the high half of byte `q`. -/
theorem digitAt_even (X : List Byte) (q : Nat) : digitAt X 4 (2 * q) = (X.getD q 0).toNat / 16 := by
  have hn : need 4 (2 * q) = q + 1 := by simp only [need]; omega
  simp only [digitAt, hn, pre_succ]
  rw [show 8 * (q + 1) - (2 * q + 1) * 4 = 4 by omega]
  have := byte_lt (X.getD q 0)
  generalize (X.getD q 0).toNat = x at this ⊢
  generalize pre X q = P
  rw [show (2 : Nat) ^ 4 = 16 from rfl]
  omega

/-- Digit `2q + 1`: the low half of byte `q`. -/
theorem digitAt_odd (X : List Byte) (q : Nat) : digitAt X 4 (2 * q + 1) = (X.getD q 0).toNat % 16 := by
  have hn : need 4 (2 * q + 1) = q + 1 := by simp only [need]; omega
  simp only [digitAt, hn, pre_succ]
  rw [show 8 * (q + 1) - (2 * q + 1 + 1) * 4 = 0 by omega, Nat.pow_zero, Nat.div_one, show (2 : Nat) ^ 4 = 16 from rfl]
  omega

/-- The base-16 digits of `X`, two for each byte, high half first. -/
def nibbles (X : List Byte) (n : Nat) : List Nat :=
  (List.range n).flatMap fun q => [(X.getD q 0).toNat / 16, (X.getD q 0).toNat % 16]

theorem base2b_nibbles (X : List Byte) (n : Nat) : base2b X 4 (2 * n) = nibbles X n := by
  rw [base2b_eq]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, List.range_succ, List.range_succ, List.map_append,
      List.map_append, ih]
    unfold nibbles
    rw [List.range_succ, List.flatMap_append]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc, digitAt_odd, digitAt_even, List.cons_append, List.nil_append]

/-- The sum of the checksum (Algorithm 7, lines 2–4) over digits below `w`. -/
theorem foldl_csum (w : Nat) : ∀ (l : List Nat) (c : Nat), (∀ x ∈ l, x < w) →
    l.foldl (fun csum mi => csum + w - 1 - mi) c = c + (l.map fun mi => w - 1 - mi).sum
  | [], c, _ => by simp
  | x :: l, c, h => by
    rw [List.foldl_cons, foldl_csum w l _ (fun y hy => h y (List.mem_cons_of_mem _ hy)), List.map_cons, List.sum_cons]
    have := h x List.mem_cons_self
    omega

/-- The three checksum digits as `xmssTree` computes them, from the sum
`cs` of `15 - digit`. -/
def csumDigits (cs : Nat) : List Nat := [cs / 256 % 16, cs / 16 % 16, cs % 16]

/-- The loop of Algorithm 1 for `w`. -/
def genLen2W (w maxChecksum : Nat) : (fuel len2 capacity : Nat) → Nat
  | 0, len2, _ => len2
  | fuel + 1, len2, capacity =>
    if capacity ≤ maxChecksum then genLen2W w maxChecksum fuel (len2 + 1) (capacity * w) else len2

theorem genLen2Loop_eq (p : Params) (m : Nat) : ∀ fuel l c, p.genLen2Loop m fuel l c = genLen2W p.w m fuel l c
  | 0, _, _ => rfl
  | fuel + 1, l, c => by simp only [Params.genLen2Loop, genLen2W, genLen2Loop_eq p m fuel]

/-- The WOTS⁺ digits (lines 1–7 of Algorithms 7 and 8) for `lg_w = 4` and
`n` of 16, 24 or 32: the halves of the bytes of `M`, then the checksum's three. -/
theorem wotsDigits_eq (p : Params) (hw : p.lgw = 4) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (M : List Byte) :
    wotsDigits p M = nibbles M p.n ++ csumDigits ((nibbles M p.n).map (fun mi => 15 - mi)).sum := by
  have h1 : p.len1 = 2 * p.n := by simp only [Params.len1, hw]; omega
  have h2 : p.len2 = 3 := by
    simp only [Params.len2, genLen2Loop_eq, Params.len1, Params.w, hw]
    rcases hn with h | h | h <;> rw [h] <;> decide
  have hlt : ∀ x ∈ nibbles M p.n, x < 16 := by
    intro x hx
    simp only [nibbles, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨q, _, rfl | rfl⟩ := hx
    · have := byte_lt (M.getD q 0); omega
    · exact Nat.mod_lt _ (by decide)
  simp only [wotsDigits, h1, h2, hw, Params.w, base2b_nibbles]
  rw [show (2 : Nat) ^ 4 = 16 from rfl, foldl_csum 16 _ 0 hlt, Nat.zero_add]
  congr 1
  generalize ((nibbles M p.n).map fun mi => 16 - 1 - mi).sum = cs
  rw [show (8 - 3 * 4 % 8) % 8 = 4 by decide, Nat.shiftLeft_eq, show (2 : Nat) ^ 4 = 16 from rfl,
    show (3 * 4 + 7) / 8 = 2 by decide, base2b_eq]
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, csumDigits]
  have e0 := digitAt_even (toByte (cs * 16) 2) 0
  have e1 := digitAt_odd (toByte (cs * 16) 2) 0
  have e2 := digitAt_even (toByte (cs * 16) 2) 1
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at e0 e1 e2
  rw [e0, e1, e2]
  simp only [toByte, List.range, List.range.loop, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ, BitVec.toNat_ofNat]
  simp only [show 2 - 1 - 0 = 1 from rfl, show 2 - 1 - 1 = 0 from rfl, Nat.pow_one, Nat.pow_zero, Nat.div_one]
  refine List.cons_eq_cons.mpr ⟨by omega, List.cons_eq_cons.mpr ⟨by omega, List.cons_eq_cons.mpr ⟨by omega, rfl⟩⟩⟩

theorem div_shift8 (P x s : Nat) (hx : x < 256) : (256 * P + x) / 2 ^ (s + 8) = P / 2 ^ s := by
  rw [Nat.pow_add, Nat.mul_comm (2 ^ s), ← Nat.div_div_eq_div_mul,
    show (256 * P + x) / 2 ^ 8 = P by rw [show (2 : Nat) ^ 8 = 256 from rfl]; omega]

/-- Reading more bytes and shifting them out gives the same digit. -/
theorem pre_extend (X : List Byte) (a c B : Nat) (hB : B ≤ 8 * c) :
    ∀ r, pre X (c + r) / 2 ^ (8 * (c + r) - B) % 2 ^ a = pre X c / 2 ^ (8 * c - B) % 2 ^ a
  | 0 => rfl
  | r + 1 => by
    rw [← pre_extend X a c B hB r, show c + (r + 1) = c + r + 1 by omega, pre_succ,
      show 8 * (c + r + 1) - B = (8 * (c + r) - B) + 8 by omega, div_shift8 _ _ _ (byte_lt _)]

/-- A FORS index (`0 < a ≤ 14`): digit `t` of `base_2b(X, a, ·)` is bits
`(t·a) mod 8` to that plus `a - 1` of the three bytes from byte `⌊t·a / 8⌋`,
as `Fors.index` computes it. -/
theorem digitAt_three (X : List Byte) {a : Nat} (ha : a ≤ 14) (t : Nat) :
    digitAt X a t =
      ((X.getD (t * a / 8) 0).toNat * 65536 + (X.getD (t * a / 8 + 1) 0).toNat * 256 +
        (X.getD (t * a / 8 + 2) 0).toNat) / 2 ^ (24 - t * a % 8 - a) % 2 ^ a := by
  obtain ⟨n₁, n₂⟩ := need_bounds a t
  have e : (t + 1) * a = t * a + a := Nat.succ_mul t a
  have h8 := Nat.div_add_mod (t * a) 8
  have hm := Nat.mod_lt (t * a) (show 0 < 8 by decide)
  generalize t * a / 8 = o at h8 ⊢
  generalize t * a % 8 = q at h8 hm ⊢
  have hc : need a t ≤ o + 3 := by omega
  have ext := pre_extend X a (need a t) ((t + 1) * a) n₁ (o + 3 - need a t)
  rw [show need a t + (o + 3 - need a t) = o + 3 by omega] at ext
  simp only [digitAt]
  rw [← ext, pre_succ, pre_succ, pre_succ, show 8 * (o + 3) - (t + 1) * a = 24 - q - a by omega]
  generalize (X.getD o 0).toNat = x₀
  generalize (X.getD (o + 1) 0).toNat = x₁
  generalize (X.getD (o + 2) 0).toNat = x₂
  generalize pre X o = P
  obtain ⟨s, hs⟩ : ∃ s, s = 24 - q - a := ⟨_, rfl⟩
  rw [← hs]
  have e24 : 256 * (256 * (256 * P + x₀) + x₁) + x₂ = (x₀ * 65536 + x₁ * 256 + x₂) + 2 ^ s * (2 ^ q * 2 ^ a * P) := by
    rw [← Nat.pow_add, ← Nat.mul_assoc, ← Nat.pow_add, show s + (q + a) = 24 by omega]
    simp only [Nat.reducePow]; omega
  rw [e24, Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.mul_comm (2 ^ q) (2 ^ a), Nat.mul_assoc,
    Nat.add_mul_mod_self_left]

/-- The chain of a verification lane: from the step `t₀ ≤ d` to 14, each
step `j` an `F` with the hash address `j`, the lane given its value `X` back
after every step `j < d`. It ends as `chain(X, d, 15 - d)` (`d ≤ 15`). -/
def restoreRun (p : Params) (pkSeed : List Byte) (adrs : Adrs) (X : List Byte) (d t₀ : Nat) : List Byte :=
  (List.range (15 - t₀)).foldl (fun v j' => if t₀ + j' < d then X else F p pkSeed (setHashAddress adrs (t₀ + j')) v) X

theorem chain_restore (p : Params) (pkSeed : List Byte) (adrs : Adrs) (X : List Byte) {d t₀ : Nat}
    (h₀ : t₀ ≤ d) (hd : d ≤ 15) :
    restoreRun p pkSeed adrs X d t₀ = chain p X d (15 - d) pkSeed adrs := by
  simp only [restoreRun, chain]
  rw [show 15 - t₀ = (d - t₀) + (15 - d) by omega, List.range_add, List.foldl_append]
  have hX : ∀ m, m ≤ d - t₀ → (List.range m).foldl
      (fun v j' => if t₀ + j' < d then X else F p pkSeed (setHashAddress adrs (t₀ + j')) v) X = X := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih => rw [List.range_succ, List.foldl_append, ih (by omega)]; simp only [List.foldl_cons, List.foldl_nil]; rw [ite_eq_left (by omega)]
  rw [hX _ (Nat.le_refl _), List.foldl_map]
  congr 1
  funext v j
  rw [ite_eq_right (by omega), show t₀ + (d - t₀ + j) = d + j by omega]

/-! ## Addresses as their fields -/

/-- The address of the tree `a16` with the type `ty` and the three words
`w₁`, `w₂` and `w₃` (key pair; chain or height; hash or index). -/
def adrsOf (a16 : List Byte) (ty w₁ w₂ w₃ : Nat) : Adrs :=
  a16 ++ toByte ty 4 ++ toByte w₁ 4 ++ toByte w₂ 4 ++ toByte w₃ 4

theorem length_toByte' (x n : Nat) : (toByte x n).length = n := by simp [toByte]

/-- Writing over the middle `B` of `A ++ B ++ C`. -/
theorem setBytes_mid_adrs (A B C : List Byte) {D : List Byte} (h : D.length = B.length) :
    setBytes (A ++ B ++ C) A.length D = A ++ D ++ C := by
  simp only [setBytes, h, List.append_assoc]
  rw [List.take_left' rfl, ← List.drop_drop, List.drop_left, List.drop_left]

theorem adrsOf_length {a16 : List Byte} (h : a16.length = 16) (ty w₁ w₂ w₃ : Nat) :
    (adrsOf a16 ty w₁ w₂ w₃).length = 32 := by
  simp [adrsOf, h, length_toByte']

theorem treeAdrs_eq_adrsOf (a16 : List Byte) : treeAdrs a16 = adrsOf a16 0 0 0 0 := by
  simp only [treeAdrs, adrsOf, List.append_assoc]; rfl

section
variable {a16 : List Byte} (h : a16.length = 16) (ty w₁ w₂ w₃ : Nat)
include h

theorem setTypeAndClear_adrsOf (Y : Nat) : setTypeAndClear (adrsOf a16 ty w₁ w₂ w₃) Y = adrsOf a16 Y 0 0 0 := by
  have e := setBytes_mid_adrs a16 (toByte ty 4 ++ toByte w₁ 4 ++ toByte w₂ 4 ++ toByte w₃ 4) []
    (D := toByte Y 4 ++ toByte 0 12) (by simp [length_toByte'])
  simp only [List.append_nil, h] at e
  simp only [setTypeAndClear, adrsOf, List.append_assoc] at e ⊢
  rw [e]; rfl

theorem setKeyPairAddress_adrsOf (i : Nat) : setKeyPairAddress (adrsOf a16 ty w₁ w₂ w₃) i = adrsOf a16 ty i w₂ w₃ := by
  have e := setBytes_mid_adrs (a16 ++ toByte ty 4) (toByte w₁ 4) (toByte w₂ 4 ++ toByte w₃ 4) (D := toByte i 4)
    (by simp [length_toByte'])
  simp only [List.length_append, h, length_toByte'] at e
  simp only [setKeyPairAddress, adrsOf, List.append_assoc] at e ⊢
  exact e

theorem setChainAddress_adrsOf (i : Nat) : setChainAddress (adrsOf a16 ty w₁ w₂ w₃) i = adrsOf a16 ty w₁ i w₃ := by
  have e := setBytes_mid_adrs (a16 ++ toByte ty 4 ++ toByte w₁ 4) (toByte w₂ 4) (toByte w₃ 4) (D := toByte i 4)
    (by simp [length_toByte'])
  simp only [List.length_append, h, length_toByte'] at e
  simp only [setChainAddress, adrsOf, List.append_assoc] at e ⊢
  exact e

theorem setTreeHeight_adrsOf (i : Nat) : setTreeHeight (adrsOf a16 ty w₁ w₂ w₃) i = adrsOf a16 ty w₁ i w₃ :=
  setChainAddress_adrsOf h ty w₁ w₂ w₃ i

theorem setHashAddress_adrsOf (i : Nat) : setHashAddress (adrsOf a16 ty w₁ w₂ w₃) i = adrsOf a16 ty w₁ w₂ i := by
  have e := setBytes_mid_adrs (a16 ++ toByte ty 4 ++ toByte w₁ 4 ++ toByte w₂ 4) (toByte w₃ 4) [] (D := toByte i 4)
    (by simp [length_toByte'])
  simp only [List.length_append, h, length_toByte', List.append_nil] at e
  simp only [setHashAddress, adrsOf, List.append_assoc] at e ⊢
  exact e

theorem setTreeIndex_adrsOf (i : Nat) : setTreeIndex (adrsOf a16 ty w₁ w₂ w₃) i = adrsOf a16 ty w₁ w₂ i :=
  setHashAddress_adrsOf h ty w₁ w₂ w₃ i

theorem getKeyPairAddress_adrsOf : getKeyPairAddress (adrsOf a16 ty w₁ w₂ w₃) = w₁ % 2 ^ 32 := by
  simp only [getKeyPairAddress, adrsOf, List.append_assoc]
  rw [show (20 : Nat) = (a16 ++ toByte ty 4).length by simp [h, length_toByte'], ← List.append_assoc,
    List.drop_left]
  simp only [toInt]
  rw [List.take_append_of_le_length (by simp [length_toByte'])]
  exact toInt_toByte4 w₁

theorem getTreeIndex_adrsOf : getTreeIndex (adrsOf a16 ty w₁ w₂ w₃) = w₃ % 2 ^ 32 := by
  simp only [getTreeIndex, adrsOf]
  rw [show (28 : Nat) = (a16 ++ toByte ty 4 ++ toByte w₁ 4 ++ toByte w₂ 4).length by simp [h, length_toByte'],
    List.drop_left]
  exact toInt_toByte4 w₃

end

/-! ## The roots verification computes -/

/-- `k` heights of a path from `node`, for the leaf index `L`, the nodes of
the authentication path at `auth` (`n` bytes each), the addresses those of
the tree `a16` of the type `ty` and key pair `kp`: height `j + 1`, index
`⌊L / 2^(j+1)⌋`, the node first or second as bit `j` of `L` says. -/
def path (p : Params) (pkSeed a16 : List Byte) (ty kp L : Nat) (auth : List Byte) : Nat → List Byte → List Byte
  | 0, node => node
  | j + 1, node =>
    let node' := path p pkSeed a16 ty kp L auth j node
    H p pkSeed (adrsOf a16 ty kp (j + 1) (L / 2 ^ (j + 1)))
      (if L / 2 ^ j % 2 = 0 then node' ++ chunk auth p.n j else chunk auth p.n j ++ node')

/-- One height of the specification's loop (Algorithm 11, lines 10–20;
Algorithm 17, lines 9–19), from the address of height `j` and index
`⌊L / 2^j⌋`, with the bit `b` of the specification's index, which is bit
`j` of `L`. -/
theorem pathStep (p : Params) (pkSeed a16 : List Byte) (ha : a16.length = 16) (ty kp L : Nat) (auth node : List Byte)
    (j : Nat) (hL : L < 2 ^ 32) (b : Nat) (hb : b = L / 2 ^ j % 2) :
    (let adrs := setTreeHeight (adrsOf a16 ty kp j (L / 2 ^ j)) (j + 1)
     if b = 0 then
       let adrs := setTreeIndex adrs (getTreeIndex adrs / 2)
       (H p pkSeed adrs (node ++ chunk auth p.n j), adrs)
     else
       let adrs := setTreeIndex adrs ((getTreeIndex adrs - 1) / 2)
       (H p pkSeed adrs (chunk auth p.n j ++ node), adrs)) =
    (H p pkSeed (adrsOf a16 ty kp (j + 1) (L / 2 ^ (j + 1)))
      (if L / 2 ^ j % 2 = 0 then node ++ chunk auth p.n j else chunk auth p.n j ++ node),
     adrsOf a16 ty kp (j + 1) (L / 2 ^ (j + 1))) := by
  have hq : L / 2 ^ j < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hL
  simp only [setTreeHeight_adrsOf ha, getTreeIndex_adrsOf ha, setTreeIndex_adrsOf ha, Nat.mod_eq_of_lt hq,
    div_two_pow_succ, hb]
  generalize L / 2 ^ j = x
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · simp only [h, ↓reduceIte]
  · simp only [h, show ¬ (1 = 0) by decide, ↓reduceIte]
    rw [show (x - 1) / 2 = x / 2 by omega]

/-- The WOTS⁺ public key of a signature (Algorithm 8), for the key pair
`idx` of the tree `a16`: `T_len` of the chains `chain(sig_i, d_i, 15 - d_i)`. -/
theorem wotsPkFromSig_eq (p : Params) {a16 : List Byte} (ha : a16.length = 16) {idx : Nat} (hidx : idx < 2 ^ 32)
    (sig M pkSeed : List Byte) :
    wotsPkFromSig p sig M pkSeed (adrsOf a16 0 idx 0 0) =
      T p pkSeed (adrsOf a16 1 idx 0 0) ((List.range p.len).flatMap fun i =>
        chain p (chunk sig p.n i) ((wotsDigits p M).getD i 0) (p.w - 1 - (wotsDigits p M).getD i 0) pkSeed
          (adrsOf a16 0 idx i 0)) := by
  simp only [wotsPkFromSig, wotsPkAdrs, setTypeAndClear_adrsOf ha, getKeyPairAddress_adrsOf ha,
    setKeyPairAddress_adrsOf ha, setChainAddress_adrsOf ha, Nat.mod_eq_of_lt hidx, WOTS_PK]

/-- The root an XMSS signature gives (Algorithm 11), for the tree `a16` and
the key pair `idx`: the WOTS⁺ public key, then `h′` heights of its path. -/
theorem xmssPkFromSig_eq (p : Params) {a16 : List Byte} (ha : a16.length = 16) {idx : Nat} (hidx : idx < 2 ^ 32)
    (sig M pkSeed : List Byte) :
    xmssPkFromSig p idx sig M pkSeed (treeAdrs a16) =
      path p pkSeed a16 2 0 idx (sig.drop (p.len * p.n)) p.hp
        (wotsPkFromSig p (sig.take (p.len * p.n)) M pkSeed (adrsOf a16 0 idx 0 0)) := by
  simp only [xmssPkFromSig, treeAdrs_eq_adrsOf, setTypeAndClear_adrsOf ha, setKeyPairAddress_adrsOf ha,
    setTreeIndex_adrsOf ha, WOTS_HASH, TREE]
  generalize wotsPkFromSig p (sig.take (p.len * p.n)) M pkSeed (adrsOf a16 0 idx 0 0) = node0
  generalize sig.drop (p.len * p.n) = auth
  have e0 : (node0, adrsOf a16 2 0 0 idx) = (path p pkSeed a16 2 0 idx auth 0 node0, adrsOf a16 2 0 0 (idx / 2 ^ 0)) := by
    simp [path]
  rw [e0]
  refine congrArg Prod.fst (foldl_range_inv (K := p.hp) (S := fun j =>
    (path p pkSeed a16 2 0 idx auth j node0, adrsOf a16 2 0 j (idx / 2 ^ j))) fun j _ => ?_)
  exact (pathStep p pkSeed a16 ha 2 0 idx auth _ j hidx _ rfl).trans (by simp only [path])

/-- Bit `j < a` of a tree's leaf number `i·2^a + idx` is bit `j` of `idx`. -/
theorem bit_leaf {i a idx j : Nat} (hj : j < a) : (i * 2 ^ a + idx) / 2 ^ j % 2 = idx / 2 ^ j % 2 := by
  rw [div_two_pow_of_le (Nat.le_of_lt hj), show a - j = (a - j - 1) + 1 by omega, Nat.pow_succ,
    ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_right]

/-- The FORS public key of a signature (Algorithm 17), for the key pair `kp`
of the tree `a16`: `T_k` of each tree's path from the `F` of its private key
value, from its leaf number `i·2^a + idx`. -/
theorem forsPkFromSig_eq (p : Params) {a16 : List Byte} (ha : a16.length = 16) {kp : Nat} (hkp : kp < 2 ^ 32)
    (hk : p.k * 2 ^ p.a ≤ 2 ^ 32) (sig md pkSeed : List Byte) :
    forsPkFromSig p sig md pkSeed (forsAdrs a16 kp) =
      T p pkSeed (adrsOf a16 4 kp 0 0) ((List.range p.k).flatMap fun i =>
        let L := i * 2 ^ p.a + (base2b md p.a p.k).getD i 0
        path p pkSeed a16 3 kp L ((sig.drop (p.n * (i * (p.a + 1) + 1))).take (p.a * p.n)) p.a
          (F p pkSeed (adrsOf a16 3 kp 0 L) (chunk sig p.n (i * (p.a + 1))))) := by
  simp only [forsPkFromSig, forsAdrs, treeAdrs_eq_adrsOf, setTypeAndClear_adrsOf ha, setKeyPairAddress_adrsOf ha,
    getKeyPairAddress_adrsOf ha, Nat.mod_eq_of_lt hkp, FORS_TREE, FORS_ROOTS]
  refine congrArg (T p pkSeed _) (flatMap_range_congr fun i hi => ?_)
  have hidx := base2b_getD_lt md p.a p.k i
  generalize (base2b md p.a p.k).getD i 0 = idx at hidx ⊢
  generalize (sig.drop (p.n * (i * (p.a + 1) + 1))).take (p.a * p.n) = auth
  have hL : i * 2 ^ p.a + idx < 2 ^ 32 := by
    have : (i + 1) * 2 ^ p.a ≤ p.k * 2 ^ p.a := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this; omega
  rw [setTreeHeight_adrsOf ha, setTreeIndex_adrsOf ha]
  generalize F p pkSeed (adrsOf a16 3 kp 0 (i * 2 ^ p.a + idx)) (chunk sig p.n (i * (p.a + 1))) = node0
  have e0 : (node0, adrsOf a16 3 kp 0 (i * 2 ^ p.a + idx)) =
      (path p pkSeed a16 3 kp (i * 2 ^ p.a + idx) auth 0 node0,
        adrsOf a16 3 kp 0 ((i * 2 ^ p.a + idx) / 2 ^ 0)) := by simp [path]
  rw [e0]
  refine congrArg Prod.fst (foldl_range_inv (K := p.a) (S := fun j =>
    (path p pkSeed a16 3 kp (i * 2 ^ p.a + idx) auth j node0, adrsOf a16 3 kp j ((i * 2 ^ p.a + idx) / 2 ^ j)))
    fun j hj => ?_)
  exact (pathStep p pkSeed a16 ha 3 kp _ auth _ j hL _ (bit_leaf hj).symm).trans (by simp only [path])

end VG.Proof.SlhDsa
