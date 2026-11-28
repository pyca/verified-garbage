module

public import VerifiedGarbage.Spec.SlhDsa
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA: lemmas about the specification

Target-independent facts about `Spec/SlhDsa.lean` that an implementation
which computes the trees by building them, rather than as the standard's
algorithms do, needs:

* the lengths of the hash functions' outputs (`F_length`, …), and of the
  signatures' parts;
* `chain_add`: two chains, the second from where the first stopped, are one;
* `wotsPkFromSig_wotsSign`: the public key a WOTS⁺ signature gives is the
  key pair's public key;
* the addresses: each setter in terms of the bytes it writes (`getElem_setBytes`),
  and the identities between them the trees need;
* `xmssPkFromSig_xmssSign`: the root an XMSS signature gives is the tree's
  root;
* `forsPkFromSig_forsSign`: the FORS public key a FORS signature gives is
  `T_k` of the trees' roots;
* the trees' levels (`xmssNode_succ`, `forsNode_succ`) and their subtrees
  (`xmssNode_subtree`, `forsNode_subtree`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa

open VG VG.Spec.SlhDsa

/-! ## Lists -/

/-- The concatenation of `f 0, …, f (i - 1)`, each of `L` bytes, has `L·i`. -/
theorem length_flatMap_range {f : Nat → List Byte} {L : Nat} :
    ∀ {i : Nat}, (∀ j < i, (f j).length = L) → ((List.range i).flatMap f).length = L * i
  | 0, _ => by simp
  | i + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range (fun j hj => h j (by omega)),
      List.flatMap_singleton, h i (by omega), Nat.mul_succ]

/-- `f 0 ‖ … ‖ f (K - 1)`, split at `f i`. -/
theorem flatMap_range_split (f : Nat → List Byte) {i K : Nat} (hi : i < K) :
    (List.range K).flatMap f =
      (List.range i).flatMap f ++ (f i ++ (List.range (K - i - 1)).flatMap fun j => f (i + 1 + j)) := by
  obtain ⟨r, rfl⟩ : ∃ r, K = i + 1 + r := ⟨K - i - 1, by omega⟩
  rw [List.range_add, List.flatMap_append, List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.flatMap_map, show i + 1 + r - i - 1 = r by omega, List.append_assoc]

/-- The bytes of `f 0 ‖ … ‖ f (K - 1)` from `f i` on, each `f j` of `L` bytes. -/
theorem drop_flatMap_range {f : Nat → List Byte} {L i K : Nat} (hL : ∀ j < K, (f j).length = L) (hi : i < K) :
    ((List.range K).flatMap f).drop (L * i) =
      f i ++ (List.range (K - i - 1)).flatMap fun j => f (i + 1 + j) := by
  rw [flatMap_range_split f hi, List.drop_append_of_le_length (by rw [length_flatMap_range fun j hj => hL j (by omega)]),
    List.drop_of_length_le (by rw [length_flatMap_range fun j hj => hL j (by omega)]), List.nil_append]

/-- String `i` of `f 0 ‖ … ‖ f (K - 1)`, each of `n` bytes, is `f i`. -/
theorem chunk_flatMap_range {f : Nat → List Byte} {n i K : Nat} (hL : ∀ j < K, (f j).length = n) (hi : i < K) :
    chunk ((List.range K).flatMap f) n i = f i := by
  rw [chunk, drop_flatMap_range hL hi, List.take_append_of_le_length (by rw [hL i hi]),
    List.take_of_length_le (by rw [hL i hi])]

/-! ## Lengths -/

theorem shake256_length (m : List Byte) (d : Nat) : (Spec.Sha3.shake256 m d).length = d :=
  Proof.Sha3.length_squeeze (by decide) (by decide) _ d

theorem sha256_length (m : List Byte) : (Spec.Sha256.hash m).length = 32 := by
  simp [Spec.Sha256.hash, Spec.Sha256.finalHash, Spec.Sha256.wordBytes, List.length_flatMap, List.map_const']

theorem sha512_length (m : List Byte) : (Spec.Sha512.sha512 m).length = 64 := by
  simp [Spec.Sha512.sha512, Spec.Sha512.finalHash, Spec.Sha512.wordBytes, List.length_flatMap, List.map_const']

variable {p : Params}

theorem sha256Adrs_length (hn : p.n ≤ 32) (pk : List Byte) (a : Adrs) (M : List Byte) :
    (sha256Adrs p pk a M).length = p.n := by
  rw [sha256Adrs, List.length_take, sha256_length]; omega

theorem sha512Adrs_length (hn : p.n ≤ 32) (pk : List Byte) (a : Adrs) (M : List Byte) :
    (sha512Adrs p pk a M).length = p.n := by
  rw [sha512Adrs, List.length_take, sha512_length]; omega

theorem shakeAdrs_length (pk : List Byte) (a : Adrs) (M : List Byte) : (shakeAdrs p pk a M).length = p.n :=
  shake256_length _ _

theorem F_length (hn : p.n ≤ 32) (pk : List Byte) (a : Adrs) (M : List Byte) : (F p pk a M).length = p.n := by
  unfold F; split
  · exact shakeAdrs_length _ _ _
  · exact sha256Adrs_length hn _ _ _

theorem prf_length (hn : p.n ≤ 32) (pk sk : List Byte) (a : Adrs) : (prf p pk sk a).length = p.n := by
  unfold prf; split
  · exact shakeAdrs_length _ _ _
  · exact sha256Adrs_length hn _ _ _

theorem H_length (hn : p.n ≤ 32) (pk : List Byte) (a : Adrs) (M : List Byte) : (H p pk a M).length = p.n := by
  unfold H; split
  · exact shakeAdrs_length _ _ _
  · split
    · exact sha256Adrs_length hn _ _ _
    · exact sha512Adrs_length hn _ _ _

theorem T_length (hn : p.n ≤ 32) (pk : List Byte) (a : Adrs) (M : List Byte) : (T p pk a M).length = p.n := by
  unfold T; split
  · exact shakeAdrs_length _ _ _
  · split
    · exact sha256Adrs_length hn _ _ _
    · exact sha512Adrs_length hn _ _ _

/-! ## Chains -/

/-- A chain run from where another stopped continues it. -/
theorem chain_add (X : List Byte) (i s t : Nat) (pkSeed : List Byte) (adrs : Adrs) :
    chain p (chain p X i s pkSeed adrs) (i + s) t pkSeed adrs = chain p X i (s + t) pkSeed adrs := by
  simp only [chain, List.range_add, List.foldl_append, List.foldl_map, Nat.add_assoc]

/-- `chain_add` from the start of the chain. -/
theorem chain_add_zero (X : List Byte) (s t : Nat) (pkSeed : List Byte) (adrs : Adrs) :
    chain p (chain p X 0 s pkSeed adrs) s t pkSeed adrs = chain p X 0 (s + t) pkSeed adrs := by
  simpa using chain_add X 0 s t pkSeed adrs

/-- A chain of `n`-byte strings outputs `n` bytes. -/
theorem chain_length (hn : p.n ≤ 32) {X : List Byte} (hX : X.length = p.n) (i s : Nat) (pkSeed : List Byte)
    (adrs : Adrs) : (chain p X i s pkSeed adrs).length = p.n := by
  unfold chain
  induction s with
  | zero => simpa using hX
  | succ s ih => rw [List.range_succ, List.foldl_append]; exact F_length hn _ _ _

/-! ## Base-`2ᵇ` digits -/

/-- A fold whose every step appends one number below `2ᵇ` to the list
`out` reads off its state. -/
theorem foldl_appends {σ : Type} {g : σ → Nat → σ} {out : σ → List Nat} {b : Nat}
    (hg : ∀ st x, ∃ v, out (g st x) = out st ++ [v] ∧ v < 2 ^ b) :
    ∀ (l : List Nat) (st : σ),
      (out (l.foldl g st)).length = (out st).length + l.length ∧
        ((∀ x ∈ out st, x < 2 ^ b) → ∀ x ∈ out (l.foldl g st), x < 2 ^ b)
  | [], _ => ⟨rfl, fun h => h⟩
  | x :: l, st => by
    obtain ⟨v, hv, hlt⟩ := hg st x
    obtain ⟨h1, h2⟩ := foldl_appends hg l (g st x)
    refine ⟨by rw [List.foldl_cons, h1, hv]; simp only [List.length_append, List.length_cons, List.length_nil]; omega,
      fun h => ?_⟩
    rw [List.foldl_cons]
    refine h2 ?_
    intro y hy
    rw [hv, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact h y hy
    · exact hlt

theorem base2b_spec (X : List Byte) (b outLen : Nat) :
    (base2b X b outLen).length = outLen ∧ ∀ x ∈ base2b X b outLen, x < 2 ^ b := by
  have := foldl_appends (b := b) (out := fun (st : Nat × Nat × Nat × List Nat) => st.2.2.2)
    (g := fun (st : Nat × Nat × Nat × List Nat) (_ : Nat) =>
        let (i, bits, total, out) := st
        let (i, bits, total) := base2bFill X b (b / 8 + 1) i bits total
        let bits := bits - b
        (i, bits, total, out ++ [total / 2 ^ bits % 2 ^ b]))
    (fun st _ => by
      obtain ⟨i, bits, total, out⟩ := st
      exact ⟨_, rfl, Nat.mod_lt _ (Nat.two_pow_pos b)⟩)
    (List.range outLen) (0, 0, 0, [])
  obtain ⟨h1, h2⟩ := this
  simp only [List.length_nil, Nat.zero_add, List.length_range] at h1
  exact ⟨h1, h2 (by simp)⟩

/-- `flatMap` over `range K` of functions that agree below `K`. -/
theorem flatMap_range_congr {f g : Nat → List Byte} :
    ∀ {K : Nat}, (∀ i < K, f i = g i) → (List.range K).flatMap f = (List.range K).flatMap g
  | 0, _ => rfl
  | K + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_congr fun i hi => h i (by omega),
      List.flatMap_singleton, List.flatMap_singleton, h K (by omega)]

theorem base2b_length (X : List Byte) (b outLen : Nat) : (base2b X b outLen).length = outLen :=
  (base2b_spec X b outLen).1

theorem base2b_lt (X : List Byte) (b outLen : Nat) : ∀ x ∈ base2b X b outLen, x < 2 ^ b :=
  (base2b_spec X b outLen).2

theorem base2b_getD_lt (X : List Byte) (b outLen i : Nat) : (base2b X b outLen).getD i 0 < 2 ^ b := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (base2b X b outLen)[i]? with
  | none => exact Nat.two_pow_pos b
  | some x => exact base2b_lt X b outLen x (List.mem_of_getElem? h)

theorem wotsDigits_length (M : List Byte) : (wotsDigits p M).length = p.len := by
  simp [wotsDigits, base2b_length, Params.len]

theorem wotsDigits_lt (M : List Byte) : ∀ x ∈ wotsDigits p M, x < p.w := by
  intro x hx
  simp only [wotsDigits, List.mem_append] at hx
  rcases hx with hx | hx <;> exact base2b_lt _ _ _ x hx

theorem wotsDigits_getD_lt (M : List Byte) (i : Nat) : (wotsDigits p M).getD i 0 < p.w := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (wotsDigits p M)[i]? with
  | none => exact Nat.two_pow_pos _
  | some x => exact wotsDigits_lt M x (List.mem_of_getElem? h)

/-! ## WOTS⁺ -/

theorem wotsSign_length (hn : p.n ≤ 32) (M skSeed pkSeed : List Byte) (adrs : Adrs) :
    (wotsSign p M skSeed pkSeed adrs).length = p.len * p.n := by
  rw [wotsSign, length_flatMap_range (L := p.n) (fun j _ => chain_length hn (prf_length hn _ _ _) _ _ _ _),
    Nat.mul_comm]

theorem wotsPkGen_length (hn : p.n ≤ 32) (skSeed pkSeed : List Byte) (adrs : Adrs) :
    (wotsPkGen p skSeed pkSeed adrs).length = p.n := T_length hn _ _ _

/-- The public key a WOTS⁺ signature of `M` gives is the key pair's. -/
theorem wotsPkFromSig_wotsSign (hn : p.n ≤ 32) (M skSeed pkSeed : List Byte) (adrs : Adrs) :
    wotsPkFromSig p (wotsSign p M skSeed pkSeed adrs) M pkSeed adrs = wotsPkGen p skSeed pkSeed adrs := by
  unfold wotsPkFromSig wotsPkGen
  refine congrArg (T p pkSeed (wotsPkAdrs adrs)) (flatMap_range_congr fun i hi => ?_)
  dsimp only
  rw [wotsSign, chunk_flatMap_range (fun j _ => chain_length hn (prf_length hn _ _ _) _ _ _ _) hi, chain_add_zero]
  have := wotsDigits_getD_lt (p := p) M i
  rw [show (wotsDigits p M).getD i 0 + (p.w - 1 - (wotsDigits p M).getD i 0) = p.w - 1 by omega]

/-! ## Addresses -/

/-- Two lists of bytes are equal if they have one length and the same bytes. -/
theorem ext_getD {a b : List Byte} (hl : a.length = b.length) (h : ∀ j < a.length, a.getD j 0 = b.getD j 0) :
    a = b := by
  apply List.ext_getElem hl
  intro j h1 h2
  have := h j h1
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at this

theorem length_toByte (x n : Nat) : (toByte x n).length = n := by simp [toByte]

theorem length_setBytes {a : Adrs} {i : Nat} {bs : List Byte} (h : i + bs.length ≤ a.length) :
    (setBytes a i bs).length = a.length := by
  simp only [setBytes, List.length_append, List.length_take, List.length_drop]; omega

theorem getD_setBytes {a : Adrs} {i : Nat} {bs : List Byte} (h : i + bs.length ≤ a.length) (j : Nat) :
    (setBytes a i bs).getD j 0 =
      if j < i then a.getD j 0 else if j < i + bs.length then bs.getD (j - i) 0 else a.getD j 0 := by
  have ht : (a.take i).length = i := by rw [List.length_take]; omega
  have htb : (a.take i ++ bs).length = i + bs.length := by rw [List.length_append, ht]
  simp only [setBytes, List.getD_eq_getElem?_getD]
  by_cases h1 : j < i
  · simp only [h1, ↓reduceIte]
    rw [List.getElem?_append_left (by rw [htb]; omega), List.getElem?_append_left (by rw [ht]; omega),
      List.getElem?_take]
    simp only [h1, ↓reduceIte]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : j < i + bs.length
    · simp only [h2, ↓reduceIte]
      rw [List.getElem?_append_left (by rw [htb]; omega), List.getElem?_append_right (by rw [ht]; omega),
        ht]
    · simp only [h2, ↓reduceIte]
      rw [List.getElem?_append_right (by rw [htb]; omega), htb, List.getElem?_drop,
        show i + bs.length + (j - (i + bs.length)) = j by omega]

theorem getD_toByte_zero (n j : Nat) : (toByte 0 n).getD j 0 = 0 := by
  simp only [toByte, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (List.range n)[j]? <;> simp

theorem getD_append (a b : List Byte) (j : Nat) :
    (a ++ b).getD j 0 = if j < a.length then a.getD j 0 else b.getD (j - a.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split <;> rfl

/-- `toInt (toByte x 4) 4 = x mod 2³²`. -/
theorem toInt_toByte4 (x : Nat) : toInt (toByte x 4) 4 = x % 2 ^ 32 := by
  simp [toInt, toByte, List.range_succ, BitVec.toNat_ofNat]
  omega

variable {a : Adrs}

theorem length_setTypeAndClear (h : a.length = 32) (Y : Nat) : (setTypeAndClear a Y).length = 32 := by
  rw [setTypeAndClear, length_setBytes (by simp [length_toByte, h]), h]
theorem length_setKeyPairAddress (h : a.length = 32) (i : Nat) : (setKeyPairAddress a i).length = 32 := by
  rw [setKeyPairAddress, length_setBytes (by simp [length_toByte, h]), h]
theorem length_setChainAddress (h : a.length = 32) (i : Nat) : (setChainAddress a i).length = 32 := by
  rw [setChainAddress, length_setBytes (by simp [length_toByte, h]), h]
theorem length_setTreeHeight (h : a.length = 32) (i : Nat) : (setTreeHeight a i).length = 32 := by
  rw [setTreeHeight, length_setBytes (by simp [length_toByte, h]), h]
theorem length_setTreeIndex (h : a.length = 32) (i : Nat) : (setTreeIndex a i).length = 32 := by
  rw [setTreeIndex, length_setBytes (by simp [length_toByte, h]), h]
theorem length_setHashAddress (h : a.length = 32) (i : Nat) : (setHashAddress a i).length = 32 := by
  rw [setHashAddress, length_setBytes (by simp [length_toByte, h]), h]

theorem getD_setTypeAndClear (h : a.length = 32) (Y j : Nat) :
    (setTypeAndClear a Y).getD j 0 = if j < 16 then a.getD j 0 else if j < 20 then (toByte Y 4).getD (j - 16) 0
      else if j < 32 then 0 else a.getD j 0 := by
  rw [setTypeAndClear, getD_setBytes (by simp [length_toByte, h])]
  simp only [List.length_append, length_toByte, getD_append, getD_toByte_zero]
  rcases (show j < 16 ∨ (16 ≤ j ∧ j < 20) ∨ (20 ≤ j ∧ j < 24) ∨ (24 ≤ j ∧ j < 28) ∨ (28 ≤ j ∧ j < 32) ∨ 32 ≤ j
    by omega) with hr | hr | hr | hr | hr | hr <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]

theorem getD_setKeyPairAddress (h : a.length = 32) (i j : Nat) :
    (setKeyPairAddress a i).getD j 0 = if j < 20 then a.getD j 0 else if j < 24 then (toByte i 4).getD (j - 20) 0
      else a.getD j 0 := by
  rw [setKeyPairAddress, getD_setBytes (by simp [length_toByte, h]), length_toByte]

theorem getD_setTreeHeight (h : a.length = 32) (i j : Nat) :
    (setTreeHeight a i).getD j 0 = if j < 24 then a.getD j 0 else if j < 28 then (toByte i 4).getD (j - 24) 0
      else a.getD j 0 := by
  rw [setTreeHeight, getD_setBytes (by simp [length_toByte, h]), length_toByte]

theorem getD_setTreeIndex (h : a.length = 32) (i j : Nat) :
    (setTreeIndex a i).getD j 0 = if j < 28 then a.getD j 0 else if j < 32 then (toByte i 4).getD (j - 28) 0
      else a.getD j 0 := by
  rw [setTreeIndex, getD_setBytes (by simp [length_toByte, h]), length_toByte]

/-- `setTypeAndClear` overwrites what a `setTypeAndClear` and a
`setKeyPairAddress` before it wrote. -/
theorem setTypeAndClear_setKeyPairAddress_setTypeAndClear (h : a.length = 32) (Y i Y' : Nat) :
    setTypeAndClear (setKeyPairAddress (setTypeAndClear a Y) i) Y' = setTypeAndClear a Y' := by
  have h1 := length_setTypeAndClear h Y
  have h2 := length_setKeyPairAddress h1 i
  apply ext_getD (by rw [length_setTypeAndClear h2, length_setTypeAndClear h])
  intro j hj
  rw [length_setTypeAndClear h2] at hj
  rw [getD_setTypeAndClear h2, getD_setTypeAndClear h, getD_setKeyPairAddress h1, getD_setTypeAndClear h]
  rcases (show j < 16 ∨ (16 ≤ j ∧ j < 20) ∨ (20 ≤ j ∧ j < 24) ∨ (24 ≤ j ∧ j < 28) ∨ (28 ≤ j ∧ j < 32) ∨ 32 ≤ j
    by omega) with hr | hr | hr | hr | hr | hr <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]

/-- A cleared address has tree height 0. -/
theorem setTreeHeight_setTypeAndClear_zero (h : a.length = 32) (Y : Nat) :
    setTreeHeight (setTypeAndClear a Y) 0 = setTypeAndClear a Y := by
  have h1 := length_setTypeAndClear h Y
  apply ext_getD (by rw [length_setTreeHeight h1, h1])
  intro j hj
  rw [length_setTreeHeight h1] at hj
  rw [getD_setTreeHeight h1, getD_setTypeAndClear h, getD_toByte_zero]
  rcases (show j < 16 ∨ (16 ≤ j ∧ j < 20) ∨ (20 ≤ j ∧ j < 24) ∨ (24 ≤ j ∧ j < 28) ∨ (28 ≤ j ∧ j < 32) ∨ 32 ≤ j
    by omega) with hr | hr | hr | hr | hr | hr <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]

/-- The tree index of an address whose tree index was set, then its height. -/
theorem getTreeIndex_setTreeHeight_setTreeIndex (h : a.length = 32) (t z : Nat) :
    getTreeIndex (setTreeHeight (setTreeIndex a t) z) = t % 2 ^ 32 := by
  have h1 := length_setTreeIndex h t
  have h2 := length_setTreeHeight h1 z
  have e : (setTreeHeight (setTreeIndex a t) z).drop 28 = toByte t 4 := by
    apply ext_getD (by rw [List.length_drop, h2, length_toByte])
    intro j hj
    rw [List.length_drop, h2] at hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
    rw [getD_setTreeHeight h1, getD_setTreeIndex h]
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right, Nat.add_sub_cancel_left]
  rw [getTreeIndex, e, toInt_toByte4]

/-- Setting the height, then the index, of an address whose height and index
were set before gives the address with only the new ones. -/
theorem setTreeIndex_setTreeHeight_idem (h : a.length = 32) (k t z t' : Nat) :
    setTreeIndex (setTreeHeight (setTreeIndex (setTreeHeight a k) t) z) t' = setTreeIndex (setTreeHeight a z) t' := by
  have h1 := length_setTreeHeight h k
  have h2 := length_setTreeIndex h1 t
  have h3 := length_setTreeHeight h2 z
  have h4 := length_setTreeHeight h z
  apply ext_getD (by rw [length_setTreeIndex h3, length_setTreeIndex h4])
  intro j hj
  rw [length_setTreeIndex h3] at hj
  rw [getD_setTreeIndex h3, getD_setTreeIndex h4, getD_setTreeHeight h2, getD_setTreeHeight h,
    getD_setTreeIndex h1, getD_setTreeHeight h]
  rcases (show j < 16 ∨ (16 ≤ j ∧ j < 20) ∨ (20 ≤ j ∧ j < 24) ∨ (24 ≤ j ∧ j < 28) ∨ (28 ≤ j ∧ j < 32) ∨ 32 ≤ j
    by omega) with hr | hr | hr | hr | hr | hr <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]

/-! ## Trees -/

/-- `x ⊕ 1`: `x + 1` for an even `x`, `x - 1` for an odd one. -/
theorem xor_one (x : Nat) : x ^^^ 1 = 2 * (x / 2) + (1 - x % 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero =>
    simp only [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, Nat.add_mod, Nat.mul_mod_right]
  | succ i =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have : (2 * (x / 2) + (1 - x % 2)) / 2 = x / 2 := by omega
    rw [this]; simp

/-- `⌊x / 2^(k+1)⌋ = ⌊⌊x / 2^k⌋ / 2⌋`. -/
theorem div_two_pow_succ (x k : Nat) : x / 2 ^ (k + 1) = x / 2 ^ k / 2 := by
  rw [Nat.pow_succ, Nat.div_div_eq_div_mul]

/-- A fold over `0, …, K - 1` whose `k`-th step takes `S k` to `S (k + 1)`
ends in `S K`. -/
theorem foldl_range_inv {α : Type} {f : α → Nat → α} {S : Nat → α} :
    ∀ {K : Nat}, (∀ k < K, f (S k) k = S (k + 1)) → (List.range K).foldl f (S 0) = S K
  | 0, _ => rfl
  | K + 1, h => by
    rw [List.range_succ, List.foldl_append, foldl_range_inv fun k hk => h k (by omega), List.foldl_cons,
      List.foldl_nil, h K (by omega)]

/-- Node `i` at height `z + 1` of an XMSS tree is `H` of its children. -/
theorem xmssNode_succ (skSeed pkSeed : List Byte) (adrs : Adrs) (i z : Nat) :
    xmssNode p skSeed i (z + 1) pkSeed adrs =
      H p pkSeed (setTreeIndex (setTreeHeight (setTypeAndClear adrs TREE) (z + 1)) i)
        (xmssNode p skSeed (2 * i) z pkSeed adrs ++ xmssNode p skSeed (2 * i + 1) z pkSeed adrs) := by
  rw [xmssNode]

/-- A leaf of an XMSS tree is a WOTS⁺ public key. -/
theorem xmssNode_zero (skSeed pkSeed : List Byte) (adrs : Adrs) (i : Nat) :
    xmssNode p skSeed i 0 pkSeed adrs = wotsPkGen p skSeed pkSeed (setKeyPairAddress (setTypeAndClear adrs WOTS_HASH) i) := by
  rw [xmssNode]

theorem xmssNode_length (hn : p.n ≤ 32) (skSeed pkSeed : List Byte) (adrs : Adrs) (i z : Nat) :
    (xmssNode p skSeed i z pkSeed adrs).length = p.n := by
  cases z with
  | zero => rw [xmssNode_zero]; exact wotsPkGen_length hn _ _ _
  | succ z => rw [xmssNode_succ]; exact H_length hn _ _ _

/-- The siblings of the path from leaf `idx`: the authentication path of
`xmss_sign` (Algorithm 10, lines 1–4). -/
theorem xmssSign_eq (M skSeed : List Byte) (idx : Nat) (pkSeed : List Byte) (adrs : Adrs) :
    xmssSign p M skSeed idx pkSeed adrs =
      wotsSign p M skSeed pkSeed (setKeyPairAddress (setTypeAndClear adrs WOTS_HASH) idx) ++
        (List.range p.hp).flatMap fun j => xmssNode p skSeed (idx / 2 ^ j ^^^ 1) j pkSeed adrs := rfl

/-- The root that an XMSS signature by leaf `idx` gives is the tree's root
(the signature's WOTS⁺ signature gives the leaf, `wotsPkFromSig_wotsSign`,
and its authentication path the nodes above it). -/
theorem xmssPkFromSig_xmssSign (hn : p.n ≤ 32) (M skSeed : List Byte) {idx : Nat} (hidx : idx < 2 ^ p.hp)
    (hidx32 : idx < 2 ^ 32) (pkSeed : List Byte) {adrs : Adrs} (ha : adrs.length = 32) :
    xmssPkFromSig p idx (xmssSign p M skSeed idx pkSeed adrs) M pkSeed adrs = xmssNode p skSeed 0 p.hp pkSeed adrs := by
  have hB := length_setTypeAndClear ha TREE
  have hsig := wotsSign_length hn M skSeed pkSeed (setKeyPairAddress (setTypeAndClear adrs WOTS_HASH) idx)
  have hauth : ∀ j < p.hp, (xmssNode p skSeed (idx / 2 ^ j ^^^ 1) j pkSeed adrs).length = p.n :=
    fun j _ => xmssNode_length hn _ _ _ _ _
  rw [xmssPkFromSig, xmssSign_eq, List.take_left' hsig, List.drop_left' hsig, wotsPkFromSig_wotsSign hn,
    setTypeAndClear_setKeyPairAddress_setTypeAndClear ha, ← xmssNode_zero]
  have e0 : (xmssNode p skSeed idx 0 pkSeed adrs, setTreeIndex (setTypeAndClear adrs TREE) idx) =
      (xmssNode p skSeed (idx / 2 ^ 0) 0 pkSeed adrs,
        setTreeIndex (setTreeHeight (setTypeAndClear adrs TREE) 0) (idx / 2 ^ 0)) := by
    simp only [Nat.pow_zero, Nat.div_one, setTreeHeight_setTypeAndClear_zero ha]
  dsimp only
  rw [e0]
  refine (congrArg Prod.fst (foldl_range_inv (K := p.hp) (S := fun k => (xmssNode p skSeed (idx / 2 ^ k) k pkSeed adrs,
    setTreeIndex (setTreeHeight (setTypeAndClear adrs TREE) k) (idx / 2 ^ k))) ?_)).trans ?_
  rotate_left
  · simp only [Nat.div_eq_of_lt hidx]
  intro k hk
  dsimp only
  have hq : idx / 2 ^ k < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hidx32
  rw [getTreeIndex_setTreeHeight_setTreeIndex (length_setTreeHeight hB k), Nat.mod_eq_of_lt hq,
    chunk_flatMap_range hauth hk, div_two_pow_succ, xmssNode_succ, xor_one]
  generalize idx / 2 ^ k = q
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · simp only [h, ↓reduceIte, setTreeIndex_setTreeHeight_idem hB]
    rw [show 2 * (q / 2) = q by omega, Nat.sub_zero]
  · simp only [h, show ¬ (1 = 0) by decide, ↓reduceIte, setTreeIndex_setTreeHeight_idem hB]
    rw [show (q - 1) / 2 = q / 2 by omega, show 2 * (q / 2) + (1 - 1) = 2 * (q / 2) by omega,
      show q = 2 * (q / 2) + 1 by omega]
    simp only [Nat.mul_add_div (by decide : 0 < 2), show 1 / 2 = 0 by decide, Nat.add_zero]

/-- Node `i` at height `z + 1` of the FORS trees is `H` of its children. -/
theorem forsNode_succ (skSeed pkSeed : List Byte) (adrs : Adrs) (i z : Nat) :
    forsNode p skSeed i (z + 1) pkSeed adrs =
      H p pkSeed (setTreeIndex (setTreeHeight adrs (z + 1)) i)
        (forsNode p skSeed (2 * i) z pkSeed adrs ++ forsNode p skSeed (2 * i + 1) z pkSeed adrs) := by
  rw [forsNode]

/-- A leaf of the FORS trees is `F` of its private key value. -/
theorem forsNode_zero (skSeed pkSeed : List Byte) (adrs : Adrs) (i : Nat) :
    forsNode p skSeed i 0 pkSeed adrs =
      F p pkSeed (setTreeIndex (setTreeHeight adrs 0) i) (forsSkGen p skSeed pkSeed adrs i) := by
  rw [forsNode]

theorem forsNode_length (hn : p.n ≤ 32) (skSeed pkSeed : List Byte) (adrs : Adrs) (i z : Nat) :
    (forsNode p skSeed i z pkSeed adrs).length = p.n := by
  cases z with
  | zero => rw [forsNode_zero]; exact F_length hn _ _ _
  | succ z => rw [forsNode_succ]; exact H_length hn _ _ _

/-- The part of a FORS signature for tree `i`: its private key value, then its
authentication path (Algorithm 16, lines 3–8). -/
def forsSigPart (md skSeed pkSeed : List Byte) (adrs : Adrs) (i : Nat) : List Byte :=
  let idx := (base2b md p.a p.k).getD i 0
  forsSkGen p skSeed pkSeed adrs (i * 2 ^ p.a + idx) ++
    (List.range p.a).flatMap fun j => forsNode p skSeed (i * 2 ^ (p.a - j) + (idx / 2 ^ j ^^^ 1)) j pkSeed adrs

theorem forsSign_eq (md skSeed pkSeed : List Byte) (adrs : Adrs) :
    forsSign p md skSeed pkSeed adrs = (List.range p.k).flatMap (forsSigPart (p := p) md skSeed pkSeed adrs) := rfl

theorem forsSigPart_length (hn : p.n ≤ 32) (md skSeed pkSeed : List Byte) (adrs : Adrs) (i : Nat) :
    (forsSigPart (p := p) md skSeed pkSeed adrs i).length = (p.a + 1) * p.n := by
  rw [forsSigPart, List.length_append, forsSkGen, prf_length hn,
    length_flatMap_range (L := p.n) fun j _ => forsNode_length hn _ _ _ _ _, Nat.add_mul, Nat.one_mul, Nat.mul_comm,
    Nat.add_comm]

/-- `⌊(i·2ᵃ + x) / 2ʲ⌋ = i·2^(a-j) + ⌊x / 2ʲ⌋` for `j ≤ a`. -/
theorem div_two_pow_of_le {i a x j : Nat} (hj : j ≤ a) : (i * 2 ^ a + x) / 2 ^ j = i * 2 ^ (a - j) + x / 2 ^ j := by
  rw [show i * 2 ^ a = i * 2 ^ (a - j) * 2 ^ j by rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel hj],
    Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), Nat.add_comm]

/-- The FORS public key a FORS signature of `md` gives is `T_k` of the
trees' roots (each tree's private key value gives its leaf, and its
authentication path the nodes above it). Tree `i`'s root is node `i` at
height `a`. -/
theorem forsPkFromSig_forsSign (hn : p.n ≤ 32) (hk : p.k * 2 ^ p.a ≤ 2 ^ 32) (md skSeed pkSeed : List Byte)
    {adrs : Adrs} (ha : adrs.length = 32) :
    forsPkFromSig p (forsSign p md skSeed pkSeed adrs) md pkSeed adrs =
      T p pkSeed (setKeyPairAddress (setTypeAndClear adrs FORS_ROOTS) (getKeyPairAddress adrs))
        ((List.range p.k).flatMap fun i => forsNode p skSeed i p.a pkSeed adrs) := by
  rw [forsPkFromSig]
  refine congrArg (T p pkSeed _) (flatMap_range_congr fun i hi => ?_)
  dsimp only
  have hL := forsSigPart_length (p := p) hn md skSeed pkSeed adrs
  have hidx := base2b_getD_lt md p.a p.k i
  generalize hI : (base2b md p.a p.k).getD i 0 = idx at hidx
  have hD : (forsSign p md skSeed pkSeed adrs).drop (p.n * (i * (p.a + 1))) =
      forsSigPart (p := p) md skSeed pkSeed adrs i ++
        (List.range (p.k - i - 1)).flatMap fun j => forsSigPart (p := p) md skSeed pkSeed adrs (i + 1 + j) := by
    rw [show p.n * (i * (p.a + 1)) = (p.a + 1) * p.n * i by
      rw [Nat.mul_comm (p.a + 1) p.n, Nat.mul_assoc, Nat.mul_comm (p.a + 1) i], forsSign_eq,
      drop_flatMap_range (fun j _ => hL j) hi]
  have hsk : (forsSkGen p skSeed pkSeed adrs (i * 2 ^ p.a + idx)).length = p.n := by
    rw [forsSkGen]; exact prf_length hn _ _ _
  have hauthL : ((List.range p.a).flatMap fun j =>
      forsNode p skSeed (i * 2 ^ (p.a - j) + (idx / 2 ^ j ^^^ 1)) j pkSeed adrs).length = p.a * p.n := by
    rw [length_flatMap_range (L := p.n) fun j _ => forsNode_length hn _ _ _ _ _, Nat.mul_comm]
  have hpart : forsSigPart (p := p) md skSeed pkSeed adrs i = forsSkGen p skSeed pkSeed adrs (i * 2 ^ p.a + idx) ++
      (List.range p.a).flatMap fun j => forsNode p skSeed (i * 2 ^ (p.a - j) + (idx / 2 ^ j ^^^ 1)) j pkSeed adrs := by
    rw [forsSigPart, hI]
  rw [hpart, List.append_assoc] at hD
  have eSk : chunk (forsSign p md skSeed pkSeed adrs) p.n (i * (p.a + 1)) = forsSkGen p skSeed pkSeed adrs (i * 2 ^ p.a + idx) := by
    rw [chunk, hD, List.take_left' hsk]
  have eAuth : ((forsSign p md skSeed pkSeed adrs).drop (p.n * (i * (p.a + 1) + 1))).take (p.a * p.n) =
      (List.range p.a).flatMap fun j => forsNode p skSeed (i * 2 ^ (p.a - j) + (idx / 2 ^ j ^^^ 1)) j pkSeed adrs := by
    rw [Nat.mul_add, Nat.mul_one, ← List.drop_drop, hD, List.drop_left' hsk, List.take_left' hauthL]
  rw [eSk, eAuth, ← forsNode_zero]
  have hN : i * 2 ^ p.a + idx < 2 ^ 32 := by
    have : i * 2 ^ p.a + idx < p.k * 2 ^ p.a := by
      have := Nat.mul_le_mul_right (2 ^ p.a) (show i + 1 ≤ p.k by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    omega
  generalize hNdef : i * 2 ^ p.a + idx = N at hN
  have e0 : (forsNode p skSeed N 0 pkSeed adrs, setTreeIndex (setTreeHeight adrs 0) N) =
      (forsNode p skSeed (N / 2 ^ 0) 0 pkSeed adrs, setTreeIndex (setTreeHeight adrs 0) (N / 2 ^ 0)) := by
    simp only [Nat.pow_zero, Nat.div_one]
  rw [e0]
  refine (congrArg Prod.fst (foldl_range_inv (K := p.a) (S := fun j => (forsNode p skSeed (N / 2 ^ j) j pkSeed adrs,
    setTreeIndex (setTreeHeight adrs j) (N / 2 ^ j))) ?_)).trans ?_
  rotate_left
  · dsimp only
    rw [← hNdef, div_two_pow_of_le (Nat.le_refl _), Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt hidx,
      Nat.add_zero]
  intro j hj
  dsimp only
  have hq : N / 2 ^ j < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hN
  have hlen := length_setTreeHeight ha j
  rw [getTreeIndex_setTreeHeight_setTreeIndex hlen, Nat.mod_eq_of_lt hq,
    chunk_flatMap_range (fun j _ => forsNode_length hn _ _ _ _ _) hj, div_two_pow_succ, forsNode_succ, xor_one,
    setTreeIndex_setTreeHeight_idem ha, setTreeIndex_setTreeHeight_idem ha]
  have hNj : N / 2 ^ j = 2 * (i * 2 ^ (p.a - j - 1)) + idx / 2 ^ j := by
    rw [← hNdef, div_two_pow_of_le (Nat.le_of_lt hj),
      show p.a - j = p.a - j - 1 + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (i * _) 2,
      show p.a - j - 1 + 1 - 1 = p.a - j - 1 by omega]
  have hij : i * 2 ^ (p.a - j) = 2 * (i * 2 ^ (p.a - j - 1)) := by
    rw [show p.a - j = p.a - j - 1 + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (i * _) 2,
      show p.a - j - 1 + 1 - 1 = p.a - j - 1 by omega]
  rw [hNj, hij]
  generalize i * 2 ^ (p.a - j - 1) = c
  generalize idx / 2 ^ j = r
  rcases Nat.mod_two_eq_zero_or_one r with h | h
  · simp only [h, ↓reduceIte, Nat.sub_zero]
    rw [show (2 * c + r) / 2 = c + r / 2 by omega, show 2 * (c + r / 2) = 2 * c + r by omega,
      show 2 * c + (2 * (r / 2) + 1) = 2 * c + r + 1 by omega]
  · simp only [h, show ¬ (1 = 0) by decide, ↓reduceIte, Nat.sub_self, Nat.add_zero]
    rw [show (2 * c + r - 1) / 2 = c + r / 2 by omega, show (2 * c + r) / 2 = c + r / 2 by omega,
      show 2 * (c + r / 2) = 2 * c + 2 * (r / 2) by omega, show 2 * c + 2 * (r / 2) + 1 = 2 * c + r by omega]

/-! ## Subtrees and the addresses the trees depend on -/

/-- The tree of height `r` above the nodes `f v` at height `s` of an XMSS tree:
node `j` of it at height `r` (node `j` at height `s + r` of the XMSS tree). -/
def xmssSubtree (pkSeed : List Byte) (adrs : Adrs) (f : Nat → List Byte) (s : Nat) : (j r : Nat) → List Byte
  | j, 0 => f j
  | j, r + 1 =>
    H p pkSeed (setTreeIndex (setTreeHeight (setTypeAndClear adrs TREE) (s + r + 1)) j)
      (xmssSubtree pkSeed adrs f s (2 * j) r ++ xmssSubtree pkSeed adrs f s (2 * j + 1) r)

/-- Node `j` at height `s + r` of an XMSS tree, from the nodes at height `s`
below it. -/
theorem xmssNode_subtree (skSeed pkSeed : List Byte) (adrs : Adrs) (s : Nat) :
    ∀ (r j : Nat), xmssNode p skSeed j (s + r) pkSeed adrs =
      xmssSubtree (p := p) pkSeed adrs (fun v => xmssNode p skSeed v s pkSeed adrs) s j r
  | 0, j => rfl
  | r + 1, j => by
    rw [← Nat.add_assoc, xmssNode_succ, xmssSubtree, xmssNode_subtree skSeed pkSeed adrs s r (2 * j),
      xmssNode_subtree skSeed pkSeed adrs s r (2 * j + 1)]

/-- The tree of height `r` above the nodes `f v` at height `s` of the FORS
trees: node `j` of it at height `r` (node `j` at height `s + r`). -/
def forsSubtree (pkSeed : List Byte) (adrs : Adrs) (f : Nat → List Byte) (s : Nat) : (j r : Nat) → List Byte
  | j, 0 => f j
  | j, r + 1 =>
    H p pkSeed (setTreeIndex (setTreeHeight adrs (s + r + 1)) j)
      (forsSubtree pkSeed adrs f s (2 * j) r ++ forsSubtree pkSeed adrs f s (2 * j + 1) r)

/-- Node `j` at height `s + r` of the FORS trees, from the nodes at height
`s` below it. -/
theorem forsNode_subtree (skSeed pkSeed : List Byte) (adrs : Adrs) (s : Nat) :
    ∀ (r j : Nat), forsNode p skSeed j (s + r) pkSeed adrs =
      forsSubtree (p := p) pkSeed adrs (fun v => forsNode p skSeed v s pkSeed adrs) s j r
  | 0, j => rfl
  | r + 1, j => by
    rw [← Nat.add_assoc, forsNode_succ, forsSubtree, forsNode_subtree skSeed pkSeed adrs s r (2 * j),
      forsNode_subtree skSeed pkSeed adrs s r (2 * j + 1)]

/-- `setTypeAndClear` keeps only the layer and tree addresses (bytes 0–15). -/
theorem setTypeAndClear_congr {a a' : Adrs} (h : a.length = 32) (h' : a'.length = 32) (ht : a.take 16 = a'.take 16)
    (Y : Nat) : setTypeAndClear a Y = setTypeAndClear a' Y := by
  apply ext_getD (by rw [length_setTypeAndClear h, length_setTypeAndClear h'])
  intro j hj
  rw [length_setTypeAndClear h] at hj
  rw [getD_setTypeAndClear h, getD_setTypeAndClear h']
  by_cases hj16 : j < 16
  · simp only [hj16, ↓reduceIte]
    have := congrArg (fun l => l.getD j 0) ht
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hj16, ↓reduceIte] at this
    simpa only [List.getD_eq_getElem?_getD] using this
  · simp only [hj16, hj, ↓reduceIte]

/-- A node of an XMSS tree depends only on the layer and tree addresses of
`ADRS` (bytes 0–15). -/
theorem xmssNode_congr (skSeed pkSeed : List Byte) {a a' : Adrs} (h : a.length = 32) (h' : a'.length = 32)
    (ht : a.take 16 = a'.take 16) : ∀ (z i : Nat), xmssNode p skSeed i z pkSeed a = xmssNode p skSeed i z pkSeed a'
  | 0, i => by rw [xmssNode_zero, xmssNode_zero, setTypeAndClear_congr h h' ht]
  | z + 1, i => by
    rw [xmssNode_succ, xmssNode_succ, setTypeAndClear_congr h h' ht, xmssNode_congr skSeed pkSeed h h' ht z (2 * i),
      xmssNode_congr skSeed pkSeed h h' ht z (2 * i + 1)]

end VG.Proof.SlhDsa
