import VerifiedGarbage.Spec.ChaCha20
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.Spec`. -/
section

/-!
# Facts about the ChaCha20 specification
-/

namespace VG.Proof.ChaCha20

open VG.Spec.ChaCha20 (Word quarterRound qround)

abbrev CState := Spec.ChaCha20.State

theorem rotateLeft_eq (x : Word) {k : Nat} (hk : 0 < k) (hk' : k < 32) :
    x.rotateLeft k = x.rotateRight (32 - k) := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_rotateRight]
  split <;> split <;> first | (exfalso; omega) | exact getElem_congr rfl (by omega) _

/-- `quarterRound` with the rotations the code does. -/
theorem quarterRound_eq (a b c d : Word) : quarterRound a b c d =
    let a := a + b; let d := (d ^^^ a).rotateRight 16
    let c := c + d; let b := (b ^^^ c).rotateRight 20
    let a := a + b; let d := (d ^^^ a).rotateRight 24
    let c := c + d; let b := (b ^^^ c).rotateRight 25
    (a, b, c, d) := by
  simp only [quarterRound, VG.Proof.ChaCha20.rotateLeft_eq _ (show 0 < 16 by decide) (by decide),
    VG.Proof.ChaCha20.rotateLeft_eq _ (show 0 < 12 by decide) (by decide), VG.Proof.ChaCha20.rotateLeft_eq _ (show 0 < 8 by decide) (by decide),
    VG.Proof.ChaCha20.rotateLeft_eq _ (show 0 < 7 by decide) (by decide)]

theorem qround_get (v : VG.Proof.ChaCha20.CState) (x y z w : Fin 16) (k : Nat) (hk : k < 16) :
    (qround v x y z w)[k]'hk =
      if w.1 = k then (quarterRound (v[x]'x.isLt) (v[y]'y.isLt) (v[z]'z.isLt) (v[w]'w.isLt)).2.2.2
      else if z.1 = k then (quarterRound (v[x]'x.isLt) (v[y]'y.isLt) (v[z]'z.isLt) (v[w]'w.isLt)).2.2.1
      else if y.1 = k then (quarterRound (v[x]'x.isLt) (v[y]'y.isLt) (v[z]'z.isLt) (v[w]'w.isLt)).2.1
      else if x.1 = k then (quarterRound (v[x]'x.isLt) (v[y]'y.isLt) (v[z]'z.isLt) (v[w]'w.isLt)).1
      else v[k]'hk := by
  simp only [qround, Vector.getElem_set]

end VG.Proof.ChaCha20

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.Keystream`. -/
section

/-!
# Facts about the ChaCha20 keystream

The keystream byte by byte (`keystream_getD`), the bytes of a state in memory
(`serialize_stateAt`), and incrementing the counter of a state in memory
(`stateAt_writeW_counter`).
-/

namespace VG.Proof.ChaCha20

open VG.Spec.ChaCha20 (Word stateAt keystream serialize block bytesAt)

/-- The state `S` with its counter (word 12) advanced by `j`, modulo 2³². -/
def ctr (S : VG.Proof.ChaCha20.CState) (j : Nat) : VG.Proof.ChaCha20.CState := S.set 12 (S[12] + BitVec.ofNat 32 j)

theorem ctr_zero (S : VG.Proof.ChaCha20.CState) : VG.Proof.ChaCha20.ctr S 0 = S := by
  apply Vector.ext; intro i hi
  simp only [VG.Proof.ChaCha20.ctr, Vector.getElem_set]
  split <;> simp_all

theorem ctr_succ (S : VG.Proof.ChaCha20.CState) (j : Nat) :
    (VG.Proof.ChaCha20.ctr S j).set 12 ((VG.Proof.ChaCha20.ctr S j)[12] + 1) = VG.Proof.ChaCha20.ctr S (j + 1) := by
  simp only [VG.Proof.ChaCha20.ctr, Vector.set_set, Vector.getElem_set_self, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

/-- Element `k` of a concatenation of lists of length `n`. -/
theorem getD_flatMap {α β : Type} (f : α → List β) {n : Nat} (hf : ∀ a, (f a).length = n) (a₀ : α)
    (l : List α) {k : Nat} (hk : k < n * l.length) (d : β) :
    (l.flatMap f).getD k d = (f (l.getD (k / n) a₀)).getD (k % n) d := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hk
    rw [List.flatMap_cons]
    by_cases h : k < n
    · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      have h' : k < (f a).length := by rw [hf]; exact h
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h',
        List.getElem?_cons_zero, Option.getD_some]
    · have h' : (f a).length ≤ k := by rw [hf]; omega
      have e1 : (f a ++ l.flatMap f).getD k d = (l.flatMap f).getD (k - n) d := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h', hf]
      have hk' : k - n < n * l.length := by
        simp only [List.length_cons, Nat.mul_add_one] at hk; omega
      have e2 : k / n = (k - n) / n + 1 := Nat.div_eq_sub_div hn (by omega)
      have e3 : k % n = (k - n) % n := Nat.mod_eq_sub_mod (by omega)
      rw [e1, ih hk', e2, e3, List.getD_cons_succ]

theorem length_flatMap_const {α β : Type} (f : α → List β) {n : Nat} (hf : ∀ a, (f a).length = n)
    (l : List α) : (l.flatMap f).length = n * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.length_append, ih, hf, List.length_cons, Nat.mul_add_one,
      Nat.add_comm]

theorem length_serialize (S : VG.Proof.ChaCha20.CState) : (serialize S).length = 64 := by
  rw [serialize, VG.Proof.ChaCha20.length_flatMap_const _ (n := 4) (fun _ => rfl), Vector.length_toList]

/-- Byte `i` of a serialized state: byte `i % 4` of word `i / 4`. -/
theorem serialize_getD (S : VG.Proof.ChaCha20.CState) {i : Nat} (hi : i < 64) :
    (serialize S).getD i 0 = (S[i / 4]'(by omega)).extractLsb' (8 * (i % 4)) 8 := by
  rw [serialize, VG.Proof.ChaCha20.getD_flatMap _ (n := 4) (fun _ => rfl) 0 _ (by rw [Vector.length_toList]; omega)]
  have h4 : i % 4 < 4 := Nat.mod_lt _ (by omega)
  have e : S.toList.getD (i / 4) 0 = S[i / 4] := by
    simp [List.getD_eq_getElem?_getD, show i / 4 < 16 by omega]
  rw [e]; clear e
  generalize S[i / 4] = w
  generalize i % 4 = j at h4 ⊢
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with h | h | h | h <;> subst h <;> rfl

/-- The bytes of a state in memory. -/
theorem serialize_stateAt (m : Mem) (p : Addr) {i : Nat} (hi : i < 64) :
    (serialize (stateAt m p)).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  rw [VG.Proof.ChaCha20.serialize_getD _ hi]
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← Mem.readW_byte _ _ (Nat.mod_lt _ (by omega)), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 3
  omega

/-- The keystream, byte by byte. -/
theorem keystream_getD (S : VG.Proof.ChaCha20.CState) {n k : Nat} (hk : k < n) :
    (keystream S n).getD k 0 = (serialize (block (VG.Proof.ChaCha20.ctr S (k / 64)))).getD (k % 64) 0 := by
  simp only [keystream]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk, ← List.getD_eq_getElem?_getD]
  rw [VG.Proof.ChaCha20.getD_flatMap _ (n := 64) (fun _ => VG.Proof.ChaCha20.length_serialize _) 0 _
    (by rw [List.length_range]; omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_range (show k / 64 < (n + 63) / 64 by omega),
    Option.getD_some]
  rfl

theorem length_keystream (S : VG.Proof.ChaCha20.CState) (n : Nat) : (keystream S n).length = n := by
  simp only [keystream, List.length_take]
  rw [VG.Proof.ChaCha20.length_flatMap_const _ (n := 64) (fun _ => VG.Proof.ChaCha20.length_serialize _), List.length_range]
  omega

/-- XORing the keystream into data in memory, byte by byte. -/
theorem bytesAt_xor {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : ∀ k < n, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0) :
    bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks := by
  apply List.ext_getElem
  · simp [bytesAt, hks]
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
    rw [h k h₁, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

end VG.Proof.ChaCha20

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.Stream`. -/
section

/-!
# The streaming state of ChaCha20

Untrusted: everything here is checked by Lean. What the implementations of
`vg_chacha20_init`, `vg_chacha20_set_nonce` and `vg_chacha20_apply` on every
target need of the streaming state (`keyAt`, `leftAt`, `restAt`), stated on
memory byte by byte, so that each target's proof only describes the bytes its
code writes:

* `restAt_getD`: the keystream left, byte by byte;
* `restAt_of_bytes`, `keyAt_of_bytes`: a state whose first 64 bytes are the
  constants, a key and a nonce, and with `64 × (2³² − c)` bytes left,
  represents the whole keystream of that key and nonce (`init`,
  `set_nonce`);
* `apply_data`, `apply_rest`: what `apply` does, in three steps: the bytes
  left in the buffered block (`h` of them), then whole blocks from the
  16-word state (`nb` of them), then the first `t` bytes of one more block,
  which becomes the buffered block.
-/

namespace VG.Proof.ChaCha20

open VG.Spec.ChaCha20 (Word stateAt keystream keystreamOf serialize block bytesAt keyAt leftAt
  restAt wordLE chacha20Block initState constants)

theorem ctr_ctr (S : VG.Proof.ChaCha20.CState) (a b : Nat) : VG.Proof.ChaCha20.ctr (VG.Proof.ChaCha20.ctr S a) b = VG.Proof.ChaCha20.ctr S (a + b) := by
  simp only [VG.Proof.ChaCha20.ctr, Vector.set_set, Vector.getElem_set_self, BitVec.ofNat_add, BitVec.add_assoc]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_getD (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hk]

theorem length_restAt (m : Mem) (p : Addr) : (restAt m p).length = leftAt m p := by
  simp only [restAt, List.length_append, VG.Proof.ChaCha20.length_bytesAt, VG.Proof.ChaCha20.length_keystream]
  omega

/-- The keystream left, byte by byte: the last `n % 64` bytes of the
buffered block, then the blocks of the 16-word state. -/
theorem restAt_getD (m : Mem) (p : Addr) {k : Nat} (hk : k < leftAt m p) :
    (restAt m p).getD k 0 =
      if k < leftAt m p % 64 then m (p + BitVec.ofNat 64 (128 - leftAt m p % 64 + k))
      else (serialize (block (VG.Proof.ChaCha20.ctr (stateAt m p) ((k - leftAt m p % 64) / 64)))).getD
        ((k - leftAt m p % 64) % 64) 0 := by
  have hn := Nat.mod_lt (leftAt m p) (by decide : 64 > 0)
  simp only [restAt, List.getD_eq_getElem?_getD]
  split
  · rename_i h
    rw [List.getElem?_append_left (by rw [VG.Proof.ChaCha20.length_bytesAt]; exact h), ← List.getD_eq_getElem?_getD,
      VG.Proof.ChaCha20.bytesAt_getD _ _ h, Offset.add_add]
  · rename_i h
    rw [List.getElem?_append_right (by rw [VG.Proof.ChaCha20.length_bytesAt]; omega), VG.Proof.ChaCha20.length_bytesAt,
      ← List.getD_eq_getElem?_getD, VG.Proof.ChaCha20.keystream_getD _ (by omega), List.getD_eq_getElem?_getD]

/-! ## Words and bytes -/

/-- Two words with the same bytes are equal. -/
theorem word_ext {x y : Word} (h : ∀ i < 4, x.extractLsb' (8 * i) 8 = y.extractLsb' (8 * i) 8) :
    x = y := by
  ext j hj
  have := congrArg (·.getLsbD (j % 8)) (h (j / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 by omega, decide_true,
    Bool.true_and] at this
  rw [show 8 * (j / 8) + j % 8 = j by omega] at this
  simpa [BitVec.getLsbD_eq_getElem hj] using this

/-- Byte `i` of a little-endian word of a byte string. -/
theorem wordLE_byte (bs : List Byte) (j : Nat) {i : Nat} (hi : i < 4) :
    (wordLE bs j).extractLsb' (8 * i) 8 = bs.getD (4 * j + i) 0 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [wordLE, Nat.add_zero]
    generalize bs.getD (4 * j + 3) 0 = a
    generalize bs.getD (4 * j + 2) 0 = b
    generalize bs.getD (4 * j + 1) 0 = c
    generalize bs.getD (4 * j) 0 = d
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
    repeat' split
    all_goals first | (exfalso; omega) | (rw [BitVec.getLsbD_eq_getElem (by omega)]; congr 1; omega)

/-- Word `j` of the 16-word state in memory, from its bytes. -/
theorem stateAt_getElem (m : Mem) (p : Addr) {j : Nat} (hj : j < 16) {bs : List Byte}
    (h : ∀ i < 4, m (p + BitVec.ofNat 64 (4 * j + i)) = bs.getD (4 * j + i) 0) :
    (stateAt m p)[j] = wordLE bs j := by
  simp only [stateAt, Vector.getElem_ofFn]
  refine VG.Proof.ChaCha20.word_ext fun i hi => ?_
  rw [VG.Proof.ChaCha20.wordLE_byte _ _ hi, ← h i hi, ← Offset.add_add, Mem.readW_byte m (p + BitVec.ofNat 64 (4 * j)) hi]

/-- A byte of the key, from the state's words 4–11. -/
theorem key_byte (m : Mem) (p : Addr) {i : Nat} (hi : i < 32) :
    m (p + 16 + BitVec.ofNat 64 i) =
      ((stateAt m p)[4 + i / 4]'(by omega)).extractLsb' (8 * (i % 4)) 8 := by
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← Mem.readW_byte m _ (Nat.mod_lt _ (by decide)), Offset.add_add,
    show (p + 16 : Addr) = p + BitVec.ofNat 64 16 from rfl, Offset.add_add,
    show 16 + i = 4 * (4 + i / 4) + i % 4 by omega]

/-- The key is words 4–11 of the 16-word state. -/
theorem keyAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ i (hi : 4 ≤ i ∧ i < 12), (stateAt m' p)[i]'(by omega) = (stateAt m p)[i]'(by omega)) :
    keyAt m' p = keyAt m p := by
  simp only [keyAt, bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [VG.Proof.ChaCha20.key_byte m' p hi, VG.Proof.ChaCha20.key_byte m p hi, h _ ⟨by omega, by omega⟩]

/-- Advancing the counter keeps the key. -/
theorem keyAt_of_ctr {m m' : Mem} {p : Addr} {j : Nat} (h : stateAt m' p = VG.Proof.ChaCha20.ctr (stateAt m p) j) :
    keyAt m' p = keyAt m p :=
  VG.Proof.ChaCha20.keyAt_congr fun i hi => by
    rw [h]; simp only [VG.Proof.ChaCha20.ctr, Vector.getElem_set, show ¬ (12 = i) from by omega, ↓reduceIte]

/-- A state whose first 136 bytes are unchanged represents the same key and
keystream. -/
theorem stream_congr {m m' : Mem} {p : Addr}
    (h : ∀ i < 136, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    keyAt m' p = keyAt m p ∧ restAt m' p = restAt m p ∧ leftAt m' p = leftAt m p := by
  have hb : ∀ a n, a + n ≤ 136 → bytesAt m' (p + BitVec.ofNat 64 a) n = bytesAt m (p + BitVec.ofNat 64 a) n :=
    fun a n hn => List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      simpa only [Offset.add_add] using h (a + i) (by omega)
  have hw : ∀ a w, a + w / 8 ≤ 136 → m'.readW (p + BitVec.ofNat 64 a) w = m.readW (p + BitVec.ofNat 64 a) w :=
    fun a w hn => Mem.readW_congr fun i hi => by
      simpa only [Offset.add_add] using h (a + i) (by omega)
  have hl : leftAt m' p = leftAt m p := by
    simp only [leftAt]; rw [show (p + 128 : Addr) = p + BitVec.ofNat 64 128 from rfl, hw _ _ (by decide)]
  have hs : stateAt m' p = stateAt m p := by
    apply Vector.ext; intro i hi
    simp only [stateAt, Vector.getElem_ofFn]
    exact hw _ _ (by omega)
  refine ⟨by simp only [keyAt]; exact hb 16 32 (by decide), ?_, hl⟩
  simp only [restAt, hl, hs]
  rw [hb _ _ (by omega)]

/-! ## Starting a keystream -/

/-- The bytes of the constants `"expand 32-byte k"`, little-endian. -/
def sigma : List Byte :=
  [0x65, 0x78, 0x70, 0x61, 0x6e, 0x64, 0x20, 0x33, 0x32, 0x2d, 0x62, 0x79, 0x74, 0x65, 0x20, 0x6b]

theorem getD_append_left {xs ys : List Byte} {n : Nat} (h : n < xs.length) (d : Byte) :
    (xs ++ ys).getD n d = xs.getD n d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {xs ys : List Byte} {n : Nat} (h : xs.length ≤ n) (d : Byte) :
    (xs ++ ys).getD n d = ys.getD (n - xs.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem wordLE_append_left {xs ys : List Byte} {i : Nat} (h : 4 * i + 4 ≤ xs.length) :
    wordLE (xs ++ ys) i = wordLE xs i := by
  simp only [wordLE, VG.Proof.ChaCha20.getD_append_left (show 4 * i + 3 < xs.length by omega),
    VG.Proof.ChaCha20.getD_append_left (show 4 * i + 2 < xs.length by omega),
    VG.Proof.ChaCha20.getD_append_left (show 4 * i + 1 < xs.length by omega),
    VG.Proof.ChaCha20.getD_append_left (show 4 * i < xs.length by omega)]

theorem wordLE_append_right {xs ys : List Byte} {a i : Nat} (hl : xs.length = 4 * a) (h : a ≤ i) :
    wordLE (xs ++ ys) i = wordLE ys (i - a) := by
  simp only [wordLE, VG.Proof.ChaCha20.getD_append_right (show xs.length ≤ 4 * i + 3 by omega),
    VG.Proof.ChaCha20.getD_append_right (show xs.length ≤ 4 * i + 2 by omega),
    VG.Proof.ChaCha20.getD_append_right (show xs.length ≤ 4 * i + 1 by omega),
    VG.Proof.ChaCha20.getD_append_right (show xs.length ≤ 4 * i by omega), hl,
    show 4 * i + 3 - 4 * a = 4 * (i - a) + 3 by omega, show 4 * i + 2 - 4 * a = 4 * (i - a) + 2 by omega,
    show 4 * i + 1 - 4 * a = 4 * (i - a) + 1 by omega, show 4 * i - 4 * a = 4 * (i - a) by omega]

theorem wordLE_drop (xs : List Byte) (i : Nat) : wordLE (xs.drop 4) i = wordLE xs (i + 1) := by
  simp only [wordLE, List.getD_eq_getElem?_getD, List.getElem?_drop,
    show 4 + (4 * i + 3) = 4 * (i + 1) + 3 by omega, show 4 + (4 * i + 2) = 4 * (i + 1) + 2 by omega,
    show 4 + (4 * i + 1) = 4 * (i + 1) + 1 by omega, show 4 + 4 * i = 4 * (i + 1) by omega]

theorem sigma_words : ∀ i < 4, wordLE VG.Proof.ChaCha20.sigma i = constants.getD i 0 := by decide

theorem length_sigma : sigma.length = 16 := rfl

/-- A state whose 16-word state is the constants, the key `key` and the
nonce `nonce`, byte by byte, and with `64 × (2³² − c)` bytes left (`c` the
initial block counter, the first word of the nonce), represents the whole
keystream of `key` and `nonce`. -/
theorem restAt_of_bytes {m : Mem} {p : Addr} {key nonce : List Byte} (hk : key.length = 32)
    (hb : ∀ i < 64, m (p + BitVec.ofNat 64 i) = (VG.Proof.ChaCha20.sigma ++ key ++ nonce).getD i 0)
    (hl : leftAt m p = 64 * (2 ^ 32 - (wordLE nonce 0).toNat)) :
    restAt m p = keystreamOf key nonce := by
  have hc := (wordLE nonce 0).isLt
  have hw : ∀ i (hi : i < 16), (stateAt m p)[i] = wordLE (VG.Proof.ChaCha20.sigma ++ key ++ nonce) i :=
    fun i hi => VG.Proof.ChaCha20.stateAt_getElem m p hi fun r hr => hb _ (by omega)
  have l48 : (VG.Proof.ChaCha20.sigma ++ key).length = 4 * 12 := by rw [List.length_append, VG.Proof.ChaCha20.length_sigma, hk]
  have l16 : sigma.length = 4 * 4 := VG.Proof.ChaCha20.length_sigma
  have hS : ∀ j : Nat, (stateAt m p).set 12 ((stateAt m p)[12] + BitVec.ofNat 32 j) =
      initState key (wordLE nonce 0 + BitVec.ofNat 32 j) (nonce.drop 4) := by
    intro j
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_set, initState, Vector.getElem_ofFn]
    by_cases e : i = 12
    · subst e
      simp only [↓reduceIte, show ¬ (12 < 4) by decide, show ¬ (12 < 12) by decide, hw 12 hi,
        VG.Proof.ChaCha20.wordLE_append_right l48 (Nat.le_refl 12)]
    · rw [hw i hi]
      by_cases h4 : i < 4
      · simp only [show ¬ (12 = i) by omega, h4, ↓reduceIte]
        rw [VG.Proof.ChaCha20.wordLE_append_left (xs := VG.Proof.ChaCha20.sigma ++ key) (by rw [l48]; omega),
          VG.Proof.ChaCha20.wordLE_append_left (by rw [VG.Proof.ChaCha20.length_sigma]; omega), VG.Proof.ChaCha20.sigma_words i h4]
      by_cases h12 : i < 12
      · simp only [show ¬ (12 = i) by omega, h4, h12, ↓reduceIte]
        rw [VG.Proof.ChaCha20.wordLE_append_left (xs := VG.Proof.ChaCha20.sigma ++ key) (by rw [l48]; omega),
          VG.Proof.ChaCha20.wordLE_append_right l16 (by omega)]
      · simp only [show ¬ (12 = i) by omega, h4, h12, e, ↓reduceIte]
        rw [VG.Proof.ChaCha20.wordLE_append_right l48 (by omega), VG.Proof.ChaCha20.wordLE_drop]
        congr 1; omega
  have h12 : (stateAt m p)[12] = wordLE nonce 0 := by
    rw [hw 12 (by decide), VG.Proof.ChaCha20.wordLE_append_right l48 (Nat.le_refl 12)]
  have hmod : leftAt m p % 64 = 0 := by rw [hl]; omega
  simp only [restAt, hmod, keystreamOf, keystream]
  have e0 : bytesAt m (p + BitVec.ofNat 64 (128 - 0)) 0 = [] := List.map_nil
  generalize hN : 2 ^ 32 - (wordLE nonce 0).toNat = N at hl
  have e1 : 64 * (leftAt m p / 64) = 64 * N := by rw [hl]; omega
  have e2 : (64 * N + 63) / 64 = N := by omega
  rw [e0, List.nil_append, e1, e2, List.take_of_length_le (by
    rw [VG.Proof.ChaCha20.length_flatMap_const _ (n := 64) (fun _ => VG.Proof.ChaCha20.length_serialize _), List.length_range])]
  simp only [hS, chacha20Block]

/-- The key of a state whose key bytes are `key`. -/
theorem keyAt_of_bytes {m : Mem} {p : Addr} {key : List Byte} (hk : key.length = 32)
    (hb : ∀ i < 32, m (p + BitVec.ofNat 64 (16 + i)) = key.getD i 0) : keyAt m p = key := by
  apply List.ext_getElem
  · simp [keyAt, VG.Proof.ChaCha20.length_bytesAt, hk]
  · intro i h₁ h₂
    simp only [keyAt, bytesAt, List.getElem_map, List.getElem_range]
    rw [show (p + 16 : Addr) = p + BitVec.ofNat 64 16 from rfl, Offset.add_add,
      hb i (by simpa [keyAt, VG.Proof.ChaCha20.length_bytesAt] using h₁), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h₂, Option.getD_some]

/-- `restAt_of_bytes` and `keyAt_of_bytes` from the three parts of the
16-word state: the constants, the key and the nonce. -/
theorem stream_of_parts {m : Mem} {p : Addr} {key nonce : List Byte} (hk : key.length = 32)
    (hσ : ∀ i < 16, m (p + BitVec.ofNat 64 i) = sigma.getD i 0)
    (hK : ∀ i < 32, m (p + BitVec.ofNat 64 (16 + i)) = key.getD i 0)
    (hN : ∀ i < 16, m (p + BitVec.ofNat 64 (48 + i)) = nonce.getD i 0)
    (hl : leftAt m p = 64 * (2 ^ 32 - (wordLE nonce 0).toNat)) :
    keyAt m p = key ∧ restAt m p = keystreamOf key nonce := by
  refine ⟨VG.Proof.ChaCha20.keyAt_of_bytes hk hK, VG.Proof.ChaCha20.restAt_of_bytes hk (fun i hi => ?_) hl⟩
  have l48 : (VG.Proof.ChaCha20.sigma ++ key).length = 48 := by rw [List.length_append, VG.Proof.ChaCha20.length_sigma, hk]
  by_cases h₁ : i < 48
  · rw [VG.Proof.ChaCha20.getD_append_left (by rw [l48]; exact h₁)]
    by_cases h₂ : i < 16
    · rw [VG.Proof.ChaCha20.getD_append_left (by rw [VG.Proof.ChaCha20.length_sigma]; exact h₂), hσ i h₂]
    · rw [VG.Proof.ChaCha20.getD_append_right (by rw [VG.Proof.ChaCha20.length_sigma]; omega), VG.Proof.ChaCha20.length_sigma, ← hK (i - 16) (by omega),
        show 16 + (i - 16) = i by omega]
  · rw [VG.Proof.ChaCha20.getD_append_right (by rw [l48]; omega), l48, ← hN (i - 48) (by omega),
      show 48 + (i - 48) = i by omega]

/-- Byte `j` of a little-endian 64-bit word. -/
theorem readW64_byte (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    (m.readW a 64).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

/-- The bytes of memory from its 64-bit words. -/
theorem byte_of_words64 {m : Mem} {p : Addr} {W : Nat → BitVec 64} {a b : Nat}
    (h : ∀ k, a ≤ k → k < b → m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = W k) {i : Nat}
    (h₁ : 8 * a ≤ i) (h₂ : i < 8 * b) :
    m (p + BitVec.ofNat 64 i) = (W (i / 8)).extractLsb' (8 * (i % 8)) 8 := by
  rw [← h (i / 8) (by omega) (by omega), VG.Proof.ChaCha20.readW64_byte _ _ (Nat.mod_lt _ (by decide)), Offset.add_add,
    show 8 * (i / 8) + i % 8 = i by omega]

/-- The bytes of memory from its 32-bit words. -/
theorem byte_of_words32 {m : Mem} {p : Addr} {W : Nat → BitVec 32} {a b : Nat}
    (h : ∀ k, a ≤ k → k < b → m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = W k) {i : Nat}
    (h₁ : 4 * a ≤ i) (h₂ : i < 4 * b) :
    m (p + BitVec.ofNat 64 i) = (W (i / 4)).extractLsb' (8 * (i % 4)) 8 := by
  rw [← h (i / 4) (by omega) (by omega), ← Mem.readW_byte _ _ (Nat.mod_lt _ (by decide)), Offset.add_add,
    show 4 * (i / 4) + i % 4 = i by omega]

/-- The first word of a nonce in memory. -/
theorem wordLE_bytesAt (m : Mem) (p : Addr) {n : Nat} (hn : 4 ≤ n) :
    wordLE (bytesAt m p n) 0 = m.readW p 32 :=
  VG.Proof.ChaCha20.word_ext fun i hi => by
    rw [VG.Proof.ChaCha20.wordLE_byte _ _ hi, Nat.mul_zero, Nat.zero_add, VG.Proof.ChaCha20.bytesAt_getD _ _ (by omega), Mem.readW_byte m p hi]

/-- The low half of a 64-bit word. -/
theorem readW64_setWidth (m : Mem) (a : Addr) : (m.readW a 64).setWidth 32 = m.readW a 32 := by
  refine VG.Proof.ChaCha20.word_ext fun i hi => ?_
  rw [← Mem.readW_byte m a hi, ← VG.Proof.ChaCha20.readW64_byte m a (by omega)]
  ext j hj
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
  omega

/-- A 16-word state with the same bytes. -/
theorem stateAt_congr {m m' : Mem} {p q : Addr}
    (h : ∀ i < 64, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) : stateAt m' q = stateAt m p := by
  apply Vector.ext; intro j hj
  simp only [stateAt, Vector.getElem_ofFn]
  refine VG.Proof.ChaCha20.word_ext fun i hi => ?_
  rw [← Mem.readW_byte m' _ hi, ← Mem.readW_byte m _ hi, Offset.add_add, Offset.add_add, h _ (by omega)]

theorem getElem_eq_getD' (l : List Byte) {i : Nat} (h : i < l.length) : l[i] = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- XORing a keystream into data in memory, byte by byte (the converse of
`bytesAt_xor`). -/
theorem xor_getD {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {j : Nat} (hj : j < n) :
    m' (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j) ^^^ ks.getD j 0 := by
  have := congrArg (·.getD j 0) h
  rw [VG.Proof.ChaCha20.bytesAt_getD _ _ hj] at this
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem
    (by rw [VG.Proof.ChaCha20.length_bytesAt]; exact hj), List.getElem?_eq_getElem (by rw [hks]; exact hj)]
  simp only [Option.getD_some]
  rw [VG.Proof.ChaCha20.getElem_eq_getD' _ (by rw [VG.Proof.ChaCha20.length_bytesAt]; exact hj), VG.Proof.ChaCha20.bytesAt_getD _ _ hj,
    VG.Proof.ChaCha20.getElem_eq_getD' _ (show j < ks.length by omega)]

/-- Reading a word after writing one elsewhere, at offsets from `p`. -/
theorem readW_writeW_ofNat (m : Mem) (p : Addr) {w w' : Nat} (v : BitVec w') {d e : Nat}
    (h : d + w / 8 ≤ e ∨ e + w' / 8 ≤ d) (hd : d + w / 8 ≤ 2 ^ 64) (he : e + w' / 8 ≤ 2 ^ 64)
    (hw : w / 8 < 2 ^ 64) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) w = m.readW (p + BitVec.ofNat 64 d) w :=
  Mem.readW_writeW_sep (Offset.sep p h hd he) hw

/-- A byte outside a write, at offsets from `p`. -/
theorem byte_writeW_ofNat (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {i e : Nat}
    (h : i + 1 ≤ e ∨ e + w / 8 ≤ i) (hi : i + 1 ≤ 2 ^ 64) (he : e + w / 8 ≤ 2 ^ 64) :
    (m.writeW (p + BitVec.ofNat 64 e) v) (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  Mem.write_apply (Offset.sep p h hi he _ (by simp))

/-! ## Applying the keystream -/

section Apply

variable (m : Mem) (p : Addr) (len : Nat)

/-- The bytes left in the buffered block. -/
abbrev bufLeft : Nat := leftAt m p % 64
/-- How many of them are used. -/
abbrev headLen : Nat := min (VG.Proof.ChaCha20.bufLeft m p) len
/-- How many whole blocks follow. -/
abbrev blocksOf : Nat := (len - VG.Proof.ChaCha20.headLen m p len) / 64
/-- How many bytes of one more block follow. -/
abbrev tailLen : Nat := (len - VG.Proof.ChaCha20.headLen m p len) % 64

end Apply

theorem ite_pos {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_neg {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem getD_take (l : List Byte) {n k : Nat} (h : k < n) : (l.take n).getD k 0 = l.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem blk_congr {S : VG.Proof.ChaCha20.CState} {a b c d : Nat} (h₁ : a = b) (h₂ : c = d) :
    (serialize (block (VG.Proof.ChaCha20.ctr S a))).getD c 0 = (serialize (block (VG.Proof.ChaCha20.ctr S b))).getD d 0 := by
  subst h₁ h₂; rfl

theorem getElem_eq_getD (l : List Byte) {i : Nat} (h : i < l.length) : l[i] = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The data after `apply`, byte by byte: the bytes left in the buffered
block, then the blocks of the 16-word state (whole ones, and the first bytes
of the last), XORed into it. -/
theorem apply_data {m m' : Mem} {p d : Addr} {len : Nat} (hlen : len ≤ leftAt m p)
    (hD : ∀ k < len, m' (d + BitVec.ofNat 64 k) = m (d + BitVec.ofNat 64 k) ^^^
      (if k < VG.Proof.ChaCha20.headLen m p len then m (p + BitVec.ofNat 64 (128 - VG.Proof.ChaCha20.bufLeft m p + k))
      else (serialize (block (VG.Proof.ChaCha20.ctr (stateAt m p) ((k - VG.Proof.ChaCha20.headLen m p len) / 64)))).getD
        ((k - VG.Proof.ChaCha20.headLen m p len) % 64) 0)) :
    bytesAt m' d len = List.zipWith (· ^^^ ·) (bytesAt m d len) ((restAt m p).take len) := by
  refine VG.Proof.ChaCha20.bytesAt_xor (by rw [List.length_take, VG.Proof.ChaCha20.length_restAt]; omega) fun k hk => ?_
  rw [hD k hk]
  refine congrArg (_ ^^^ ·) ?_
  have hh : VG.Proof.ChaCha20.headLen m p len = min (leftAt m p % 64) len := rfl
  have hb : VG.Proof.ChaCha20.bufLeft m p = leftAt m p % 64 := rfl
  rw [VG.Proof.ChaCha20.getD_take _ hk, VG.Proof.ChaCha20.restAt_getD _ _ (by omega)]
  by_cases h : k < VG.Proof.ChaCha20.headLen m p len
  · rw [VG.Proof.ChaCha20.ite_pos h, VG.Proof.ChaCha20.ite_pos (by omega)]
  · rw [VG.Proof.ChaCha20.ite_neg h, VG.Proof.ChaCha20.ite_neg (by omega), show VG.Proof.ChaCha20.headLen m p len = leftAt m p % 64 by omega]

/-- The keystream left after `apply`: the counter advanced past the blocks
used, and, if a block was started (`tailLen ≠ 0`), that block buffered;
`left` decreased by the length. -/
theorem apply_rest {m m' : Mem} {p : Addr} {len : Nat} (hlen : len ≤ leftAt m p)
    (hL : leftAt m' p = leftAt m p - len)
    (hS : stateAt m' p = VG.Proof.ChaCha20.ctr (stateAt m p) (VG.Proof.ChaCha20.blocksOf m p len + if VG.Proof.ChaCha20.tailLen m p len = 0 then 0 else 1))
    (hB : ∀ i < 64, m' (p + BitVec.ofNat 64 (64 + i)) = if VG.Proof.ChaCha20.tailLen m p len = 0 then m (p + BitVec.ofNat 64 (64 + i))
      else (serialize (block (VG.Proof.ChaCha20.ctr (stateAt m p) (VG.Proof.ChaCha20.blocksOf m p len)))).getD i 0) :
    restAt m' p = (restAt m p).drop len := by
  apply List.ext_getElem
  · rw [VG.Proof.ChaCha20.length_restAt, List.length_drop, VG.Proof.ChaCha20.length_restAt, hL]
  intro i h₁ _
  rw [VG.Proof.ChaCha20.length_restAt, hL] at h₁
  rw [List.getElem_drop, VG.Proof.ChaCha20.getElem_eq_getD, VG.Proof.ChaCha20.getElem_eq_getD,
    VG.Proof.ChaCha20.restAt_getD _ _ (by omega), VG.Proof.ChaCha20.restAt_getD _ _ (by omega), hL, hS, VG.Proof.ChaCha20.ctr_ctr]
  generalize hn : leftAt m p = n at *
  have hbl : VG.Proof.ChaCha20.bufLeft m p = n % 64 := by simp only [VG.Proof.ChaCha20.bufLeft, hn]
  have hh : VG.Proof.ChaCha20.headLen m p len = min (n % 64) len := by simp only [VG.Proof.ChaCha20.headLen, hbl]
  have hnb : VG.Proof.ChaCha20.blocksOf m p len = (len - min (n % 64) len) / 64 := by simp only [VG.Proof.ChaCha20.blocksOf, hh]
  have ht : VG.Proof.ChaCha20.tailLen m p len = (len - min (n % 64) len) % 64 := by simp only [VG.Proof.ChaCha20.tailLen, hh]
  rw [hnb, ht] at hB ⊢
  by_cases t0 : (len - min (n % 64) len) % 64 = 0
  · simp only [t0, ite_true, Nat.add_zero] at hB ⊢
    by_cases hlo : len ≤ n % 64
    · have e1 : (n - len) % 64 = n % 64 - len := by omega
      have e2 : (len - min (n % 64) len) / 64 = 0 := by omega
      rw [e1, e2]
      by_cases hi : i < n % 64 - len
      · rw [VG.Proof.ChaCha20.ite_pos hi, VG.Proof.ChaCha20.ite_pos (by omega)]
        have := hB (64 - (n % 64 - len) + i) (by omega)
        rw [show 64 + (64 - (n % 64 - len) + i) = 128 - (n % 64 - len) + i by omega] at this
        rw [this, show 128 - n % 64 + (len + i) = 128 - (n % 64 - len) + i by omega]
      · rw [VG.Proof.ChaCha20.ite_neg hi, VG.Proof.ChaCha20.ite_neg (by omega)]
        exact VG.Proof.ChaCha20.blk_congr (by omega) (by omega)
    · have e1 : (n - len) % 64 = 0 := by omega
      rw [e1, VG.Proof.ChaCha20.ite_neg (by omega), VG.Proof.ChaCha20.ite_neg (by omega)]
      exact VG.Proof.ChaCha20.blk_congr (by omega) (by omega)
  · simp only [t0, ite_false] at hB ⊢
    have e1 : (n - len) % 64 = 64 - (len - n % 64) % 64 := by omega
    rw [e1]
    by_cases hi : i < 64 - (len - n % 64) % 64
    · rw [VG.Proof.ChaCha20.ite_pos hi, VG.Proof.ChaCha20.ite_neg (by omega)]
      have := hB ((len - n % 64) % 64 + i) (by omega)
      rw [show 64 + ((len - n % 64) % 64 + i) = 128 - (64 - (len - n % 64) % 64) + i by omega]
        at this
      rw [this]
      exact VG.Proof.ChaCha20.blk_congr (by omega) (by omega)
    · rw [VG.Proof.ChaCha20.ite_neg hi, VG.Proof.ChaCha20.ite_neg (by omega)]
      exact VG.Proof.ChaCha20.blk_congr (by omega) (by omega)

end VG.Proof.ChaCha20

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.StreamBytes`. -/
section

/-!
# Streaming ChaCha20: words in memory, byte by byte

Untrusted: everything here is checked by Lean. Target-independent lemmas for
the 32-bit targets, which store the 64-bit number of bytes left as two
32-bit words and copy 16 bytes at a time: the bytes of a write and of a
read of any width, and a 64-bit word from its two halves.
-/

namespace VG.Proof.ChaCha20

open VG.Spec.ChaCha20 (leftAt)

/-- A byte of a little-endian write. -/
theorem byte_writeW_self (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) {i : Nat} (hi : i < w / 8)
    (hi' : i < 2 ^ 64) : (m.writeW a v) (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a hi', hi, ite_true]
  ext k hk
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * i + k < 8 * (w / 8) := by omega
  simp [this]

/-- Byte `j` of a little-endian 128-bit word. -/
theorem readW128_byte (m : Mem) (a : Addr) {j : Nat} (hj : j < 16) :
    (m.readW a 128).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m a (n := 16) hj]
  simp only [Mem.readW]
  rfl

/-- Two 64-bit words with the same bytes are equal. -/
theorem word64_ext {x y : BitVec 64} (h : ∀ i < 8, x.extractLsb' (8 * i) 8 = y.extractLsb' (8 * i) 8) :
    x = y := by
  ext j hj
  have := congrArg (·.getLsbD (j % 8)) (h (j / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 by omega, decide_true,
    Bool.true_and] at this
  rw [show 8 * (j / 8) + j % 8 = j by omega] at this
  simpa [BitVec.getLsbD_eq_getElem hj] using this

/-- The 64-bit number `v` from its two 32-bit halves, low first, written at
`p + e`. -/
theorem readW64_halves (m : Mem) (p : Addr) {e : Nat} (v : Nat) (he : e + 8 ≤ 2 ^ 32) :
    ((m.writeW (p + BitVec.ofNat 64 e) (BitVec.ofNat 32 v)).writeW (p + BitVec.ofNat 64 (e + 4))
      (BitVec.ofNat 32 (v / 2 ^ 32))).readW (p + BitVec.ofNat 64 e) 64 = BitVec.ofNat 64 v := by
  refine VG.Proof.ChaCha20.word64_ext fun j hj => ?_
  rw [VG.Proof.ChaCha20.readW64_byte _ _ hj, Offset.add_add]
  by_cases hlo : j < 4
  · rw [VG.Proof.ChaCha20.byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), ← Offset.add_add p e j,
      VG.Proof.ChaCha20.byte_writeW_self _ _ _ (by omega) (by omega)]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_ofNat]
    simp [show 8 * j + k < 32 by omega, show 8 * j + k < 64 by omega]
  · rw [show e + j = (e + 4) + (j - 4) by omega, ← Offset.add_add p (e + 4) (j - 4),
      VG.Proof.ChaCha20.byte_writeW_self _ _ _ (by omega) (by omega)]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_ofNat, Nat.testBit_div_two_pow]
    simp [show 8 * (j - 4) + k < 32 by omega, show 8 * j + k < 64 by omega,
      show 8 * (j - 4) + k + 32 = 8 * j + k by omega]

/-- The number of bytes left, from its two halves. -/
theorem leftAt_halves (m : Mem) (p : Addr) {v : Nat} (hv : v < 2 ^ 64) :
    leftAt ((m.writeW (p + BitVec.ofNat 64 128) (BitVec.ofNat 32 v)).writeW (p + BitVec.ofNat 64 132)
      (BitVec.ofNat 32 (v / 2 ^ 32))) p = v := by
  simp only [leftAt]
  rw [show (p + 128 : Addr) = p + BitVec.ofNat 64 128 from rfl, VG.Proof.ChaCha20.readW64_halves m p (e := 128) v (by decide),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

/-- Byte `j` of two words, low first. -/
theorem append_byte (hi lo : BitVec 32) {j : Nat} (hj : j < 8) :
    (hi ++ lo).extractLsb' (8 * j) 8 = if j < 4 then lo.extractLsb' (8 * j) 8 else hi.extractLsb' (8 * (j - 4)) 8 := by
  by_cases h : j < 4
  · rw [VG.Proof.ChaCha20.ite_pos h]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append, show 8 * j + k < 32 by omega, ite_true]
  · rw [VG.Proof.ChaCha20.ite_neg h]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append, show ¬ (8 * j + k < 32) by omega, ite_false]
    congr 1; omega

/-- A 64-bit word in memory is its two 32-bit halves, low first. -/
theorem readW64_split (m : Mem) (a : Addr) : m.readW a 64 = m.readW (a + BitVec.ofNat 64 4) 32 ++ m.readW a 32 := by
  refine VG.Proof.ChaCha20.word64_ext fun j hj => ?_
  rw [VG.Proof.ChaCha20.readW64_byte _ _ hj, VG.Proof.ChaCha20.append_byte _ _ hj]
  by_cases h : j < 4
  · rw [VG.Proof.ChaCha20.ite_pos h, ← Mem.readW_byte _ _ h]
  · rw [VG.Proof.ChaCha20.ite_neg h, ← Mem.readW_byte _ _ (by omega), Offset.add_add, show 4 + (j - 4) = j by omega]

theorem readW64_toNat (m : Mem) (a : Addr) :
    (m.readW a 64).toNat = (m.readW a 32).toNat + 2 ^ 32 * (m.readW (a + BitVec.ofNat 64 4) 32).toNat := by
  rw [VG.Proof.ChaCha20.readW64_split, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (m.readW a 32).isLt, Nat.shiftLeft_eq]
  omega

/-- The bytes of memory from its 128-bit words. -/
theorem byte_of_words128 {m : Mem} {p : Addr} {W : Nat → BitVec 128} {a b : Nat}
    (h : ∀ k, a ≤ k → k < b → m.readW (p + BitVec.ofNat 64 (16 * k)) 128 = W k) {i : Nat}
    (h₁ : 16 * a ≤ i) (h₂ : i < 16 * b) :
    m (p + BitVec.ofNat 64 i) = (W (i / 16)).extractLsb' (8 * (i % 16)) 8 := by
  rw [← h (i / 16) (by omega) (by omega), VG.Proof.ChaCha20.readW128_byte _ _ (Nat.mod_lt _ (by decide)), Offset.add_add,
    show 16 * (i / 16) + i % 16 = i by omega]

end VG.Proof.ChaCha20

end
