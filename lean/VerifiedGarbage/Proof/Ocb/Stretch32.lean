import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Spec.Aes.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ocb.Sum`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ocb.Spec`. -/
section

/-!
# OCB: the algorithm as the implementations compute it

Untrusted: everything here is checked by Lean. Target-independent facts
about `Spec/Ocb.lean`:

* OCB's blocks, `double` and AES are GCM's and CMAC's (`ofBytes_eq`,
  `double_eq`, `aesWith_eq`), whose lemmas apply;
* `L_i` is `L_0` doubled `i` times, and `ntz` halves an even number
  (`lAt_succ`, `ntz_odd`, `ntz_even`);
* the folds of `HASH`, `OCB-ENCRYPT` and `OCB-DECRYPT` over the whole blocks
  compute the offsets (`offAt`), the checksum (`ckAt`), the sum (`hsum`) and
  the output a block at a time (`hash_eq`, `encryptWith_eq`,
  `decryptWith_eq`), which the implementations compute in passes;
* the blocks of bytes in memory (`blockAt_bytesAt`, `bytesAt_blocks`).
-/

namespace VG.Proof.Ocb

open VG.Spec.Ocb

theorem ofBytes_eq : Spec.Ocb.ofBytes = Spec.Gcm.ofBytes := rfl
theorem toBytes_eq : Spec.Ocb.toBytes = Spec.Gcm.toBytes := rfl
theorem xor_eq : Spec.Ocb.xor = Spec.Cmac.xor := rfl
theorem aesWith_eq : Spec.Ocb.aesWith = Spec.Gcm.aesWith := rfl
theorem zeros_eq : Spec.Ocb.zeros = Spec.Cmac.zeros := rfl

theorem double_eq (s : Block) : double s = Proof.Cmac.dbl128 s := by
  unfold double Proof.Cmac.dbl128; split <;> simp

theorem toBytes_length (x : Block) : (toBytes x).length = 16 := Proof.Cmac.toBytes_length x

theorem ofBytes_toBytes (x : Block) : ofBytes (toBytes x) = x := Proof.Cmac.ofBytes_toBytes x

theorem toBytes_ofBytes {bs : List Byte} (h : bs.length = 16) : toBytes (ofBytes bs) = bs :=
  Proof.Cmac.toBytes_ofBytes h

theorem toBytes_inj {x y : Block} (h : toBytes x = toBytes y) : x = y := by
  rw [← VG.Proof.Ocb.ofBytes_toBytes x, h, VG.Proof.Ocb.ofBytes_toBytes]

/-- XOR of blocks is XOR of their bytes. -/
theorem toBytes_xor (x y : Block) : toBytes (x ^^^ y) = Spec.Ocb.xor (toBytes x) (toBytes y) := by
  refine Proof.Cmac.ext16 (VG.Proof.Ocb.toBytes_length _) (by simp [Spec.Ocb.xor, VG.Proof.Ocb.toBytes_length]) fun k hk => ?_
  rw [VG.Proof.Ocb.toBytes_eq, Proof.Aes.toBytes_xor x y hk, VG.Proof.Ocb.xor_eq,
    Proof.Cmac.getD_xor (by simp [Proof.Cmac.toBytes_length]) (by rw [Proof.Cmac.toBytes_length]; exact hk)]

theorem ofBytes_xor {xs ys : List Byte} (hx : xs.length = 16) (hy : ys.length = 16) :
    ofBytes (Spec.Ocb.xor xs ys) = ofBytes xs ^^^ ofBytes ys := by
  apply VG.Proof.Ocb.toBytes_inj
  rw [VG.Proof.Ocb.toBytes_xor, VG.Proof.Ocb.toBytes_ofBytes hx, VG.Proof.Ocb.toBytes_ofBytes hy,
    VG.Proof.Ocb.toBytes_ofBytes (by simp [Spec.Ocb.xor, hx, hy])]

/-! ## `L_i` and `ntz` -/

theorem lAt_zero (l : Block) : lAt l 0 = double (double l) := rfl

theorem lAt_succ (l : Block) (i : Nat) : lAt l (i + 1) = double (lAt l i) := rfl

theorem lAt_zero_dollar (l : Block) : lAt l 0 = double (lDollar l) := rfl

theorem ntzAux_succ : ∀ f n, n ≤ f → ntzAux (f + 1) n = ntzAux f n
  | 0, n, h => by
    obtain rfl : n = 0 := by omega
    rfl
  | f + 1, n, h => by
    show (if n = 0 ∨ n % 2 = 1 then 0 else ntzAux (f + 1) (n / 2) + 1) =
      (if n = 0 ∨ n % 2 = 1 then 0 else ntzAux f (n / 2) + 1)
    split
    · rfl
    · rw [VG.Proof.Ocb.ntzAux_succ f (n / 2) (by omega)]

theorem ntzAux_ge {f n : Nat} (h : n ≤ f) : ntzAux f n = ntz n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, VG.Proof.Ocb.ntzAux_succ _ _ (by omega), ih (by omega)]

theorem ntz_odd {n : Nat} (h : n % 2 = 1) : ntz n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show (if k + 1 = 0 ∨ (k + 1) % 2 = 1 then 0 else ntzAux k ((k + 1) / 2) + 1) = 0
  exact ite_eq_left_iff.mpr fun hn => absurd (.inr h) hn

theorem ntz_even {n : Nat} (h0 : 0 < n) (h : n % 2 = 0) : ntz n = ntz (n / 2) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show (if k + 1 = 0 ∨ (k + 1) % 2 = 1 then 0 else ntzAux k ((k + 1) / 2) + 1) = _
  simp only [show ¬(k + 1 = 0 ∨ (k + 1) % 2 = 1) by omega, ↓reduceIte]
  rw [VG.Proof.Ocb.ntzAux_ge (by omega)]

/-! ## The folds over the whole blocks -/

/-- `Offset_i`, from `Offset_0 = o0`. -/
def offAt (o0 l : Block) : Nat → Block
  | 0 => o0
  | i + 1 => VG.Proof.Ocb.offAt o0 l i ^^^ lAt l (ntz (i + 1))

/-- `Checksum_i` of the plaintext `p`. -/
def ckAt (p : List Byte) : Nat → Block
  | 0 => 0
  | i + 1 => VG.Proof.Ocb.ckAt p i ^^^ blockAt p i

/-- `Sum_i` of `HASH` of `a`. -/
def hsum (ciph : Cipher) (l : Block) (a : List Byte) : Nat → Block
  | 0 => 0
  | i + 1 => VG.Proof.Ocb.hsum ciph l a i ^^^ ciph (blockAt a i ^^^ VG.Proof.Ocb.offAt 0 l (i + 1))

/-- `C_1 ‖ … ‖ C_m`. -/
def encBlocks (ciph : Cipher) (o0 l : Block) (p : List Byte) (m : Nat) : List Byte :=
  (List.range m).flatMap fun i => toBytes (VG.Proof.Ocb.offAt o0 l (i + 1) ^^^ ciph (blockAt p i ^^^ VG.Proof.Ocb.offAt o0 l (i + 1)))

/-- `P_i` of the ciphertext `c`. -/
def decBlock (inv : Cipher) (o0 l : Block) (c : List Byte) (i : Nat) : Block :=
  VG.Proof.Ocb.offAt o0 l (i + 1) ^^^ inv (blockAt c i ^^^ VG.Proof.Ocb.offAt o0 l (i + 1))

/-- `P_1 ‖ … ‖ P_m`. -/
def decBlocks (inv : Cipher) (o0 l : Block) (c : List Byte) (m : Nat) : List Byte :=
  (List.range m).flatMap fun i => toBytes (VG.Proof.Ocb.decBlock inv o0 l c i)

/-- `Checksum_i` of the decrypted ciphertext `c`. -/
def dckAt (inv : Cipher) (o0 l : Block) (c : List Byte) : Nat → Block
  | 0 => 0
  | i + 1 => VG.Proof.Ocb.dckAt inv o0 l c i ^^^ VG.Proof.Ocb.decBlock inv o0 l c i

theorem hash_fold (ciph : Cipher) (l : Block) (a : List Byte) (m : Nat) :
    (List.range m).foldl (fun (sum, offset) i =>
      let offset := offset ^^^ lAt l (ntz (i + 1))
      (sum ^^^ ciph (blockAt a i ^^^ offset), offset)) ((0 : Block), (0 : Block)) =
      (VG.Proof.Ocb.hsum ciph l a m, VG.Proof.Ocb.offAt 0 l m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem enc_fold (ciph : Cipher) (l o0 : Block) (p : List Byte) (m : Nat) :
    (List.range m).foldl (fun (offset, checksum, c) i =>
      let offset := offset ^^^ lAt l (ntz (i + 1))
      (offset, checksum ^^^ blockAt p i, c ++ toBytes (offset ^^^ ciph (blockAt p i ^^^ offset))))
      (o0, (0 : Block), ([] : List Byte)) =
      (VG.Proof.Ocb.offAt o0 l m, VG.Proof.Ocb.ckAt p m, VG.Proof.Ocb.encBlocks ciph o0 l p m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, VG.Proof.Ocb.encBlocks, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl

theorem dec_fold (inv : Cipher) (l o0 : Block) (c : List Byte) (m : Nat) :
    (List.range m).foldl (fun (offset, checksum, p) i =>
      let offset := offset ^^^ lAt l (ntz (i + 1))
      let pi := offset ^^^ inv (blockAt c i ^^^ offset)
      (offset, checksum ^^^ pi, p ++ toBytes pi))
      (o0, (0 : Block), ([] : List Byte)) =
      (VG.Proof.Ocb.offAt o0 l m, VG.Proof.Ocb.dckAt inv o0 l c m, VG.Proof.Ocb.decBlocks inv o0 l c m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, VG.Proof.Ocb.decBlocks, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl

/-- `HASH`, from the sum and the offset of its whole blocks. -/
theorem hash_eq (ciph : Cipher) (l : Block) (a : List Byte) :
    Spec.Ocb.hash ciph l a =
      if (a.drop (16 * (a.length / 16))).length > 0 then
        VG.Proof.Ocb.hsum ciph l a (a.length / 16) ^^^
          ciph (pad (a.drop (16 * (a.length / 16))) ^^^ (VG.Proof.Ocb.offAt 0 l (a.length / 16) ^^^ l))
      else VG.Proof.Ocb.hsum ciph l a (a.length / 16) := by
  unfold Spec.Ocb.hash
  simp only [VG.Proof.Ocb.hash_fold]

/-- `OCB-ENCRYPT`, from the offset, the checksum and the output of its whole
blocks. -/
theorem encryptWith_eq (ciph : Cipher) (l : Block) (t : Nat) (nonce a p : List Byte) :
    encryptWith ciph l t nonce a p =
      let m := p.length / 16
      let o := VG.Proof.Ocb.offAt (offset0 ciph t nonce) l m
      let ck := VG.Proof.Ocb.ckAt p m
      let c := VG.Proof.Ocb.encBlocks ciph (offset0 ciph t nonce) l p m
      let rest := p.drop (16 * m)
      if rest.length > 0 then
        (c ++ Spec.Ocb.xor rest (toBytes (ciph (o ^^^ l))),
          (toBytes (ciph (ck ^^^ pad rest ^^^ (o ^^^ l) ^^^ lDollar l) ^^^ Spec.Ocb.hash ciph l a)).take t)
      else (c, (toBytes (ciph (ck ^^^ o ^^^ lDollar l) ^^^ Spec.Ocb.hash ciph l a)).take t) := by
  unfold encryptWith
  simp only [VG.Proof.Ocb.enc_fold]
  split <;> rfl

/-- `OCB-DECRYPT`, from the offset, the checksum and the output of its whole
blocks. -/
theorem decryptWith_eq (ciph inv : Cipher) (l : Block) (t : Nat) (nonce a c tag : List Byte) :
    decryptWith ciph inv l t nonce a c tag =
      let m := c.length / 16
      let o := VG.Proof.Ocb.offAt (offset0 ciph t nonce) l m
      let ck := VG.Proof.Ocb.dckAt inv (offset0 ciph t nonce) l c m
      let p := VG.Proof.Ocb.decBlocks inv (offset0 ciph t nonce) l c m
      let rest := c.drop (16 * m)
      let (p, tag') :=
        if rest.length > 0 then
          let ps := Spec.Ocb.xor rest (toBytes (ciph (o ^^^ l)))
          (p ++ ps, ciph (ck ^^^ pad ps ^^^ (o ^^^ l) ^^^ lDollar l) ^^^ Spec.Ocb.hash ciph l a)
        else (p, ciph (ck ^^^ o ^^^ lDollar l) ^^^ Spec.Ocb.hash ciph l a)
      if (toBytes tag').take t = tag then some p else none := by
  unfold decryptWith
  simp only [VG.Proof.Ocb.dec_fold]

/-! ## Blocks of bytes in memory -/

theorem bytesAt_append (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Aes.bytesAt m p (a + b) =
      Spec.Aes.bytesAt m p a ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Aes.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc, BitVec.ofNat_add]

/-- The bytes from `a` to `a + b`. -/
theorem bytesAt_slice (m : Mem) (p : Addr) {a b n : Nat} (h : a + b ≤ n) :
    ((Spec.Aes.bytesAt m p n).drop a).take b = Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt]; omega)
  intro k h₁ h₂
  simp only [List.length_take, List.length_drop, Spec.Aes.bytesAt, List.length_map,
    List.length_range] at h₁
  simp [Spec.Aes.bytesAt, BitVec.add_assoc, BitVec.ofNat_add]

theorem bytesAt_drop (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    (Spec.Aes.bytesAt m p n).drop a = Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) (n - a) := by
  rw [← VG.Proof.Ocb.bytesAt_slice m p (a := a) (b := n - a) (n := n) (by omega),
    List.take_of_length_le (by simp [Spec.Aes.bytesAt])]

/-- Block `i` of the bytes at `p`. -/
theorem blockAt_bytesAt (m : Mem) (p : Addr) {n i : Nat} (h : 16 * (i + 1) ≤ n) :
    blockAt (Spec.Aes.bytesAt m p n) i = blockAtMem m (p + BitVec.ofNat 64 (16 * i)) := by
  rw [blockAt, VG.Proof.Ocb.bytesAt_slice m p (by omega), blockAtMem]

/-- The bytes of `k` blocks, a block at a time. -/
theorem bytesAt_blocks (m : Mem) (p : Addr) (k : Nat) :
    Spec.Aes.bytesAt m p (16 * k) =
      (List.range k).flatMap fun i => Spec.Aes.bytesAt m (p + BitVec.ofNat 64 (16 * i)) 16 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 16 * (k + 1) = 16 * k + 16 by omega, VG.Proof.Ocb.bytesAt_append, ih, List.range_succ,
      List.flatMap_append]
    simp

end VG.Proof.Ocb

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ocb.Bytes`. -/
section

/-!
# OCB: the bytes of a buffer after writes

Untrusted: everything here is checked by Lean. A write of a byte or of
bytes into a buffer replaces those of its bytes (`bytesAt_writeBytes_at`,
`bytesAt_writeW8_at`), on every target: the pieces build the blocks
`pad(S)` and `Nonce` as lists. A byte of memory as an element of the bytes read
(`getD_bytesAt_eq`), an element of a list of 16 with one byte replaced
(`getD_set16`), bytes XORed with the first bytes of a block
(`xor_bytesAt_block`), and its first bytes (`bytesAt_take_block`).
-/

namespace VG.Proof.Ocb

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem getElem_bytesAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n)[i]'(by rw [VG.Proof.Ocb.length_bytesAt]; exact hi) = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt]

/-- `xs` written at `p + o`, inside the `n` bytes at `p`. -/
theorem bytesAt_writeBytes_at (m : Mem) (p : Addr) {o n : Nat} (xs : List Byte) (h : o + xs.length ≤ n)
    (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 o) xs) p n =
      (bytesAt m p n).take o ++ xs ++ (bytesAt m p n).drop (o + xs.length) := by
  apply List.ext_getElem (by simp [VG.Proof.Ocb.length_bytesAt]; omega)
  intro i h₁ h₂
  rw [VG.Proof.Ocb.getElem_bytesAt _ _ (by rw [VG.Proof.Ocb.length_bytesAt] at h₁; exact h₁)]
  simp only [writeBytes]
  have hi : i < n := by rw [VG.Proof.Ocb.length_bytesAt] at h₁; exact h₁
  have e : (p + BitVec.ofNat 64 i - (p + BitVec.ofNat 64 o)).toNat = (i + (2 ^ 64 - o)) % 2 ^ 64 := by
    rw [Offset.add_sub_add_left, BitVec.toNat_sub, VG.Proof.Ocb.toNat_ofNat_of_lt (by omega), VG.Proof.Ocb.toNat_ofNat_of_lt (by omega)]
    omega
  rw [e]
  have hl := VG.Proof.Ocb.length_bytesAt m p n
  by_cases hlo : i < o
  · rw [show (i + (2 ^ 64 - o)) % 2 ^ 64 = 2 ^ 64 - o + i by omega]
    simp only [show ¬ (2 ^ 64 - o + i < xs.length) by omega, ite_false]
    rw [List.getElem_append_left (by simp [hl]; omega), List.getElem_append_left (by simp [hl]; omega),
      List.getElem_take, VG.Proof.Ocb.getElem_bytesAt _ _ hi]
  · rw [show (i + (2 ^ 64 - o)) % 2 ^ 64 = i - o by omega]
    by_cases hhi : i < o + xs.length
    · simp only [show i - o < xs.length by omega, ite_true]
      rw [List.getElem_append_left (by simp [hl]; omega), List.getElem_append_right (by simp [hl]; omega)]
      simp only [List.length_take, hl, List.getD_eq_getElem?_getD, Nat.min_eq_left (show o ≤ n by omega),
        List.getElem?_eq_getElem (show i - o < xs.length by omega), Option.getD_some]
    · simp only [show ¬ (i - o < xs.length) by omega, ite_false]
      rw [List.getElem_append_right (by simp [hl]; omega), List.getElem_drop]
      simp only [List.length_append, List.length_take, hl, Nat.min_eq_left (show o ≤ n by omega)]
      rw [VG.Proof.Ocb.getElem_bytesAt _ _ (by omega), show o + xs.length + (i - (o + xs.length)) = i by omega]

/-- A byte write is a write of one byte. -/
theorem writeW8_eq (m : Mem) (a : Addr) (b : Byte) : m.writeW a b = writeBytes m a [b] := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, List.length_cons, List.length_nil, Nat.zero_add]
  split
  · rename_i h
    simp only [show (x - a).toNat = 0 by omega, List.getD_cons_zero]
    simp
  · rfl

/-- A word write is a write of its bytes, least significant first. -/
theorem bytesAt_writeW8_at (m : Mem) (p : Addr) {o n : Nat} (b : Byte) (h : o + 1 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 o) b) p n = (bytesAt m p n).take o ++ [b] ++ (bytesAt m p n).drop (o + 1) := by
  rw [VG.Proof.Ocb.writeW8_eq, VG.Proof.Ocb.bytesAt_writeBytes_at _ _ _ h hn]; rfl

/-- At offset 0. -/
theorem bytesAt_writeBytes_base (m : Mem) (p : Addr) {n : Nat} (xs : List Byte) (h : xs.length ≤ n)
    (hn : n < 2 ^ 64) : bytesAt (writeBytes m p xs) p n = xs ++ (bytesAt m p n).drop xs.length := by
  have := VG.Proof.Ocb.bytesAt_writeBytes_at m p (o := 0) xs (by omega) hn
  simpa using this

theorem bytesAt_writeW8_base (m : Mem) (p : Addr) {n : Nat} (b : Byte) (h : 1 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW p b) p n = b :: (bytesAt m p n).drop 1 := by
  have := VG.Proof.Ocb.bytesAt_writeW8_at m p (o := 0) b h hn
  simpa using this

theorem getD_bytesAt_eq (m : Mem) (p : Addr) {k n : Nat} (hk : k < n) :
    m (p + BitVec.ofNat 64 k) = (bytesAt m p n).getD k 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [bytesAt, hk]

/-- A byte written into a list of 16. -/
theorem getD_set16 (L : List Byte) (hL : L.length = 16) {o : Nat} (ho : o < 16) (b : Byte) {k : Nat}
    (hk : k < 16) : (L.take o ++ [b] ++ L.drop (o + 1)).getD k 0 = if k = o then b else L.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy k o with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_take_of_lt h]
    simp [show k ≠ o by omega]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp [show min k L.length = k by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_take, List.length_singleton, List.getElem?_drop,
      show ¬ k = o by omega, ↓reduceIte]
    congr 2; omega

theorem xor_append_right (xs ys zs : List Byte) (h : xs.length = ys.length) :
    Spec.Ocb.xor xs (ys ++ zs) = Spec.Ocb.xor xs ys := by
  simpa [Spec.Ocb.xor] using List.zipWith_append (f := fun x1 x2 : Byte => x1 ^^^ x2) (l₁' := []) (l₂' := zs) h

/-- `r` bytes XORed with the first `r` bytes of a block. -/
theorem xor_bytesAt_block (xs : List Byte) (m : Mem) (Q : Addr) {r : Nat} (hl : xs.length = r) (hr : r ≤ 16) :
    Spec.Ocb.xor xs (bytesAt m Q r) = Spec.Ocb.xor xs (Spec.Ocb.toBytes (Spec.Ocb.blockAtMem m Q)) := by
  rw [Spec.Ocb.blockAtMem, VG.Proof.Ocb.toBytes_ofBytes (Proof.Cmac.bytesAt_length _ _ _), show (16 : Nat) = r + (16 - r) by omega,
    VG.Proof.Ocb.bytesAt_append, VG.Proof.Ocb.xor_append_right _ _ _ (by rw [hl, Proof.Cmac.bytesAt_length])]

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (Spec.Ocb.blockAtMem m p)).take t := by
  rw [Spec.Ocb.blockAtMem, VG.Proof.Ocb.toBytes_ofBytes (Proof.Cmac.bytesAt_length _ _ _), show (16 : Nat) = t + (16 - t) by omega,
    VG.Proof.Ocb.bytesAt_append, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.Ocb

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ocb.Nonce`. -/
section

/-!
# OCB: the block `Nonce`

Untrusted: everything here is checked by Lean. `Nonce` (§4.2), for a tag of
`t` bytes and a nonce of 1 to 15 bytes, is the block `nonceN t nonce`, whose
byte `k` is `nb t nonce k` (`nonceN_byte`): the nonce at the end, a 1 before
it, and `TAGLEN mod 128` in the top 7 bits, as an implementation writes it
into zeros. `ENCIPHER` takes it with its last 6 bits cleared
(`nonceN_masked_byte`), which are `bottom` (`nonceN_bottom`, `offset0_eq`).
-/

namespace VG.Proof.Ocb

open VG.Spec.Ocb

/-- A number below `2 ^ i` has no bit `j ≥ i`. -/
theorem testBit_ge {x i j : Nat} (hx : x < 2 ^ i) (h : i ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) h))

/-- Bit `j` of byte `e` (from the right) of big-endian bytes. -/
theorem testBit_beVal (bs : List Byte) (e : Nat) {j : Nat} (hj : j < 8) :
    (Proof.Aes.beVal bs).testBit (8 * e + j) =
      if e < bs.length then (bs.getD (bs.length - 1 - e) 0).getLsbD j else false := by
  split
  · have hd := Proof.Aes.beVal_digit bs (k := bs.length - 1 - e) (by omega)
    rw [show bs.length - 1 - (bs.length - 1 - e) = e by omega] at hd
    rw [BitVec.getLsbD, ← hd, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, Nat.testBit_mod_two_pow,
      Nat.testBit_div_two_pow]
    simp [hj, Nat.add_comm]
  · have := Proof.Aes.beVal_lt bs
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
    exact VG.Proof.Ocb.testBit_ge this (by omega)

/-- The block `Nonce` of §4.2, before its last 6 bits are cleared. -/
def nonceN (t : Nat) (nonce : List Byte) : Block :=
  (BitVec.ofNat 128 (8 * t % 128) <<< 121) ||| ((1 : Block) <<< (8 * nonce.length)) |||
    BitVec.ofNat 128 (nonce.foldl (fun acc b => 256 * acc + b.toNat) 0)

/-- Byte `k` of `zeros ‖ 1 ‖ N`: the nonce at the end and a 1 before it. -/
def nbase (nonce : List Byte) (k : Nat) : Byte :=
  if k = 15 - nonce.length then 1
  else if 16 - nonce.length ≤ k then nonce.getD (k - (16 - nonce.length)) 0 else 0

/-- Byte `k` of `Nonce`, as an implementation writes it: the nonce at the end,
a 1 before it, and `TAGLEN mod 128` in the top 7 bits. -/
def nb (t : Nat) (nonce : List Byte) (k : Nat) : Byte :=
  if k = 0 then VG.Proof.Ocb.nbase nonce k ||| BitVec.ofNat 8 (16 * (t % 16)) else VG.Proof.Ocb.nbase nonce k

/-- The bits of 1. -/
theorem getLsbD_one' {w : Nat} (hw : 0 < w) (i : Nat) : (1 : BitVec w).getLsbD i = decide (i = 0) := by
  rw [show (1 : BitVec w) = 1#w from rfl, BitVec.getLsbD_one]; simp [hw]

/-- The bytes of `Nonce`. -/
theorem nonceN_byte (t : Nat) (nonce : List Byte) (h1 : 1 ≤ nonce.length) (h15 : nonce.length ≤ 15)
    {k : Nat} (hk : k < 16) : (toBytes (VG.Proof.Ocb.nonceN t nonce)).getD k 0 = VG.Proof.Ocb.nb t nonce k := by
  rw [VG.Proof.Ocb.toBytes_eq, Proof.Aes.toBytes_getD _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hb : nonce.foldl (fun acc b => 256 * acc + b.toNat) 0 = Proof.Aes.beVal nonce := rfl
  simp only [VG.Proof.Ocb.nonceN, hb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, VG.Proof.Ocb.getLsbD_one' (show 0 < 128 by decide), hj, decide_true, Bool.true_and,
    show 8 * (15 - k) + j < 128 by omega]
  rw [VG.Proof.Ocb.testBit_beVal nonce (15 - k) hj]
  have e8 : 8 * t % 128 = (t % 16) * 2 ^ 3 := by omega
  rw [e8, Nat.testBit_mul_two_pow]
  unfold VG.Proof.Ocb.nb VG.Proof.Ocb.nbase
  by_cases hk0 : k = 0
  · subst hk0
    have e16 : 16 * (t % 16) = 2 ^ 4 * (t % 16) := rfl
    simp only [↓reduceIte, BitVec.getLsbD_or, e16, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_mul, hj,
      decide_true, Bool.true_and, show ¬ 15 < nonce.length by omega, show ¬ 16 - nonce.length ≤ 0 by omega]
    by_cases hn : nonce.length = 15
    · simp only [hn, ↓reduceIte, VG.Proof.Ocb.getLsbD_one' (show 0 < 8 by decide)]
      rcases (show j = 0 ∨ (1 ≤ j ∧ j < 4) ∨ 4 ≤ j by omega) with rfl | ⟨ha, hb⟩ | ha
      · simp
      · simp [show ¬ 120 + j < 121 by omega, show ¬ 3 ≤ 120 + j - 121 by omega, show ¬ 4 ≤ j by omega,
          show j ≠ 0 by omega]
      · simp [show ¬ 120 + j < 121 by omega, show 3 ≤ 120 + j - 121 by omega, ha, show j ≠ 0 by omega,
          show 120 + j - 121 - 3 = j - 4 by omega, show 120 + j - 121 < 128 by omega]
    · simp only [show (0 = 15 - nonce.length) = False by simp; omega, ↓reduceIte]
      rcases (show j = 0 ∨ (1 ≤ j ∧ j < 4) ∨ 4 ≤ j by omega) with rfl | ⟨ha, hb⟩ | ha
      · simp [show ¬ 120 < 8 * nonce.length by omega, show 120 - 8 * nonce.length ≠ 0 by omega]
      · simp [show ¬ 120 + j < 121 by omega, show ¬ 3 ≤ 120 + j - 121 by omega, show ¬ 4 ≤ j by omega,
          show ¬ 120 + j < 8 * nonce.length by omega, show 120 + j - 8 * nonce.length ≠ 0 by omega]
      · simp [show ¬ 120 + j < 121 by omega, show 3 ≤ 120 + j - 121 by omega, ha,
          show 120 + j - 121 - 3 = j - 4 by omega, show 120 + j - 121 < 128 by omega,
          show ¬ 120 + j < 8 * nonce.length by omega, show 120 + j - 8 * nonce.length ≠ 0 by omega]
  · simp only [hk0, ↓reduceIte, show 8 * (15 - k) + j < 121 by omega, decide_true, Bool.not_true,
      Bool.false_and, Bool.false_or]
    by_cases hkn : k = 15 - nonce.length
    · simp only [hkn, ↓reduceIte, VG.Proof.Ocb.getLsbD_one' (show 0 < 8 by decide),
        show ¬ 15 - (15 - nonce.length) < nonce.length by omega, Bool.or_false]
      rcases (show j = 0 ∨ 0 < j by omega) with rfl | ha
      · simp [show 15 - (15 - nonce.length) = nonce.length by omega]
      · simp [show ¬ 8 * (15 - (15 - nonce.length)) + j < 8 * nonce.length by omega,
          show 8 * (15 - (15 - nonce.length)) + j - 8 * nonce.length ≠ 0 by omega, show j ≠ 0 by omega]
    · simp only [hkn, ↓reduceIte]
      by_cases hkr : 16 - nonce.length ≤ k
      · simp [hkr, show 15 - k < nonce.length by omega, show 8 * (15 - k) + j < 8 * nonce.length by omega,
          show nonce.length - 1 - (15 - k) = k - (16 - nonce.length) by omega]
      · simp [hkr, show ¬ 15 - k < nonce.length by omega, show ¬ 8 * (15 - k) + j < 8 * nonce.length by omega,
          show 8 * (15 - k) + j - 8 * nonce.length ≠ 0 by omega]

/-- The bytes of `~~~63`. -/
theorem mask63_byte : ∀ k < 16, (~~~(63 : Block)).extractLsb' (8 * (15 - k)) 8 =
    if k = 15 then 0xc0 else 0xff := by decide

/-- The bytes of `Nonce` with its last 6 bits cleared. -/
theorem nonceN_masked_byte (t : Nat) (nonce : List Byte) (h1 : 1 ≤ nonce.length) (h15 : nonce.length ≤ 15)
    {k : Nat} (hk : k < 16) :
    (toBytes (VG.Proof.Ocb.nonceN t nonce &&& ~~~(63 : Block))).getD k 0 =
      if k = 15 then VG.Proof.Ocb.nb t nonce 15 &&& 0xc0 else VG.Proof.Ocb.nb t nonce k := by
  rw [VG.Proof.Ocb.toBytes_eq, Proof.Aes.toBytes_getD _ hk, BitVec.extractLsb'_and, VG.Proof.Ocb.mask63_byte k hk,
    ← Proof.Aes.toBytes_getD _ hk, ← VG.Proof.Ocb.toBytes_eq, VG.Proof.Ocb.nonceN_byte t nonce h1 h15 hk]
  split
  · subst_vars; rfl
  · exact BitVec.and_allOnes

/-- `bottom`: the last 6 bits of `Nonce`. -/
theorem nonceN_bottom (t : Nat) (nonce : List Byte) (h1 : 1 ≤ nonce.length) (h15 : nonce.length ≤ 15) :
    ((VG.Proof.Ocb.nonceN t nonce).extractLsb' 0 6).toNat = (VG.Proof.Ocb.nb t nonce 15).toNat % 64 := by
  rw [← VG.Proof.Ocb.nonceN_byte t nonce h1 h15 (by decide), VG.Proof.Ocb.toBytes_eq, Proof.Aes.toBytes_getD _ (by decide),
    BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
  simp only [Nat.shiftRight_zero, show 8 * (15 - 15) = 0 from rfl]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

/-- `Offset_0`, from the block of `Nonce` with its last 6 bits cleared and
`bottom`. -/
theorem offset0_eq (ciph : Cipher) (t : Nat) (nonce : List Byte) :
    offset0 ciph t nonce =
      let ktop := ciph (VG.Proof.Ocb.nonceN t nonce &&& ~~~(63 : Block))
      let stretch : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)
      stretch.extractLsb' (64 - ((VG.Proof.Ocb.nonceN t nonce).extractLsb' 0 6).toNat) 128 := rfl

/-- The bytes `zeros ‖ 1 ‖ N`. -/
theorem nbase_list (nonce : List Byte) (h1 : 1 ≤ nonce.length) (h15 : nonce.length ≤ 15) {k : Nat} (hk : k < 16) :
    (zeros (15 - nonce.length) ++ [1] ++ nonce).getD k 0 = VG.Proof.Ocb.nbase nonce k := by
  unfold VG.Proof.Ocb.nbase zeros
  rw [List.getD_eq_getElem?_getD]
  by_cases h₁ : k < 15 - nonce.length
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
    simp [h₁, show k ≠ 15 - nonce.length by omega, show ¬ 16 - nonce.length ≤ k by omega]
  · by_cases h₂ : k = 15 - nonce.length
    · subst h₂
      rw [List.getElem?_append_left (by simp), List.getElem?_append_right (by simp)]
      simp
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_append, List.length_replicate, List.length_singleton, h₂, ↓reduceIte,
        show 16 - nonce.length ≤ k by omega, List.getD_eq_getElem?_getD]
      congr 2; omega

end VG.Proof.Ocb

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ocb.State`. -/
section

/-!
# OCB: blocks in memory as AES states

Untrusted: everything here is checked by Lean. The AES functions on whole
blocks are specified on AES states (`Spec.Aes.statesAt`); OCB's blocks in
memory (`blockAtMem`) are the same bytes (`blockAtMem_of_state`,
`stateAt_of_statesAt`), on every target.
-/

namespace VG.Proof.Ocb

open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem)

theorem bytesAt_toList (m : Mem) (p : Addr) : bytesAt m p 16 = (Spec.Aes.stateAt m p).toList := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp [bytesAt, Spec.Aes.stateAt]

theorem stateAt_eq (m : Mem) (p : Addr) :
    Spec.Aes.stateAt m p = Vector.ofFn fun i => (Spec.Ocb.toBytes (blockAtMem m p)).getD i.1 0 := by
  rw [blockAtMem, VG.Proof.Ocb.toBytes_ofBytes (by simp [bytesAt])]
  apply Vector.ext
  intro i hi
  simp [Spec.Aes.stateAt, bytesAt, List.getD_eq_getElem?_getD]

/-- The block at `p`, after a function of states replaced the state there. -/
theorem blockAtMem_of_state {m m' : Mem} {p : Addr} (g : Spec.Aes.State → Spec.Aes.State)
    (h : Spec.Aes.stateAt m' p = g (Spec.Aes.stateAt m p)) :
    blockAtMem m' p =
      Spec.Ocb.ofBytes (g (Vector.ofFn fun i => (Spec.Ocb.toBytes (blockAtMem m p)).getD i.1 0)).toList := by
  rw [blockAtMem, VG.Proof.Ocb.bytesAt_toList, h, VG.Proof.Ocb.stateAt_eq]

theorem stateAt_of_statesAt {m m' : Mem} {D : Addr} {n : Nat} {g : Spec.Aes.State → Spec.Aes.State}
    (h : Spec.Aes.statesAt m' D n = (Spec.Aes.statesAt m D n).map g) {i : Nat} (hi : i < n) :
    Spec.Aes.stateAt m' (D + BitVec.ofNat 64 (16 * i)) = g (Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * i))) := by
  have := congrArg (·[i]?) h
  simpa [Spec.Aes.statesAt, hi] using this

theorem blockAtMem_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAtMem m' p = blockAtMem m p := by
  rw [blockAtMem, blockAtMem, Proof.Cmac.bytesAt_frame hf hd (by decide)]

end VG.Proof.Ocb

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ocb.Stretch`. -/
section

/-!
# OCB: `Offset_0` in 64-bit words

Untrusted: everything here is checked by Lean. `Stretch` (§4.2) is 192 bits:
`Ktop` (the words `H ++ L`) and `Ktop[1..64] ⊕ Ktop[9..72]`, the word
`((H ⋘ 8) ∨ (L ⋙ 56)) ⊕ H` (`stretch_words`). An implementation shifts it
left by `bottom` (less than 64) in six stages, by 1, 2, 4, 8, 16 and 32 bits,
each kept or not by a mask from a bit of `bottom` (`sel_mask`), on three
words (`shl3`, with `ror_mask`), so that `Offset_0` is the top 128 bits
(`offset_shl`, `shl_stages`).
-/

namespace VG.Proof.Ocb

/-- Rotating right by `64 − a` and masking off the `a` low bits shifts left
by `a`. -/
theorem ror_mask (x : BitVec 64) {a : Nat} (ha : 0 < a) (ha' : a < 64) :
    x.rotateRight (64 - a) &&& (BitVec.allOnes 64 <<< a) = x <<< a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, hi, decide_true, Bool.true_and]
  by_cases hia : i < a
  · simp [hia]
  · simp only [hia, decide_false, Bool.not_false, Bool.true_and]
    simp only [BitVec.getLsbD, show i < 64 - (64 - a) ↔ i < a by omega, hia, ↓reduceIte,
      Nat.mod_eq_of_lt (show 64 - a < 64 by omega)]
    rw [show i - (64 - (64 - a)) = i - a by omega]
    simp [show i - a < 64 by omega]

/-- Bit `k` of `bottom` (less than 64), as 0 or 1. -/
theorem bit_bottom {v : Nat} (hv : v < 64) (k : Nat) :
    (BitVec.ofNat 64 v >>> k) &&& BitVec.signExtend 64 (1 : BitVec 32) =
      if v.testBit k then 1 else 0 := by
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  rw [e1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  have h2 : v / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : v / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]; omega

/-- A shift of three words left by `a` (from 1 to 63), a word at a time. -/
theorem shl3 (x y z : BitVec 64) {a : Nat} (ha : 0 < a) (ha' : a < 64) :
    (x <<< a ||| y >>> (64 - a)) ++ (y <<< a ||| z >>> (64 - a)) ++ (z <<< a) = (x ++ y ++ z) <<< a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  rcases (show i < 64 ∨ (64 ≤ i ∧ i < 128) ∨ (128 ≤ i ∧ i < 192) by omega) with h | ⟨h, h'⟩ | ⟨h, h'⟩
  · by_cases h2 : i < a
    · simp [h, h2]
    · simp [h, h2, show i - a < 64 by omega]
  · simp only [show ¬ i < 64 by omega, show i - 64 < 64 by omega, show ¬ i < a by omega, ↓reduceIte,
      decide_false, Bool.not_false, Bool.true_and]
    by_cases h2 : i - 64 < a
    · simp [h2, show i - a < 64 by omega, show 64 - a + (i - 64) = i - a by omega]
    · simp [h2, show ¬ i - a < 64 by omega, BitVec.getLsbD_of_ge z (64 - a + (i - 64)) (by omega),
        show i - a - 64 = i - 64 - a by omega, show i - 64 - a < 64 by omega]
  · simp only [show ¬ i < 64 by omega, show ¬ i - 64 < 64 by omega, show ¬ i < a by omega, ↓reduceIte,
      decide_false, Bool.not_false, Bool.true_and, show ¬ i - a < 64 by omega]
    by_cases h2 : i - 128 < a
    · simp [show i - 64 - 64 < a by omega, show i - a - 64 < 64 by omega,
        show 64 - a + (i - 64 - 64) = i - a - 64 by omega]
    · simp [show ¬ i - 64 - 64 < a by omega, show i - 64 - 64 < 64 by omega, show ¬ i - a - 64 < 64 by omega,
        BitVec.getLsbD_of_ge y (64 - a + (i - 64 - 64)) (by omega), show i - a - 64 - 64 = i - 64 - 64 - a by omega]

/-- The choice of `x'` or `x` with a mask of all ones or all zeros. -/
theorem sel_mask (x x' : BitVec 64) (b : Bool) :
    x ^^^ ((x' ^^^ x) &&& ((0 : BitVec 64) - (if b then 1 else 0))) = if b then x' else x := by
  cases b
  · simp
  · have h : (0 : BitVec 64) - 1 = BitVec.allOnes 64 := by decide
    simp only [↓reduceIte, h, BitVec.and_allOnes]
    rw [BitVec.xor_comm x' x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- `Stretch` in words. -/
theorem stretch_words (h l : BitVec 64) :
    (h ++ l) ++ ((h ++ l).extractLsb' 64 64 ^^^ (h ++ l).extractLsb' 56 64) =
      h ++ l ++ (((h <<< 8) ||| (l >>> 56)) ^^^ h) := by
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.xor_comm _ h]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hi, decide_true,
    Bool.true_and, show ¬ 64 + i < 64 by omega, ↓reduceIte, show 64 + i - 64 = i by omega]
  congr 1
  by_cases h8 : i < 8
  · simp [h8, show 56 + i < 64 by omega]
  · simp [h8, show ¬ 56 + i < 64 by omega, show 56 + i - 64 = i - 8 by omega,
      BitVec.getLsbD_of_ge l (56 + i) (by omega)]

/-- The top 128 bits of `Stretch` shifted left by `b ≤ 64` are its bits from
`64 − b`. -/
theorem offset_shl (s : BitVec 192) {b : Nat} (hb : b ≤ 64) :
    (s <<< b).extractLsb' 64 128 = s.extractLsb' (64 - b) 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    show 64 + i < 192 by omega, show ¬ 64 + i < b by omega, decide_false, Bool.not_false]
  congr 1; omega

/-- A shift left by `k` if `c`. -/
def shlIf (c : Bool) (k : Nat) (x : BitVec 192) : BitVec 192 := if c then x <<< k else x

/-- The six stages shift left by `bottom`. -/
theorem shl_stages (s : BitVec 192) {v : Nat} (hv : v < 64) :
    VG.Proof.Ocb.shlIf (v.testBit 5) 32 (VG.Proof.Ocb.shlIf (v.testBit 4) 16 (VG.Proof.Ocb.shlIf (v.testBit 3) 8 (VG.Proof.Ocb.shlIf (v.testBit 2) 4
      (VG.Proof.Ocb.shlIf (v.testBit 1) 2 (VG.Proof.Ocb.shlIf (v.testBit 0) 1 s))))) = s <<< v := by
  have key : ∀ (c : Bool) (k : Nat) (x : BitVec 192), VG.Proof.Ocb.shlIf c k x = x <<< (if c then k else 0) := by
    intro c k x; cases c <;> simp [VG.Proof.Ocb.shlIf]
  simp only [key, ← BitVec.shiftLeft_add]
  congr 1
  revert v
  decide

end VG.Proof.Ocb

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ocb.Sum`. -/
section

/-!
# OCB: the sum of `HASH` a chunk at a time

Untrusted: everything here is checked by Lean. `Sum_{j+c}` is `Sum_j` with
the `c` enciphered blocks after block `j` added (`hsum_add`); a checksum of
blocks is the spec's when the blocks are (`ckOf_eq`, `ckOf_dck`).
-/

namespace VG.Proof.Ocb

open VG.Spec.Ocb (Block Cipher blockAt)

/-- `x` XORed with `g 0`, …, `g (k − 1)`. -/
def sumOf (x : Block) (g : Nat → Block) : Nat → Block
  | 0 => x
  | k + 1 => VG.Proof.Ocb.sumOf x g k ^^^ g k

theorem hsum_add (ciph : Cipher) (l : Block) (a : List Byte) (j : Nat) :
    ∀ c, VG.Proof.Ocb.hsum ciph l a (j + c) =
      VG.Proof.Ocb.sumOf (VG.Proof.Ocb.hsum ciph l a j) (fun k => ciph (blockAt a (j + k) ^^^ VG.Proof.Ocb.offAt 0 l (j + k + 1))) c
  | 0 => rfl
  | c + 1 => by rw [← Nat.add_assoc, VG.Proof.Ocb.hsum, VG.Proof.Ocb.hsum_add ciph l a j c]; rfl

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => VG.Proof.Ocb.ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {p : List Byte} {m : Nat} (h : ∀ i < m, X i = blockAt p i) :
    VG.Proof.Ocb.ckOf X m = VG.Proof.Ocb.ckAt p m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [VG.Proof.Ocb.ckOf, VG.Proof.Ocb.ckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = VG.Proof.Ocb.decBlock inv o0 l c i) : VG.Proof.Ocb.ckOf X m = VG.Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [VG.Proof.Ocb.ckOf, VG.Proof.Ocb.dckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega)]

end VG.Proof.Ocb

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ocb.Stretch32`. -/
section

/-!
# OCB: `Offset_0` in 32-bit words

Untrusted: everything here is checked by Lean. The facts of `Stretch.lean`
for a target with 32-bit words: `Stretch` is six words (`stretch_words32`),
shifted left by `bottom` (less than 64) in six stages, each kept or not by a
mask from a bit of `bottom` (`sel_mask32`, `bit32`, `bit32_0`); the stages of
1 to 16 bits shift a word at a time (`shl6`), the stage of 32 bits moves the
words (`shl6_32`), and `Offset_0` is the top four words (`top4`).
-/

namespace VG.Proof.Ocb

/-- Shifting `X ++ y` left by `a ≤ 32` shifts `X`, fills it from the top of
`y`, and shifts `y`. -/
private theorem shl_app {n : Nat} (X : BitVec n) (y : BitVec 32) {a : Nat} (ha' : a ≤ 32) :
    (X ++ y) <<< a = ((X <<< a) ||| (y >>> (32 - a)).setWidth n) ++ (y <<< a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases h : i < 32
  · by_cases h2 : i < a
    · simp [h, h2]
    · simp [h, h2, show i - a < 32 by omega]
  · simp only [h, ↓reduceIte, show ¬ i < a by omega, decide_false, Bool.not_false, Bool.true_and,
      show i - 32 < n by omega]
    by_cases h2 : i - 32 < a
    · simp [h2, show i - a < 32 by omega, show 32 - a + (i - 32) = i - a by omega]
    · simp [h2, show ¬ i - a < 32 by omega, BitVec.getLsbD_of_ge y (32 - a + (i - 32)) (by omega),
        show i - a - 32 = i - 32 - a by omega]

/-- Or-ing a word into the low word of `P ++ q`. -/
private theorem or_setWidth_append {n : Nat} (P : BitVec n) (q r : BitVec 32) :
    (P ++ q) ||| r.setWidth (n + 32) = P ++ (q ||| r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  by_cases h : i < 32
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge r i (by omega)]

private theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] {t e : α} (h : c) : ite c t e = t := by
  simp [h]

private theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] {t e : α} (h : ¬ c) : ite c t e = e := by
  simp [h]

private theorem dec_pos {p : Prop} [Decidable p] (h : p) : decide p = true := decide_eq_true h

private theorem dec_neg {p : Prop} [Decidable p] (h : ¬ p) : decide p = false := decide_eq_false h

private theorem getLsbD_ge32 (x : BitVec 32) {k : Nat} (h : 32 ≤ k) : x.getLsbD k = false :=
  BitVec.getLsbD_of_ge x k h

/-- A shift of six 32-bit words left by `a` (from 1 to 31), a word at a time. -/
theorem shl6 (x₀ x₁ x₂ x₃ x₄ x₅ : BitVec 32) {a : Nat} (ha : 0 < a) (ha' : a < 32) :
    (x₀ <<< a ||| x₁ >>> (32 - a)) ++ (x₁ <<< a ||| x₂ >>> (32 - a)) ++ (x₂ <<< a ||| x₃ >>> (32 - a)) ++
      (x₃ <<< a ||| x₄ >>> (32 - a)) ++ (x₄ <<< a ||| x₅ >>> (32 - a)) ++ (x₅ <<< a) =
      (x₀ ++ x₁ ++ x₂ ++ x₃ ++ x₄ ++ x₅) <<< a := by
  -- `0 < a` is not needed: the shift by 0 is the identity on both sides.
  have _ := ha
  simp only [shl_app _ _ (Nat.le_of_lt ha'), or_setWidth_append, BitVec.setWidth_eq]

/-- A shift of six 32-bit words left by a word. -/
theorem shl6_32 (x₀ x₁ x₂ x₃ x₄ x₅ : BitVec 32) :
    x₁ ++ x₂ ++ x₃ ++ x₄ ++ x₅ ++ (0 : BitVec 32) = (x₀ ++ x₁ ++ x₂ ++ x₃ ++ x₄ ++ x₅) <<< 32 := by
  have hz : ∀ y : BitVec 32, y <<< 32 = 0 := fun y => BitVec.shiftLeft_eq_zero (Nat.le_refl _)
  have hz' : ∀ y : BitVec 32, (0 : BitVec 32) ||| y = y := fun y => by simp
  simp only [shl_app _ _ (Nat.le_refl 32), or_setWidth_append, BitVec.setWidth_eq, Nat.sub_self,
    BitVec.ushiftRight_zero, hz, hz']

/-- The choice of `x'` or `x` with a mask of all ones or all zeros. -/
theorem sel_mask32 (x x' : BitVec 32) (b : Bool) :
    x ^^^ ((x' ^^^ x) &&& ((0 : BitVec 32) - (if b then 1 else 0))) = if b then x' else x := by
  cases b
  · simp
  · have h : (0 : BitVec 32) - 1 = BitVec.allOnes 32 := by decide
    simp only [↓reduceIte, h, BitVec.and_allOnes]
    rw [BitVec.xor_comm x' x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Bit `k` of `bottom` (less than 64), as 0 or 1. -/
theorem bit32 {v : Nat} (hv : v < 64) (k : Nat) :
    (BitVec.ofNat 32 v >>> k) &&& BitVec.ofNat 32 1 = if v.testBit k then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show (BitVec.ofNat 32 1).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq,
    Nat.shiftRight_eq_div_pow]
  have h2 : v / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : v / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]; omega

/-- Bit 0 of `bottom`, as 0 or 1. -/
theorem bit32_0 {v : Nat} (hv : v < 64) :
    BitVec.ofNat 32 v &&& BitVec.ofNat 32 1 = if v.testBit 0 then 1 else 0 := by
  have h := bit32 hv 0
  rwa [BitVec.ushiftRight_zero] at h

/-- `Stretch` in 32-bit words: `Ktop` (the words `k₀ ++ k₁ ++ k₂ ++ k₃`, `k₀`
the most significant) and `Ktop[1..64] ⊕ Ktop[9..72]`. -/
theorem stretch_words32 (k₀ k₁ k₂ k₃ : BitVec 32) :
    (k₀ ++ k₁ ++ k₂ ++ k₃) ++ ((k₀ ++ k₁ ++ k₂ ++ k₃).extractLsb' 64 64 ^^^ (k₀ ++ k₁ ++ k₂ ++ k₃).extractLsb' 56 64) =
      k₀ ++ k₁ ++ k₂ ++ k₃ ++ (((k₀ <<< 8) ||| (k₁ >>> 24)) ^^^ k₀) ++ (((k₁ <<< 8) ||| (k₂ >>> 24)) ^^^ k₁) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨
      (96 ≤ i ∧ i < 128) ∨ (128 ≤ i ∧ i < 160) ∨ 160 ≤ i by omega)
    with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · simp (disch := omega) only [ite_pos, ite_neg, dec_pos, Bool.true_and,
      show 64 + i - 32 - 32 = i by omega, show 56 + i - 32 = 24 + i by omega]
    exact Bool.xor_comm _ _
  · simp (disch := omega) only [ite_pos, ite_neg, dec_pos, dec_neg, Bool.true_and, Bool.not_true,
      Bool.or_false, show 64 + i - 32 - 32 = i by omega, show 56 + i - 32 - 32 = i - 8 by omega,
      getLsbD_ge32]
    exact Bool.xor_comm _ _
  · simp (disch := omega) only [ite_pos, ite_neg, dec_pos, Bool.true_and,
      show 64 + i - 32 - 32 - 32 = i - 32 by omega,
      show 56 + i - 32 - 32 = i - 8 by omega, show 24 + (i - 32) = i - 8 by omega]
    exact Bool.xor_comm _ _
  · simp (disch := omega) only [ite_pos, ite_neg, dec_pos, dec_neg, Bool.true_and, Bool.not_true,
      Bool.or_false, show 64 + i - 32 - 32 - 32 = i - 32 by omega,
      show 56 + i - 32 - 32 - 32 = i - 32 - 8 by omega, getLsbD_ge32]
    exact Bool.xor_comm _ _
  all_goals simp (disch := omega) only [ite_pos, ite_neg, Nat.sub_sub, Nat.reduceAdd]

/-- The top four of six words. -/
theorem top4 (x₀ x₁ x₂ x₃ x₄ x₅ : BitVec 32) :
    (x₀ ++ x₁ ++ x₂ ++ x₃ ++ x₄ ++ x₅).extractLsb' 64 128 = x₀ ++ x₁ ++ x₂ ++ x₃ := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 64 + i < 32 by omega, show ¬ 64 + i - 32 < 32 by omega, show 64 + i - 32 - 32 = i by omega,
    ↓reduceIte]

/-! ## Words as six-word values, for x86 -/

/-- Six words, the most significant first. -/
abbrev cat6 (x0 x1 x2 x3 x4 x5 : BitVec 32) : BitVec 192 := x0 ++ x1 ++ x2 ++ x3 ++ x4 ++ x5

/-- Bit `32 k + j` of six words: bit `j` of word `5 − k`. -/
theorem getLsbD_cat6 (x0 x1 x2 x3 x4 x5 : BitVec 32) (i : Nat) :
    (cat6 x0 x1 x2 x3 x4 x5).getLsbD i =
      if i < 32 then x5.getLsbD i else if i < 64 then x4.getLsbD (i - 32) else
      if i < 96 then x3.getLsbD (i - 64) else if i < 128 then x2.getLsbD (i - 96) else
      if i < 160 then x1.getLsbD (i - 128) else x0.getLsbD (i - 160) := by
  simp only [cat6, BitVec.getLsbD_append]
  simp only [Nat.sub_sub, Nat.reduceAdd]
  by_cases h1 : i < 32
  · simp only [h1, ↓reduceIte]
  by_cases h2 : i < 64
  · simp only [h1, h2, show i - 32 < 32 by omega, ↓reduceIte]
  by_cases h3 : i < 96
  · simp only [h1, h2, h3, show ¬ i - 32 < 32 by omega, show i - 64 < 32 by omega, ↓reduceIte]
  by_cases h4 : i < 128
  · simp only [h1, h2, h3, h4, show ¬ i - 32 < 32 by omega, show ¬ i - 64 < 32 by omega,
      show i - 96 < 32 by omega, ↓reduceIte]
  by_cases h5 : i < 160
  · simp only [h1, h2, h3, h4, h5, show ¬ i - 32 < 32 by omega, show ¬ i - 64 < 32 by omega,
      show ¬ i - 96 < 32 by omega, show i - 128 < 32 by omega, ↓reduceIte]
  · simp only [h1, h2, h3, h4, h5, show ¬ i - 32 < 32 by omega, show ¬ i - 64 < 32 by omega,
      show ¬ i - 96 < 32 by omega, show ¬ i - 128 < 32 by omega, ↓reduceIte]

/-- The word `x` shifted left by `a` with the top bits of the next, `y`. -/
abbrev shlW (a : Nat) (x y : BitVec 32) : BitVec 32 := x <<< a ||| y >>> (32 - a)

theorem getLsbD_shlW (a : Nat) (ha : 0 < a) (ha' : a < 32) (x y : BitVec 32) {j : Nat} (hj : j < 32) :
    (shlW a x y).getLsbD j = if j < a then y.getLsbD (32 - a + j) else x.getLsbD (j - a) := by
  simp only [shlW, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hj, decide_true,
    Bool.true_and]
  by_cases h : j < a
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge y (32 - a + j) (by omega)]

/-- Rotating right by `32 − a` and masking off the `a` low bits shifts left
by `a`. -/
theorem ror_mask32 (x : BitVec 32) {a : Nat} (ha : 0 < a) (ha' : a < 32) :
    x.rotateRight (32 - a) &&& (BitVec.allOnes 32 <<< a) = x <<< a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, hi, decide_true, Bool.true_and]
  by_cases hia : i < a
  · simp [hia]
  · simp only [hia, decide_false, Bool.not_false, Bool.true_and]
    simp only [BitVec.getLsbD, show i < 32 - (32 - a) ↔ i < a by omega, hia, ↓reduceIte,
      Nat.mod_eq_of_lt (show 32 - a < 32 by omega)]
    rw [show i - (32 - (32 - a)) = i - a by omega]
    simp [show i - a < 32 by omega]

/-- Bit `k` of `bottom` (less than 64), as 0 or 1. -/
theorem bit_bottom32 {v : Nat} (hv : v < 64) (k : Nat) :
    (BitVec.ofNat 32 v >>> k) &&& 1 = if v.testBit k then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq,
    Nat.shiftRight_eq_div_pow]
  have h2 : v / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : v / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]; omega

theorem getLsbD_cat4 (k0 k1 k2 k3 : BitVec 32) (i : Nat) :
    (k0 ++ k1 ++ k2 ++ k3).getLsbD i =
      if i < 32 then k3.getLsbD i else if i < 64 then k2.getLsbD (i - 32) else
      if i < 96 then k1.getLsbD (i - 64) else k0.getLsbD (i - 96) := by
  simp only [BitVec.getLsbD_append]
  simp only [Nat.sub_sub, Nat.reduceAdd]
  by_cases h1 : i < 32
  · simp only [h1, ↓reduceIte]
  by_cases h2 : i < 64
  · simp only [h1, h2, show i - 32 < 32 by omega, ↓reduceIte]
  by_cases h3 : i < 96
  · simp only [h1, h2, h3, show ¬ i - 32 < 32 by omega, show i - 64 < 32 by omega, ↓reduceIte]
  · simp only [h1, h2, h3, show ¬ i - 32 < 32 by omega, show ¬ i - 64 < 32 by omega, ↓reduceIte]

end VG.Proof.Ocb

end
