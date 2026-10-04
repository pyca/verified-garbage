import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Dbl32

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
  rw [← ofBytes_toBytes x, h, ofBytes_toBytes]

/-- XOR of blocks is XOR of their bytes. -/
theorem toBytes_xor (x y : Block) : toBytes (x ^^^ y) = Spec.Ocb.xor (toBytes x) (toBytes y) := by
  refine Proof.Cmac.ext16 (toBytes_length _) (by simp [Spec.Ocb.xor, toBytes_length]) fun k hk => ?_
  rw [toBytes_eq, Proof.Aes.toBytes_xor x y hk, xor_eq,
    Proof.Cmac.getD_xor (by simp [Proof.Cmac.toBytes_length]) (by rw [Proof.Cmac.toBytes_length]; exact hk)]

theorem ofBytes_xor {xs ys : List Byte} (hx : xs.length = 16) (hy : ys.length = 16) :
    ofBytes (Spec.Ocb.xor xs ys) = ofBytes xs ^^^ ofBytes ys := by
  apply toBytes_inj
  rw [toBytes_xor, toBytes_ofBytes hx, toBytes_ofBytes hy,
    toBytes_ofBytes (by simp [Spec.Ocb.xor, hx, hy])]

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
    · rw [ntzAux_succ f (n / 2) (by omega)]

theorem ntzAux_ge {f n : Nat} (h : n ≤ f) : ntzAux f n = ntz n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, ntzAux_succ _ _ (by omega), ih (by omega)]

theorem ntz_odd {n : Nat} (h : n % 2 = 1) : ntz n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show (if k + 1 = 0 ∨ (k + 1) % 2 = 1 then 0 else ntzAux k ((k + 1) / 2) + 1) = 0
  exact ite_eq_left_iff.mpr fun hn => absurd (.inr h) hn

theorem ntz_even {n : Nat} (h0 : 0 < n) (h : n % 2 = 0) : ntz n = ntz (n / 2) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show (if k + 1 = 0 ∨ (k + 1) % 2 = 1 then 0 else ntzAux k ((k + 1) / 2) + 1) = _
  simp only [show ¬(k + 1 = 0 ∨ (k + 1) % 2 = 1) by omega, ↓reduceIte]
  rw [ntzAux_ge (by omega)]

/-! ## The folds over the whole blocks -/

/-- `Offset_i`, from `Offset_0 = o0`. -/
def offAt (o0 l : Block) : Nat → Block
  | 0 => o0
  | i + 1 => offAt o0 l i ^^^ lAt l (ntz (i + 1))

/-- `Checksum_i` of the plaintext `p`. -/
def ckAt (p : List Byte) : Nat → Block
  | 0 => 0
  | i + 1 => ckAt p i ^^^ blockAt p i

/-- `Sum_i` of `HASH` of `a`. -/
def hsum (ciph : Cipher) (l : Block) (a : List Byte) : Nat → Block
  | 0 => 0
  | i + 1 => hsum ciph l a i ^^^ ciph (blockAt a i ^^^ offAt 0 l (i + 1))

/-- `C_1 ‖ … ‖ C_m`. -/
def encBlocks (ciph : Cipher) (o0 l : Block) (p : List Byte) (m : Nat) : List Byte :=
  (List.range m).flatMap fun i => toBytes (offAt o0 l (i + 1) ^^^ ciph (blockAt p i ^^^ offAt o0 l (i + 1)))

/-- `P_i` of the ciphertext `c`. -/
def decBlock (inv : Cipher) (o0 l : Block) (c : List Byte) (i : Nat) : Block :=
  offAt o0 l (i + 1) ^^^ inv (blockAt c i ^^^ offAt o0 l (i + 1))

/-- `P_1 ‖ … ‖ P_m`. -/
def decBlocks (inv : Cipher) (o0 l : Block) (c : List Byte) (m : Nat) : List Byte :=
  (List.range m).flatMap fun i => toBytes (decBlock inv o0 l c i)

/-- `Checksum_i` of the decrypted ciphertext `c`. -/
def dckAt (inv : Cipher) (o0 l : Block) (c : List Byte) : Nat → Block
  | 0 => 0
  | i + 1 => dckAt inv o0 l c i ^^^ decBlock inv o0 l c i

theorem hash_fold (ciph : Cipher) (l : Block) (a : List Byte) (m : Nat) :
    (List.range m).foldl (fun (sum, offset) i =>
      let offset := offset ^^^ lAt l (ntz (i + 1))
      (sum ^^^ ciph (blockAt a i ^^^ offset), offset)) ((0 : Block), (0 : Block)) =
      (hsum ciph l a m, offAt 0 l m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem enc_fold (ciph : Cipher) (l o0 : Block) (p : List Byte) (m : Nat) :
    (List.range m).foldl (fun (offset, checksum, c) i =>
      let offset := offset ^^^ lAt l (ntz (i + 1))
      (offset, checksum ^^^ blockAt p i, c ++ toBytes (offset ^^^ ciph (blockAt p i ^^^ offset))))
      (o0, (0 : Block), ([] : List Byte)) =
      (offAt o0 l m, ckAt p m, encBlocks ciph o0 l p m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, encBlocks, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl

theorem dec_fold (inv : Cipher) (l o0 : Block) (c : List Byte) (m : Nat) :
    (List.range m).foldl (fun (offset, checksum, p) i =>
      let offset := offset ^^^ lAt l (ntz (i + 1))
      let pi := offset ^^^ inv (blockAt c i ^^^ offset)
      (offset, checksum ^^^ pi, p ++ toBytes pi))
      (o0, (0 : Block), ([] : List Byte)) =
      (offAt o0 l m, dckAt inv o0 l c m, decBlocks inv o0 l c m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, decBlocks, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl

/-- `HASH`, from the sum and the offset of its whole blocks. -/
theorem hash_eq (ciph : Cipher) (l : Block) (a : List Byte) :
    Spec.Ocb.hash ciph l a =
      if (a.drop (16 * (a.length / 16))).length > 0 then
        hsum ciph l a (a.length / 16) ^^^
          ciph (pad (a.drop (16 * (a.length / 16))) ^^^ (offAt 0 l (a.length / 16) ^^^ l))
      else hsum ciph l a (a.length / 16) := by
  unfold Spec.Ocb.hash
  simp only [hash_fold]

/-- `OCB-ENCRYPT`, from the offset, the checksum and the output of its whole
blocks. -/
theorem encryptWith_eq (ciph : Cipher) (l : Block) (t : Nat) (nonce a p : List Byte) :
    encryptWith ciph l t nonce a p =
      let m := p.length / 16
      let o := offAt (offset0 ciph t nonce) l m
      let ck := ckAt p m
      let c := encBlocks ciph (offset0 ciph t nonce) l p m
      let rest := p.drop (16 * m)
      if rest.length > 0 then
        (c ++ Spec.Ocb.xor rest (toBytes (ciph (o ^^^ l))),
          (toBytes (ciph (ck ^^^ pad rest ^^^ (o ^^^ l) ^^^ lDollar l) ^^^ Spec.Ocb.hash ciph l a)).take t)
      else (c, (toBytes (ciph (ck ^^^ o ^^^ lDollar l) ^^^ Spec.Ocb.hash ciph l a)).take t) := by
  unfold encryptWith
  simp only [enc_fold]
  split <;> rfl

/-- `OCB-DECRYPT`, from the offset, the checksum and the output of its whole
blocks. -/
theorem decryptWith_eq (ciph inv : Cipher) (l : Block) (t : Nat) (nonce a c tag : List Byte) :
    decryptWith ciph inv l t nonce a c tag =
      let m := c.length / 16
      let o := offAt (offset0 ciph t nonce) l m
      let ck := dckAt inv (offset0 ciph t nonce) l c m
      let p := decBlocks inv (offset0 ciph t nonce) l c m
      let rest := c.drop (16 * m)
      let (p, tag') :=
        if rest.length > 0 then
          let ps := Spec.Ocb.xor rest (toBytes (ciph (o ^^^ l)))
          (p ++ ps, ciph (ck ^^^ pad ps ^^^ (o ^^^ l) ^^^ lDollar l) ^^^ Spec.Ocb.hash ciph l a)
        else (p, ciph (ck ^^^ o ^^^ lDollar l) ^^^ Spec.Ocb.hash ciph l a)
      if (toBytes tag').take t = tag then some p else none := by
  unfold decryptWith
  simp only [dec_fold]

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
  rw [← bytesAt_slice m p (a := a) (b := n - a) (n := n) (by omega),
    List.take_of_length_le (by simp [Spec.Aes.bytesAt])]

/-- Block `i` of the bytes at `p`. -/
theorem blockAt_bytesAt (m : Mem) (p : Addr) {n i : Nat} (h : 16 * (i + 1) ≤ n) :
    blockAt (Spec.Aes.bytesAt m p n) i = blockAtMem m (p + BitVec.ofNat 64 (16 * i)) := by
  rw [blockAt, bytesAt_slice m p (by omega), blockAtMem]

/-- The bytes of `k` blocks, a block at a time. -/
theorem bytesAt_blocks (m : Mem) (p : Addr) (k : Nat) :
    Spec.Aes.bytesAt m p (16 * k) =
      (List.range k).flatMap fun i => Spec.Aes.bytesAt m (p + BitVec.ofNat 64 (16 * i)) 16 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 16 * (k + 1) = 16 * k + 16 by omega, bytesAt_append, ih, List.range_succ,
      List.flatMap_append]
    simp

end VG.Proof.Ocb
