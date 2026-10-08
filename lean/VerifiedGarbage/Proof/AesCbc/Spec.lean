import VerifiedGarbage.Spec.Cbc.Contract
import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# CBC: the mode one block at a time, and blocks in memory

Untrusted: everything here is checked by Lean. The functions implemented in
assembly encrypt or decrypt one block at a time: CBC of the first `k + 1`
blocks is CBC of the first `k`, followed by the block that chains from the
last ciphertext block of those (`encrypt_snoc`, `decrypt_snoc`). Each block
is enciphered by AES's functions on whole blocks, which are specified on AES
states (`aesWith_state`, `aesInvWith_state`), and transformed in place: the
blocks in memory after it are those before it with one replaced
(`blocksAt_set`). On every target, where the proofs cover both directions
at once: `cbc enc` is encryption or decryption, `ciphOf enc` the cipher it
uses, and `cts enc` its ciphertext blocks (the output or the input), the last
of which is the chaining value to continue from.
-/

namespace VG.Proof.AesCbc

open VG Spec.Cbc
open VG.Spec.Aes (bytesAt)

theorem xor_eq : Spec.Cbc.xor = Spec.Cmac.xor := rfl

/-! ## Either direction -/

/-- The cipher of a direction, with `R` rounds and the key schedule `w`. -/
def ciphOf (enc : Bool) (R : Nat) (w : List Byte) : Spec.Cbc.Cipher :=
  if enc then Spec.Cbc.aesWith R w else Spec.Cbc.aesInvWith R w

/-- CBC in a direction. -/
def cbc (enc : Bool) (ciph : Spec.Cbc.Cipher) (iv : List Byte) (xs : List (List Byte)) :
    List (List Byte) :=
  if enc then Spec.Cbc.encrypt ciph iv xs else Spec.Cbc.decrypt ciph iv xs

/-- The ciphertext blocks of a direction: the output, or the input. -/
def cts (enc : Bool) (xs ys : List (List Byte)) : List (List Byte) := if enc then ys else xs


theorem length_encrypt (ciph : Cipher) (iv : List Byte) (xs : List (List Byte)) :
    (encrypt ciph iv xs).length = xs.length := by
  induction xs generalizing iv with
  | nil => rfl
  | cons _ _ ih => simp [encrypt, ih]

theorem length_decrypt (ciph : Cipher) (iv : List Byte) (xs : List (List Byte)) :
    (decrypt ciph iv xs).length = xs.length := by
  induction xs generalizing iv with
  | nil => rfl
  | cons _ _ ih => simp [decrypt, ih]

theorem next_cons (iv c : List Byte) (cs : List (List Byte)) : next iv (c :: cs) = next c cs := by
  simp only [next, List.getLastD_eq_getLast?, List.getLast?_cons, Option.getD_some]

theorem next_snoc (iv : List Byte) (cs : List (List Byte)) (c : List Byte) : next iv (cs ++ [c]) = c := by
  simp [next]

theorem encrypt_snoc (ciph : Cipher) (iv : List Byte) (xs : List (List Byte)) (x : List Byte) :
    encrypt ciph iv (xs ++ [x]) = encrypt ciph iv xs ++ [ciph (xor x (next iv (encrypt ciph iv xs)))] := by
  induction xs generalizing iv with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append, encrypt, ih, next_cons]

theorem decrypt_snoc (ciph : Cipher) (iv : List Byte) (xs : List (List Byte)) (x : List Byte) :
    decrypt ciph iv (xs ++ [x]) = decrypt ciph iv xs ++ [xor (ciph x) (next iv xs)] := by
  induction xs generalizing iv with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append, decrypt, ih, next_cons]

/-! ## Blocks in memory -/

theorem length_blocksAt (m : Mem) (p : Addr) (n : Nat) : (blocksAt m p n).length = n := by
  simp [blocksAt]

theorem getElem_blocksAt (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (blocksAt m p n)[k]'(by rw [length_blocksAt]; exact hk) = bytesAt m (p + BitVec.ofNat 64 (16 * k)) 16 := by
  simp [blocksAt]

/-- The blocks after one of them changed. -/
theorem blocksAt_set {m m' : Mem} {p : Addr} {n k : Nat}
    (h : ∀ j < n, j ≠ k →
      bytesAt m' (p + BitVec.ofNat 64 (16 * j)) 16 = bytesAt m (p + BitVec.ofNat 64 (16 * j)) 16) :
    blocksAt m' p n = (blocksAt m p n).set k (bytesAt m' (p + BitVec.ofNat 64 (16 * k)) 16) := by
  apply List.ext_getElem (by simp [length_blocksAt])
  intro j h₁ h₂
  rw [length_blocksAt] at h₁
  rw [List.getElem_set, getElem_blocksAt _ _ h₁]
  by_cases hj : k = j
  · subst hj; simp
  · simp only [hj, ↓reduceIte]; rw [getElem_blocksAt _ _ h₁, h j h₁ (Ne.symm hj)]

/-- The first `k` blocks transformed and the rest not, with block `k`
replaced. -/
theorem set_prefix {α : Type} (ys xs : List α) (x : α) {k : Nat} (hy : ys.length = k) (hk : k < xs.length) :
    (ys ++ xs.drop k).set k x = (ys ++ [x]) ++ xs.drop (k + 1) := by
  subst hy
  rw [List.set_append_right _ _ (by omega), Nat.sub_self, List.append_assoc]
  congr 1
  rw [List.drop_eq_getElem_cons hk, List.set_cons_zero]
  rfl

/-! ## AES on one block -/

theorem bytesAt_toList (m : Mem) (p : Addr) : bytesAt m p 16 = (Spec.Aes.stateAt m p).toList := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp [bytesAt, Spec.Aes.stateAt]

theorem ofFn_bytesAt (m : Mem) (p : Addr) :
    (Vector.ofFn fun i : Fin 16 => (bytesAt m p 16).getD i.1 0) = Spec.Aes.stateAt m p := by
  apply Vector.ext
  intro i hi
  simp [Spec.Aes.stateAt, bytesAt, List.getD_eq_getElem?_getD]

theorem aesWith_state (nr : Nat) (w : List Byte) (m : Mem) (p : Addr) :
    aesWith nr w (bytesAt m p 16) = (Spec.Aes.cipher nr w (Spec.Aes.stateAt m p)).toList := by
  rw [aesWith, ofFn_bytesAt]

theorem aesInvWith_state (nr : Nat) (w : List Byte) (m : Mem) (p : Addr) :
    aesInvWith nr w (bytesAt m p 16) = (Spec.Aes.invCipher nr w (Spec.Aes.stateAt m p)).toList := by
  rw [aesInvWith, ofFn_bytesAt]

/-- The block at `D` after a function of states on one block replaced it. -/
theorem bytesAt_of_statesAt {m m' : Mem} {D : Addr} {g : Spec.Aes.State → Spec.Aes.State}
    (h : Spec.Aes.statesAt m' D 1 = (Spec.Aes.statesAt m D 1).map g) :
    bytesAt m' D 16 = (g (Spec.Aes.stateAt m D)).toList := by
  have := congrArg (·[0]?) h
  simp only [Spec.Aes.statesAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
    BitVec.add_zero, List.getElem?_cons_zero, Option.some.injEq] at this
  rw [bytesAt_toList, this]

end VG.Proof.AesCbc
