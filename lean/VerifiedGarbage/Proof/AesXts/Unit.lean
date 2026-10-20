module
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Framework.Mem

import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import Std.Data.DTreeMap.Internal.Operations
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# XTS-AES of whole data units: what every target shares

Untrusted: everything here is checked by Lean, and depends on no target.
The functions on a data unit (`vg_aes_xts_encrypt_unit`,
`vg_aes_xts_decrypt_unit`) call the whole-block functions three or four
times and swap bytes between the last whole block and the partial one:

* `T = AES-enc(Key2, i)` is the whole-block encryption of `i` with a zero
  tweak (`block_zeros`);
* `aesXtsEncrypt` and `aesXtsDecrypt` are `encWith` and `decWith` of the
  ciphers and the tweak the key schedules give (`aesXtsEncrypt_eq`,
  `keys_of`);
* the swap of the first `b` bytes of the block at `L` with the `b` bytes
  after it leaves `swapMem`, which is built one byte of each at a time
  (`swapMem_step`), and holds the bytes ciphertext stealing moves
  (`bytesAt_swap_lo`, `bytesAt_swap_hi`);
* the bytes of the data unit after the calls and the swap are those of
  `encWith` and `decWith` (`enc_whole`, `enc_steal`, `dec_whole`,
  `dec_steal`), from what each call and the swap leave.
-/

@[expose] public section

namespace VG.Proof.AesXts.Unit

open VG Spec.Xts
open VG.Spec.Aes (bytesAt)
open VG.Spec.Cbc (Cipher blocksAt)

/-! ## Bytes and blocks in memory -/

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_append (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc, BitVec.ofNat_add]

theorem bytesAt_take (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    (bytesAt m p n).take a = bytesAt m p a := by
  rw [show n = a + (n - a) by omega, bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

theorem bytesAt_drop (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    (bytesAt m p n).drop a = bytesAt m (p + BitVec.ofNat 64 a) (n - a) := by
  rw [show n = a + (n - a) by omega, bytesAt_append, List.drop_left' (length_bytesAt _ _ _),
    Nat.add_sub_cancel_left]

theorem length_blocksAt (m : Mem) (p : Addr) (n : Nat) : (blocksAt m p n).length = n := by
  simp [blocksAt]

theorem blocksAt_succ (m : Mem) (p : Addr) (n : Nat) :
    blocksAt m p (n + 1) = blocksAt m p n ++ [bytesAt m (p + BitVec.ofNat 64 (16 * n)) 16] := by
  simp [blocksAt, List.range_succ]

theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [bytesAt m p 16] := by
  simp [blocksAt]

theorem flatten_blocksAt (m : Mem) (p : Addr) (n : Nat) :
    (blocksAt m p n).flatten = bytesAt m p (16 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [blocksAt_succ, List.flatten_append, ih, List.flatten_singleton,
      show 16 * (n + 1) = 16 * n + 16 by omega, bytesAt_append]

theorem blocks_bytesAt (m : Mem) (p : Addr) (n : Nat) :
    Spec.Cbc.blocks (bytesAt m p (16 * n)) = blocksAt m p n := by
  simp only [Spec.Cbc.blocks, length_bytesAt, Nat.mul_div_cancel_left _ (by decide : 0 < 16), blocksAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [bytesAt_drop _ _ (by omega), bytesAt_take _ _ (by omega)]

/-! ## The swap -/

/-- `m` with the first `k` bytes at `L` swapped with the `k` bytes at
`L + 16` (`k ≤ 16`). -/
def swapMem (m : Mem) (L : Addr) (k : Nat) : Mem := fun x =>
  if (x - L).toNat < k then m (x + 16) else
  if 16 ≤ (x - L).toNat ∧ (x - L).toNat < 16 + k then m (x - 16) else m x

theorem swapMem_zero (m : Mem) (L : Addr) : swapMem m L 0 = m := by
  funext x
  simp only [swapMem, Nat.not_lt_zero, ite_false, Nat.add_zero]
  rw [ite_eq_right (by omega)]

theorem eq_add_iff (x L : Addr) {j : Nat} (hj : j < 2 ^ 64) :
    x = L + BitVec.ofNat 64 j ↔ (x - L).toNat = j := by
  constructor
  · rintro rfl; exact Mem.sub_ofNat_toNat L hj
  · intro h
    have : x - L = BitVec.ofNat 64 j := BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj])
    rw [← this, BitVec.add_comm, BitVec.sub_add_cancel]

theorem add16_of (x L : Addr) {j : Nat} (h : (x - L).toNat = j) (hj : j + 16 < 2 ^ 64) :
    x + 16 = L + BitVec.ofNat 64 (16 + j) := by
  rw [(eq_add_iff x L (by omega)).mpr h, BitVec.add_assoc, Nat.add_comm, BitVec.ofNat_add]; rfl

theorem sub16_of (x L : Addr) {j : Nat} (h : (x - L).toNat = 16 + j) (hj : 16 + j < 2 ^ 64) :
    x - 16 = L + BitVec.ofNat 64 j := by
  rw [(eq_add_iff x L hj).mpr h, Nat.add_comm, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem swapMem_lo (m : Mem) (L : Addr) {k i : Nat} (hk : k ≤ i) (hi : i < 16) :
    swapMem m L k (L + BitVec.ofNat 64 i) = m (L + BitVec.ofNat 64 i) := by
  simp only [swapMem, Mem.sub_ofNat_toNat L (show i < 2 ^ 64 by omega)]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem swapMem_hi (m : Mem) (L : Addr) {k i : Nat} (hk : k ≤ i) (hi : i < 16) :
    swapMem m L k (L + BitVec.ofNat 64 (16 + i)) = m (L + BitVec.ofNat 64 (16 + i)) := by
  simp only [swapMem, Mem.sub_ofNat_toNat L (show 16 + i < 2 ^ 64 by omega)]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem swapMem_step (m : Mem) (L : Addr) {k : Nat} (hk : k < 16) :
    ((swapMem m L k).writeW (L + BitVec.ofNat 64 k) (m (L + BitVec.ofNat 64 (16 + k)))).writeW
      (L + BitVec.ofNat 64 (16 + k)) (m (L + BitVec.ofNat 64 k)) = swapMem m L (k + 1) := by
  funext x
  rw [WriteBytes.writeW8_apply, WriteBytes.writeW8_apply]
  have hd := (x - L).isLt
  by_cases h₁ : x = L + BitVec.ofNat 64 (16 + k)
  · have e := (eq_add_iff x L (by omega)).mp h₁
    rw [ite_eq_left h₁]
    simp only [swapMem]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), sub16_of x L e (by omega)]
  · have e₁ : (x - L).toNat ≠ 16 + k := fun h => h₁ ((eq_add_iff x L (by omega)).mpr h)
    rw [ite_eq_right h₁]
    by_cases h₂ : x = L + BitVec.ofNat 64 k
    · have e := (eq_add_iff x L (by omega)).mp h₂
      rw [ite_eq_left h₂]
      simp only [swapMem]
      rw [ite_eq_left (by omega), add16_of x L e (by omega)]
    · have e₂ : (x - L).toNat ≠ k := fun h => h₂ ((eq_add_iff x L (by omega)).mpr h)
      rw [ite_eq_right h₂]
      simp only [swapMem]
      by_cases a : (x - L).toNat < k
      · simp only [a, show (x - L).toNat < k + 1 by omega, ite_true]
      · simp only [a, show ¬ (x - L).toNat < k + 1 by omega, ite_false]
        by_cases c : 16 ≤ (x - L).toNat ∧ (x - L).toNat < 16 + k
        · simp only [c, show 16 ≤ (x - L).toNat ∧ (x - L).toNat < 16 + (k + 1) by omega]
        · simp only [c, show ¬ (16 ≤ (x - L).toNat ∧ (x - L).toNat < 16 + (k + 1)) by omega, ite_false]

theorem swapMem_frame (m : Mem) (L : Addr) (b : Nat) :
    Frame [⟨L, 16 + b⟩] m (swapMem m L b) := by
  intro x hx
  have hc := hx _ List.mem_cons_self
  simp only [Region.Contains] at hc
  simp only [swapMem]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem bytesAt_swap_lo (m : Mem) (L : Addr) {b : Nat} (hb : b ≤ 16) :
    bytesAt (swapMem m L b) L 16 = bytesAt m (L + 16) b ++ (bytesAt m L 16).drop b := by
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro k h₁ h₂
  rw [length_bytesAt] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  by_cases hk : k < b
  · rw [List.getElem_append_left (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range, swapMem, Mem.sub_ofNat_toNat L (show k < 2 ^ 64 by omega),
      hk, ite_true]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 k)]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_map, List.length_range, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [show b + (k - b) = k by omega, swapMem_lo m L (by omega) (by omega)]

theorem bytesAt_swap_hi (m : Mem) (L : Addr) {b : Nat} (hb : b ≤ 16) :
    bytesAt (swapMem m L b) (L + 16) b = (bytesAt m L 16).take b := by
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro k h₁ h₂
  rw [length_bytesAt] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take]
  have e : L + 16 + BitVec.ofNat 64 k = L + BitVec.ofNat 64 (16 + k) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl
  rw [e]
  simp only [swapMem, Mem.sub_ofNat_toNat L (show 16 + k < 2 ^ 64 by omega)]
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  congr 1
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 16), ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

/-! ## The spec, from the ciphers and the tweak -/

/-- XTS-AES encryption of the data unit `p` (at least 16 bytes) with
`AES-enc(Key1, ·)` `enc` and the tweak `T = t`: `aesXtsEncrypt` once the
key schedules are known. -/
def encWith (enc : Cipher) (t p : List Byte) : List Byte :=
  let m := p.length / 16
  let b := p.length % 16
  if b = 0 then (crypt enc t (Spec.Cbc.blocks p)).flatten else
  let head := (crypt enc t (Spec.Cbc.blocks (p.take (16 * (m - 1))))).flatten
  let cc := block enc (next t (m - 1)) ((p.drop (16 * (m - 1))).take 16)
  let pp := p.drop (16 * m) ++ cc.drop b
  head ++ block enc (next t m) pp ++ cc.take b

/-- XTS-AES decryption of the data unit `c` with `AES-dec(Key1, ·)` `dec`
and the tweak `T = t`. -/
def decWith (dec : Cipher) (t c : List Byte) : List Byte :=
  let m := c.length / 16
  let b := c.length % 16
  if b = 0 then (crypt dec t (Spec.Cbc.blocks c)).flatten else
  let head := (crypt dec t (Spec.Cbc.blocks (c.take (16 * (m - 1))))).flatten
  let pp := block dec (next t m) ((c.drop (16 * (m - 1))).take 16)
  let cc := c.drop (16 * m) ++ pp.drop b
  head ++ block dec (next t (m - 1)) cc ++ pp.take b

theorem aesXtsEncrypt_eq {key i p : List Byte} {enc dec : Cipher} {t : List Byte}
    (hk : keys key i = (enc, dec, t)) (hp : 16 ≤ p.length) :
    aesXtsEncrypt key i p = some (encWith enc t p) := by
  simp only [aesXtsEncrypt, hk, encWith, show ¬ p.length < 16 by omega, ite_false]
  split <;> rfl

theorem aesXtsDecrypt_eq {key i c : List Byte} {enc dec : Cipher} {t : List Byte}
    (hk : keys key i = (enc, dec, t)) (hc : 16 ≤ c.length) :
    aesXtsDecrypt key i c = some (decWith dec t c) := by
  simp only [aesXtsDecrypt, hk, decWith, show ¬ c.length < 16 by omega, ite_false]
  split <;> rfl

/-- The ciphers and the tweak of a key whose schedules are at `W` and `K`. -/
theorem keys_of {mem : Mem} {W K : Addr} {R : Nat} {key : List Byte} (i : List Byte)
    (h : KeySchedules mem W K R key) :
    keys key i = (Spec.Cbc.aesWith R (bytesAt mem W (16 * (R + 1))),
      Spec.Cbc.aesInvWith R (bytesAt mem W (16 * (R + 1))),
      Spec.Cbc.aesWith R (bytesAt mem K (16 * (R + 1))) i) := by
  obtain ⟨hl, hR, hW, hK⟩ := h
  have e : (key.drop (key.length / 2)).length / 4 = (key.take (key.length / 2)).length / 4 := by
    simp only [List.length_drop, List.length_take]; omega
  simp only [keys, hW, hK, e, ← hR]

/-! ## The tweak -/

theorem length_aesWith (R : Nat) (w x : List Byte) : (Spec.Cbc.aesWith R w x).length = 16 := by
  simp [Spec.Cbc.aesWith]

theorem xor_zeros {x : List Byte} (h : x.length = 16) : Spec.Cbc.xor x (List.replicate 16 0) = x := by
  apply List.ext_getElem (by simp [Spec.Cbc.xor, h])
  intro k h₁ h₂
  simp only [Spec.Cbc.xor, List.getElem_zipWith, List.getElem_replicate]
  exact BitVec.xor_zero

/-- The whole-block encryption of `x` with a zero tweak is `x` enciphered. -/
theorem block_zeros (R : Nat) (w : List Byte) {x : List Byte} (hx : x.length = 16) :
    block (Spec.Cbc.aesWith R w) (List.replicate 16 0) x = Spec.Cbc.aesWith R w x := by
  rw [block, xor_zeros hx, xor_zeros (length_aesWith _ _ _)]

/-- What the call computing the tweak leaves at `p`. -/
theorem tweak_of {m₁ m₂ : Mem} {p : Addr} {R : Nat} {w z : List Byte}
    (h : blocksAt m₂ p 1 = crypt (Spec.Cbc.aesWith R w) z (blocksAt m₁ p 1)) (hz : z = List.replicate 16 0) :
    bytesAt m₂ p 16 = Spec.Cbc.aesWith R w (bytesAt m₁ p 16) := by
  rw [blocksAt_one, blocksAt_one] at h
  simp only [crypt, List.length_singleton, tweaks, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.cons.injEq, and_true] at h
  rw [h, hz, block_zeros _ _ (length_bytesAt _ _ _)]

/-- What a call on one block leaves. -/
theorem crypt_one_of {m m' : Mem} {p : Addr} {ciph : Cipher} {t : List Byte}
    (h : blocksAt m' p 1 = crypt ciph t (blocksAt m p 1)) : bytesAt m' p 16 = block ciph t (bytesAt m p 16) := by
  rw [blocksAt_one, blocksAt_one] at h
  simp only [crypt, List.length_singleton, tweaks, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.cons.injEq, and_true] at h
  exact h

/-! ## The data unit -/

theorem add16 (p : Addr) (a : Nat) : p + BitVec.ofNat 64 a + 16 = p + BitVec.ofNat 64 (a + 16) :=
  Offset.add_add p a 16

section
variable {m₀ : Mem} {D : Addr} {M b : Nat}

theorem enc_whole {enc : Cipher} {t : List Byte} {m₃ : Mem}
    (h₃ : blocksAt m₃ D M = crypt enc t (blocksAt m₀ D M)) :
    bytesAt m₃ D (16 * M) = encWith enc t (bytesAt m₀ D (16 * M)) := by
  simp only [encWith, length_bytesAt, show 16 * M % 16 = 0 by omega, ite_true]
  rw [blocks_bytesAt, ← h₃, flatten_blocksAt]

theorem dec_whole {dec : Cipher} {t : List Byte} {m₃ : Mem}
    (h₃ : blocksAt m₃ D M = crypt dec t (blocksAt m₀ D M)) :
    bytesAt m₃ D (16 * M) = decWith dec t (bytesAt m₀ D (16 * M)) := by
  simp only [decWith, length_bytesAt, show 16 * M % 16 = 0 by omega, ite_true]
  rw [blocks_bytesAt, ← h₃, flatten_blocksAt]

/-- The bytes of the data unit, in three parts. -/
theorem bytesAt_three (m : Mem) (D : Addr) (M b : Nat) (hM : 1 ≤ M) :
    bytesAt m D (16 * M + b) = bytesAt m D (16 * (M - 1)) ++
      bytesAt m (D + BitVec.ofNat 64 (16 * (M - 1))) 16 ++
      bytesAt m (D + BitVec.ofNat 64 (16 * (M - 1)) + 16) b := by
  rw [show 16 * M + b = 16 * (M - 1) + 16 + b by omega, bytesAt_append, bytesAt_append, add16]

/-- The parts of the data unit on entry. -/
theorem parts (m : Mem) (D : Addr) (hM : 1 ≤ M) (hb : b < 16) :
    let p := bytesAt m D (16 * M + b)
    p.take (16 * (M - 1)) = bytesAt m D (16 * (M - 1)) ∧
    (p.drop (16 * (M - 1))).take 16 = bytesAt m (D + BitVec.ofNat 64 (16 * (M - 1))) 16 ∧
    p.drop (16 * M) = bytesAt m (D + BitVec.ofNat 64 (16 * (M - 1)) + 16) b ∧
    p.length / 16 = M ∧ p.length % 16 = b := by
  refine ⟨bytesAt_take _ _ (by omega), ?_, ?_, ?_, ?_⟩
  · rw [bytesAt_drop _ _ (by omega), bytesAt_take _ _ (by omega)]
  · rw [bytesAt_drop _ _ (by omega), add16, show 16 * (M - 1) + 16 = 16 * M by omega,
      show 16 * M + b - 16 * M = b by omega]
  · rw [length_bytesAt]; omega
  · rw [length_bytesAt]; omega

/-- Encryption with a partial block: `m₃` after the call on the `M` whole
blocks from `t`, `m₅` after the swap and the call on the last whole block
from the tweak of block `M`. -/
theorem enc_steal {enc : Cipher} {t : List Byte} {m₃ m₅ : Mem} (hM : 1 ≤ M) (hb : 0 < b) (hb16 : b < 16)
    (h₃ : blocksAt m₃ D M = crypt enc t (blocksAt m₀ D M))
    (h₃t : bytesAt m₃ (D + BitVec.ofNat 64 (16 * (M - 1)) + 16) b =
      bytesAt m₀ (D + BitVec.ofNat 64 (16 * (M - 1)) + 16) b)
    (h₅ : let L := D + BitVec.ofNat 64 (16 * (M - 1))
      bytesAt m₅ L 16 = block enc (next t M) (bytesAt (swapMem m₃ L b) L 16) ∧
      bytesAt m₅ D (16 * (M - 1)) = bytesAt m₃ D (16 * (M - 1)) ∧
      bytesAt m₅ (L + 16) b = bytesAt (swapMem m₃ L b) (L + 16) b) :
    bytesAt m₅ D (16 * M + b) = encWith enc t (bytesAt m₀ D (16 * M + b)) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := parts m₀ D (M := M) (b := b) hM hb16
  obtain ⟨h5L, h5H, h5T⟩ := h₅
  have hs : blocksAt m₀ D M = blocksAt m₀ D (M - 1) ++ [bytesAt m₀ (D + BitVec.ofNat 64 (16 * (M - 1))) 16] := by
    rw [← blocksAt_succ, Nat.sub_add_cancel hM]
  have hs₃ : blocksAt m₃ D M = blocksAt m₃ D (M - 1) ++ [bytesAt m₃ (D + BitVec.ofNat 64 (16 * (M - 1))) 16] := by
    rw [← blocksAt_succ, Nat.sub_add_cancel hM]
  rw [hs, crypt_snoc, hs₃, length_blocksAt] at h₃
  obtain ⟨hh, hc⟩ := List.append_inj' h₃ rfl
  simp only [List.cons.injEq, and_true] at hc
  simp only [encWith, p4, p5, show b ≠ 0 by omega, ite_false, p1, p2, p3]
  rw [bytesAt_three _ _ _ _ hM, h5L, h5H, h5T, bytesAt_swap_lo _ _ (by omega), bytesAt_swap_hi _ _ (by omega),
    h₃t, hc, ← flatten_blocksAt, hh, blocks_bytesAt]

/-- Decryption with a partial block: `m₃` after the call on the first
`M - 1` whole blocks from `t`, `m₅` after the call on the last whole block
from the tweak of block `M`, and `m₇` after the swap and the call on the
last whole block from the tweak of block `M - 1`. -/
theorem dec_steal {dec : Cipher} {t : List Byte} {m₃ m₅ m₇ : Mem} (hM : 1 ≤ M) (hb : 0 < b) (hb16 : b < 16)
    (h₃ : blocksAt m₃ D (M - 1) = crypt dec t (blocksAt m₀ D (M - 1)))
    (h₃L : let L := D + BitVec.ofNat 64 (16 * (M - 1))
      bytesAt m₃ L 16 = bytesAt m₀ L 16 ∧ bytesAt m₃ (L + 16) b = bytesAt m₀ (L + 16) b)
    (h₅ : let L := D + BitVec.ofNat 64 (16 * (M - 1))
      bytesAt m₅ L 16 = block dec (next t M) (bytesAt m₃ L 16) ∧
      bytesAt m₅ D (16 * (M - 1)) = bytesAt m₃ D (16 * (M - 1)) ∧
      bytesAt m₅ (L + 16) b = bytesAt m₃ (L + 16) b)
    (h₇ : let L := D + BitVec.ofNat 64 (16 * (M - 1))
      bytesAt m₇ L 16 = block dec (next t (M - 1)) (bytesAt (swapMem m₅ L b) L 16) ∧
      bytesAt m₇ D (16 * (M - 1)) = bytesAt m₅ D (16 * (M - 1)) ∧
      bytesAt m₇ (L + 16) b = bytesAt (swapMem m₅ L b) (L + 16) b) :
    bytesAt m₇ D (16 * M + b) = decWith dec t (bytesAt m₀ D (16 * M + b)) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := parts m₀ D (M := M) (b := b) hM hb16
  obtain ⟨h3L, h3T⟩ := h₃L
  obtain ⟨h5L, h5H, h5T⟩ := h₅
  obtain ⟨h7L, h7H, h7T⟩ := h₇
  simp only [decWith, p4, p5, show b ≠ 0 by omega, ite_false, p1, p2, p3]
  rw [bytesAt_three _ _ _ _ hM, h7L, h7H, h7T, bytesAt_swap_lo _ _ (by omega), bytesAt_swap_hi _ _ (by omega),
    h5L, h5H, h5T, h3L, h3T, ← flatten_blocksAt, h₃, blocks_bytesAt]

end

end VG.Proof.AesXts.Unit
