module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Tail
public import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Tbl

/-!
# AES-GCM on AArch64, the last bytes: their bytes

Untrusted: everything here is checked by Lean. The bytes `tbl` leaves with
the indices of `Tail.ksTail` and `Tail.padVec`: the keystream block moved up
by `16 - r` bytes, XORed into the 16 bytes that end the text and stored back,
leaves the memory `crTail` leaves (`ks_mem`); and the 16 bytes that end the
text moved down are its last `r` bytes padded with zeros, each doubleword's
bytes reversed as `loadRev` leaves a block (`pad_vec`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Tail

open VG VG.AArch64 VG.WriteBytes
open VG.Impl.AesGcm.AArch64.Tail (idxTable)
open VG.Spec.Aes (bytesAt)

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

/-- The indices `0, …, 15`, as `ldrqTbl` loads them. -/
abbrev iotaV : BitVec 128 := idxTable.getD 1 0 ++ idxTable.getD 0 0

/-- The indices of `rev64`, as `ldrqTbl` loads them. -/
abbrev revV : BitVec 128 := idxTable.getD 3 0 ++ idxTable.getD 2 0

/-- Byte `i` of a block, its doublewords' bytes reversed: byte `rv i`. -/
def rv (i : Nat) : Nat := 8 * (i / 8) + 7 - i % 8

theorem vbyte_iotaV : ∀ i < 16, vbyte iotaV i = BitVec.ofNat 8 i := by decide

theorem vbyte_revV : ∀ i < 16, vbyte revV i = BitVec.ofNat 8 (rv i) := by decide

theorem rv_lt : ∀ i < 16, rv i < 16 := by decide

/-- The indices of `ksTail`: below `16 - r`, 16 or more; from there, `i - (16 - r)`. -/
theorem up_idx : ∀ r < 16, ∀ i < 16,
    ((BitVec.ofNat 8 i - BitVec.ofNat 8 (16 - r)).toNat < 16 ↔ 16 - r ≤ i) ∧
    (16 - r ≤ i → (BitVec.ofNat 8 i - BitVec.ofNat 8 (16 - r)).toNat = i - (16 - r)) := by
  decide

/-- The indices of `padVec`: `rv i + 16 - r`, less than 16 exactly when `rv i < r`. -/
theorem down_idx : ∀ r < 16, 0 < r → ∀ i < 16,
    ((BitVec.ofNat 8 (rv i) + BitVec.ofNat 8 (16 - r)).toNat < 16 ↔ rv i < r) ∧
    (rv i < r → (BitVec.ofNat 8 (rv i) + BitVec.ofNat 8 (16 - r)).toNat = rv i + (16 - r)) := by
  decide

/-- The keystream block `K` moved up by `16 - r` bytes, as `ksTail`'s `tbl`
leaves it. -/
def upV (K : BitVec 128) (r : Nat) : BitVec 128 :=
  ofVBytes fun i =>
    if (vbyte (VArr.b16.map2 (fun _ x y => x - y) iotaV
        (ofVBytes fun _ => (BitVec.ofNat 64 (16 - r)).setWidth 8)) i).toNat < 16 then
      vbyte K (vbyte (VArr.b16.map2 (fun _ x y => x - y) iotaV
        (ofVBytes fun _ => (BitVec.ofNat 64 (16 - r)).setWidth 8)) i).toNat
    else 0

theorem setWidth_ofNat8 (k : Nat) : (BitVec.ofNat 64 k).setWidth 8 = BitVec.ofNat 8 k := by
  simp only [BitVec.setWidth_ofNat_of_le (show 8 ≤ 64 by decide)]

theorem vbyte_upV (K : BitVec 128) {r : Nat} (hr : r < 16) {i : Nat} (hi : i < 16) :
    vbyte (upV K r) i = if 16 - r ≤ i then vbyte K (i - (16 - r)) else 0 := by
  rw [upV, vbyte_ofVBytes _ hi]
  simp only [VArr.map2, vbyte_ofVBytes _ hi, vbyte_iotaV i hi, setWidth_ofNat8]
  obtain ⟨h₁, h₂⟩ := up_idx r hr i hi
  by_cases h : 16 - r ≤ i
  · rw [ite_t (h₁.mpr h), ite_t h, h₂ h]
  · rw [ite_f (fun e => h (h₁.mp e)), ite_f h]

/-- Distance from `E` to `x`, past `c` bytes. -/
theorem toNat_sub_add (x E : Addr) {c : Nat} (hc : c < 16) :
    (x - (E + BitVec.ofNat 64 c)).toNat < 16 - c ↔ c ≤ (x - E).toNat ∧ (x - E).toNat < 16 := by
  have e : x - (E + BitVec.ofNat 64 c) = (x - E) - BitVec.ofNat 64 c := by
    exact Offset.sub_add_eq _ _ _
  rw [e, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := (x - E).isLt
  rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
  constructor
  · intro h
    by_contra hn
    have : (x - E).toNat < c ∨ 16 ≤ (x - E).toNat := by omega
    rcases this with h' | h'
    · rw [show 2 ^ 64 - c + (x - E).toNat = 2 ^ 64 - (c - (x - E).toNat) by omega,
        Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [show 2 ^ 64 - c + (x - E).toNat = 2 ^ 64 + ((x - E).toNat - c) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)] at h
      omega
  · rintro ⟨h₁, h₂⟩
    rw [show 2 ^ 64 - c + (x - E).toNat = 2 ^ 64 + ((x - E).toNat - c) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega)]
    omega

theorem toNat_sub_add_eq (x E : Addr) {c : Nat} (hc : c < 16) (h : c ≤ (x - E).toNat)
    (h' : (x - E).toNat < 16) : (x - (E + BitVec.ofNat 64 c)).toNat = (x - E).toNat - c := by
  have e : x - (E + BitVec.ofNat 64 c) = (x - E) - BitVec.ofNat 64 c := by
    exact Offset.sub_add_eq _ _ _
  rw [e, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega),
    show 2 ^ 64 - c + (x - E).toNat = 2 ^ 64 + ((x - E).toNat - c) by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (by omega)]

theorem eq_add_toNat (x E : Addr) : x = E + BitVec.ofNat 64 (x - E).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

theorem xorBytes_getD (m : Mem) (D S : Addr) {n k : Nat} (hk : k < n) :
    (xorBytes m D S n).getD k 0 = m (D + BitVec.ofNat 64 k) ^^^ m (S + BitVec.ofNat 64 k) := by
  simp [xorBytes, bytesAt, List.getD_eq_getElem?_getD, hk]

/-- The 16 bytes at `E`, XORed with the block at `S` moved up by `16 - r`
bytes and stored back: the `r` bytes from `E + 16 - r` XORed with the first
`r` bytes at `S`. -/
theorem ks_mem (m : Mem) (E S : Addr) {r : Nat} (hr : r < 16) :
    m.write E 16 (m.read E 16 ^^^ upV (m.read S 16) r) =
      writeBytes m (E + BitVec.ofNat 64 (16 - r)) (xorBytes m (E + BitVec.ofNat 64 (16 - r)) S r) := by
  funext x
  have hlen := length_xorBytes m (E + BitVec.ofNat 64 (16 - r)) S r
  have hc : 16 - r < 16 ∨ r = 0 := by omega
  simp only [Mem.write, writeBytes, hlen]
  by_cases ht : (x - E).toNat < 16
  · rw [ite_t ( ht)]
    have hb : (m.read E 16 ^^^ upV (m.read S 16) r).extractLsb' (8 * (x - E).toNat) 8 =
        vbyte (m.read E 16) (x - E).toNat ^^^ vbyte (upV (m.read S 16) r) (x - E).toNat := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]
    rw [hb, vbyte, Mem.extractLsb'_read m E ht, vbyte_upV _ hr ht, ← eq_add_toNat]
    by_cases hu : 16 - r ≤ (x - E).toNat
    · rcases hc with hc | hc
      · have hl : (x - (E + BitVec.ofNat 64 (16 - r))).toNat < r := by
          have := (toNat_sub_add x E hc).mpr ⟨hu, ht⟩; omega
        rw [ite_t ( hu), ite_t ( hl), toNat_sub_add_eq x E hc hu ht, vbyte, Mem.extractLsb'_read m S (by omega)]
        rw [xorBytes_getD _ _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
          show 16 - r + ((x - E).toNat - (16 - r)) = (x - E).toNat by omega, ← eq_add_toNat]
      · subst hc; omega
    · have hl : ¬ (x - (E + BitVec.ofNat 64 (16 - r))).toNat < r := by
        rcases hc with hc | hc
        · intro h; exact hu ((toNat_sub_add x E hc).mp (by omega)).1
        · omega
      rw [ite_f ( hu), ite_f ( hl)]
      exact BitVec.xor_zero
  · rw [ite_f ( ht)]
    have hl : ¬ (x - (E + BitVec.ofNat 64 (16 - r))).toNat < r := by
      rcases hc with hc | hc
      · intro h; exact ht ((toNat_sub_add x E hc).mp (by omega)).2
      · omega
    rw [ite_f ( hl)]

/-- The `r` bytes at `P` padded with zeros to a block, in a memory of their
own (at address 0). -/
def padMem (m : Mem) (P : Addr) (r : Nat) : Mem :=
  writeBytes m 0 (bytesAt m P r ++ Spec.Gcm.zeros (16 - r))

theorem blockAt_padMem (m : Mem) (P : Addr) {r : Nat} (hr : r ≤ 16) :
    Spec.Gcm.blockAt (padMem m P r) 0 = Spec.Gcm.ofBytes (bytesAt m P r ++ Spec.Gcm.zeros (16 - r)) := by
  have hl : (bytesAt m P r ++ Spec.Gcm.zeros (16 - r)).length = 16 := by
    simp [length_bytesAt, Spec.Gcm.zeros]; omega
  have e := bytesAt_writeBytes_self m 0 (bytesAt m P r ++ Spec.Gcm.zeros (16 - r)) (by rw [hl]; decide)
  rw [hl] at e
  rw [Spec.Gcm.blockAt, padMem, e]

/-- Byte `k` of the padded block. -/
theorem padMem_at (m : Mem) (P : Addr) {r k : Nat} (hr : r ≤ 16) (hk : k < 16) :
    padMem m P r (0 + BitVec.ofNat 64 k) = if k < r then m (P + BitVec.ofNat 64 k) else 0 := by
  have hl : (bytesAt m P r ++ Spec.Gcm.zeros (16 - r)).length = 16 := by
    simp [length_bytesAt, Spec.Gcm.zeros]; omega
  have ha : ((0 : Addr) + BitVec.ofNat 64 k - 0).toNat = k := by
    simp [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  simp only [padMem, writeBytes, hl, ha, hk, ↓reduceIte]
  by_cases h : k < r
  · rw [ite_t (h), List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [length_bytesAt]; exact h)]
    simp [bytesAt, h]
  · rw [ite_f (h), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [length_bytesAt]; omega)]
    simp only [Spec.Gcm.zeros, length_bytesAt, List.getElem?_replicate]
    rw [ite_t ((by omega))]
    rfl

/-- The 16 bytes `X` moved down by `16 - r` bytes into the bytes of a block
padded with zeros, each doubleword's bytes reversed, as `padVec`'s `tbl`
leaves them. -/
def downV (X : BitVec 128) (r : Nat) : BitVec 128 :=
  ofVBytes fun i =>
    if (vbyte (VArr.b16.map2 (fun _ x y => x + y) revV
        (ofVBytes fun _ => (BitVec.ofNat 64 (16 - r)).setWidth 8)) i).toNat < 16 then
      vbyte X (vbyte (VArr.b16.map2 (fun _ x y => x + y) revV
        (ofVBytes fun _ => (BitVec.ofNat 64 (16 - r)).setWidth 8)) i).toNat
    else 0

/-- The 16 bytes at `E`, moved down (`downV`): the `r` bytes from
`E + 16 - r` padded, as `loadRev` leaves them. -/
theorem pad_vec (m : Mem) (E : Addr) {r : Nat} (hr0 : 0 < r) (hr : r < 16) :
    downV (m.read E 16) r = VRevOp.eval .rev64b ((padMem m (E + BitVec.ofNat 64 (16 - r)) r).read 0 16) := by
  apply Tbl.vbyte_ext
  intro i hi
  rw [downV, vbyte_ofVBytes _ hi, VRevOp.eval, vbyte_ofVBytes _ hi]
  simp only [VArr.map2, vbyte_ofVBytes _ hi, vbyte_revV i hi, setWidth_ofNat8]
  have hrv : 8 * (i / 8) + (7 - i % 8) = rv i := by simp only [rv]; omega
  simp only [hrv, vbyte]
  rw [Mem.extractLsb'_read (padMem m _ r) 0 (rv_lt i hi), padMem_at _ _ (by omega) (rv_lt i hi)]
  obtain ⟨h₁, h₂⟩ := down_idx r hr hr0 i hi
  by_cases h : rv i < r
  · rw [ite_t (h₁.mpr h), ite_t h, h₂ h, Mem.extractLsb'_read _ _ (by omega), BitVec.add_assoc,
      ← BitVec.ofNat_add, Nat.add_comm]
  · rw [ite_f (fun e => h (h₁.mp e)), ite_f h]

end VG.Proof.AesGcm.AArch64.Tail
