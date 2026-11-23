module

public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.ByteMap
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# A look-up in a table of 256 bytes with `pshufb` on x86 (32-bit)

A table of 256 bytes is sixteen rows of sixteen. A byte `x` is looked up in
it, in every byte of a register at once, by reading every row through
`pshufb` with the row's *index vector* and ORing what the rows give: the
index vector of row `r` holds, in the byte whose index is `x`, the low
nibble of `x` if its high nibble is `r`, and `0x80` ORed with it otherwise,
for which `pshufb` gives zero. The index vector is `pshufb(C, H) | L`
(`idx`), for the constant row `C` that is zero at byte `r` and `0x80`
elsewhere, and the registers `H` and `L` of the indices' high and low
nibbles.

`byte_acc`: the rows `0` to `15` through their index vectors, ORed (`acc`),
hold in each byte the table's byte at that byte's index: byte `x & 15` of
row `x >> 4`. Nothing here is about a machine state: the code that computes
`idx` and `acc` is each cipher's.

`byte_gather`: four registers' doublewords 0 put together by two
`punpckldq`, a `punpcklqdq` and a `pshufb` with the bytes
`0, 4, 8, 12, 1, 5, …` hold in byte `p` of doubleword `k` the byte `k` of
register `p`: four byte planes' look-ups as entries of four bytes.
-/

@[expose] public section

namespace VG.X86.ByteLookup

open VG VG.X86 VG.X86.ByteMap

/-- The index vector of the row whose constant is `C`, for the indices' high
nibbles `H` and low nibbles `L`. -/
def idx (C H L : BitVec 128) : BitVec 128 := XBinOp.eval .por (XBinOp.eval .pshufb C H) L

/-- The rows `0` to `n`, each through its index vector, ORed: each row into
what the rows before it gave. -/
def acc (rows V : Nat → BitVec 128) : Nat → BitVec 128
  | 0 => XBinOp.eval .pshufb (rows 0) (V 0)
  | n + 1 => XBinOp.eval .por (XBinOp.eval .pshufb (rows (n + 1)) (V (n + 1))) (acc rows V n)

/-- `acc` reads the index vectors of the rows `0` to `n` only. -/
theorem acc_congr {rows V V' : Nat → BitVec 128} (n : Nat) (h : ∀ r ≤ n, V r = V' r) :
    acc rows V n = acc rows V' n := by
  induction n with
  | zero => rw [acc, acc, h 0 (Nat.le_refl 0)]
  | succ n ih => rw [acc, acc, h (n + 1) (Nat.le_refl _), ih fun r hr => h r (Nat.le_succ_of_le hr)]

/-- A byte of a doubleword is a byte of the register. -/
theorem byte_of_dword (v : BitVec 128) (k : Nat) {p : Nat} (hp : p < 4) :
    (dword v k).extractLsb' (8 * p) 8 = byte v (4 * k + p) := by
  rw [byte_eq_dword, show (4 * k + p) / 4 = k by omega_using [hp], show (4 * k + p) % 4 = p by omega_using [hp]]

theorem byte_or (a b : BitVec 128) (i : Nat) : byte (a ||| b) i = byte a i ||| byte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, hr, decide_true, Bool.true_and]

/-- What the look-up needs of a byte's nibbles. -/
theorem nibbles (x : BitVec 8) :
    (x >>> 4).msb = false ∧ ((x >>> 4).extractLsb' 0 4).toNat = (x >>> 4).toNat ∧
      (x &&& 0x0f#8).msb = false ∧ ((x &&& 0x0f#8).extractLsb' 0 4).toNat = (x &&& 0x0f#8).toNat ∧
      (0x80#8 ||| (x &&& 0x0f#8)).msb = true ∧ (x >>> 4).toNat < 16 ∧ (x &&& 0x0f#8).toNat < 16 ∧
      16 * (x >>> 4).toNat + (x &&& 0x0f#8).toNat = x.toNat := by
  have h : ∀ n < 256, ((BitVec.ofNat 8 n) >>> 4).msb = false ∧
      (((BitVec.ofNat 8 n) >>> 4).extractLsb' 0 4).toNat = ((BitVec.ofNat 8 n) >>> 4).toNat ∧
      ((BitVec.ofNat 8 n) &&& 0x0f#8).msb = false ∧
      (((BitVec.ofNat 8 n) &&& 0x0f#8).extractLsb' 0 4).toNat = ((BitVec.ofNat 8 n) &&& 0x0f#8).toNat ∧
      (0x80#8 ||| ((BitVec.ofNat 8 n) &&& 0x0f#8)).msb = true ∧ ((BitVec.ofNat 8 n) >>> 4).toNat < 16 ∧
      ((BitVec.ofNat 8 n) &&& 0x0f#8).toNat < 16 ∧
      16 * ((BitVec.ofNat 8 n) >>> 4).toNat + ((BitVec.ofNat 8 n) &&& 0x0f#8).toNat = (BitVec.ofNat 8 n).toNat := by
    decide +kernel
  have e := h x.toNat x.isLt
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at e
  exact e

/-- A byte of the index vector of row `r`. -/
theorem byte_idx {C H L : BitVec 128} {x : BitVec 8} {r i : Nat} (hi : i < 16)
    (hC : ∀ b < 16, byte C b = if b = r then 0#8 else 0x80#8) (hH : byte H i = x >>> 4)
    (hL : byte L i = x &&& 0x0f#8) :
    byte (idx C H L) i = if (x >>> 4).toNat = r then x &&& 0x0f#8 else 0x80#8 ||| (x &&& 0x0f#8) := by
  obtain ⟨m, e, -, -, -, lt, -, -⟩ := nibbles x
  rw [idx, show XBinOp.eval .por (XBinOp.eval .pshufb C H) L = XBinOp.eval .pshufb C H ||| L from rfl, byte_or,
    byte_pshufb _ _ hi, hH, hL, m, e, hC _ lt]
  by_cases h : (x >>> 4).toNat = r
  · rw [ite_eq_left h, ite_eq_left h]; simp
  · rw [ite_eq_right h, ite_eq_right h]; simp

/-- A byte of a row read through its index vector: the row's byte at the
index's low nibble where the index's high nibble is the row's number. -/
theorem byte_row {row V : BitVec 128} {x : BitVec 8} {r i : Nat} (hi : i < 16)
    (hV : byte V i = if (x >>> 4).toNat = r then x &&& 0x0f#8 else 0x80#8 ||| (x &&& 0x0f#8)) :
    byte (XBinOp.eval .pshufb row V) i = if (x >>> 4).toNat = r then byte row (x &&& 0x0f#8).toNat else 0#8 := by
  obtain ⟨-, -, m, e, m', -, -, -⟩ := nibbles x
  rw [byte_pshufb _ _ hi, hV]
  by_cases h : (x >>> 4).toNat = r
  · rw [ite_eq_left h, ite_eq_left h, m, e]; simp
  · rw [ite_eq_right h, ite_eq_right h, m']; simp

/-- A byte of the rows `0` to `n`: the table's byte, if its row is among them. -/
theorem byte_acc_le {rows V : Nat → BitVec 128} {x : BitVec 8} {i : Nat} (hi : i < 16)
    (hV : ∀ r < 16, byte (V r) i = if (x >>> 4).toNat = r then x &&& 0x0f#8 else 0x80#8 ||| (x &&& 0x0f#8))
    (n : Nat) (hn : n < 16) :
    byte (acc rows V n) i = if (x >>> 4).toNat ≤ n then byte (rows (x >>> 4).toNat) (x &&& 0x0f#8).toNat else 0#8 := by
  induction n with
  | zero =>
    rw [acc, byte_row hi (hV 0 hn)]
    by_cases h : (x >>> 4).toNat = 0
    · rw [ite_eq_left h, ite_eq_left (Nat.le_of_eq h), h]
    · rw [ite_eq_right h, ite_eq_right (by omega_using [h])]
  | succ n ih =>
    rw [acc, show ∀ a b : BitVec 128, XBinOp.eval .por a b = a ||| b from fun _ _ => rfl, byte_or,
      byte_row hi (hV (n + 1) hn), ih (by omega_using [hn])]
    by_cases h : (x >>> 4).toNat = n + 1
    · rw [ite_eq_left h, ite_eq_right (by omega_using [h]), ite_eq_left (Nat.le_of_eq h), h]; simp
    · rw [ite_eq_right h]
      by_cases h' : (x >>> 4).toNat ≤ n
      · rw [ite_eq_left h', ite_eq_left (by omega_using [h'])]; simp
      · rw [ite_eq_right h', ite_eq_right (by omega_using [h, h'])]; simp

/-- **The look-up.** With the sixteen rows' index vectors made from the
constant rows `C r` and the indices' nibbles, the sixteen rows ORed hold in
byte `i` the table's byte at the index `x` of that byte. -/
theorem byte_acc {rows C : Nat → BitVec 128} {H L : BitVec 128} {x : BitVec 8} {i : Nat} (hi : i < 16)
    (hC : ∀ r < 16, ∀ b < 16, byte (C r) b = if b = r then 0#8 else 0x80#8) (hH : byte H i = x >>> 4)
    (hL : byte L i = x &&& 0x0f#8) :
    byte (acc rows (fun r => idx (C r) H L) 15) i = byte (rows (x >>> 4).toNat) (x &&& 0x0f#8).toNat := by
  rw [byte_acc_le hi (fun r hr => byte_idx hi (hC r hr) hH hL) 15 (by decide),
    ite_eq_left (by have := (nibbles x).2.2.2.2.2.1; omega_using [this])]

/-- The nibbles of the bytes of `X`, as code makes them with the mask `M` of
`0x0f` in every byte: the high ones by a shift of the doublewords and the
mask, the low ones by the mask. -/
theorem byte_hi {X M : BitVec 128} {i : Nat} (hi : i < 16) (hM : byte M i = 0x0f#8) :
    byte (XBinOp.eval .pand (XShiftOp.eval .psrld X 4) M) i = byte X i >>> 4 :=
  byte_hi4 X M hi hM

theorem byte_lo {X M : BitVec 128} {i : Nat} (hM : byte M i = 0x0f#8) :
    byte (XBinOp.eval .pand X M) i = byte X i &&& 0x0f#8 := by
  rw [show XBinOp.eval .pand X M = X &&& M from rfl, byte_and, hM]

/-- Four registers' doublewords 0, a byte of each in every doubleword. -/
def gather (a0 a1 a2 a3 T : BitVec 128) : BitVec 128 :=
  XBinOp.eval .pshufb (XBinOp.eval .punpcklqdq (XBinOp.eval .punpckldq a0 a1) (XBinOp.eval .punpckldq a2 a3)) T

/-- Byte `k` of doubleword `q` of four doublewords. -/
theorem byte_at (d0 d1 d2 d3 : BitVec 32) {q k : Nat} (hq : q < 4) (hk : k < 4) :
    byte (ofDwords d0 d1 d2 d3) (4 * q + k) = ([d0, d1, d2, d3].getD q 0).extractLsb' (8 * k) 8 := by
  rw [byte_eq_dword, show (4 * q + k) / 4 = q by omega_using [hk], show (4 * q + k) % 4 = k by omega_using [hk]]
  rcases cases4 hq with rfl | rfl | rfl | rfl
  · rw [dword_ofDwords_0]; rfl
  · rw [dword_ofDwords_1]; rfl
  · rw [dword_ofDwords_2]; rfl
  · rw [dword_ofDwords_3]; rfl

/-- Byte `k` of a register's doubleword 0. -/
theorem byte_low (v : BitVec 128) {k : Nat} (hk : k < 4) : byte v k = (dword v 0).extractLsb' (8 * k) 8 := by
  rw [byte_eq_dword, show k / 4 = 0 by omega_using [hk], show k % 4 = k by omega_using [hk]]

/-- Byte `p` of doubleword `k` of `gather` is byte `k` of register `p`. -/
theorem byte_gather {a : Nat → BitVec 128} {T : BitVec 128}
    (hT : ∀ i < 16, byte T i = BitVec.ofNat 8 (4 * (i % 4) + i / 4)) {k p : Nat} (hk : k < 4) (hp : p < 4) :
    byte (gather (a 0) (a 1) (a 2) (a 3) T) (4 * k + p) = byte (a p) k := by
  have e : (BitVec.ofNat 8 (4 * p + k)).msb = false ∧
      ((BitVec.ofNat 8 (4 * p + k)).extractLsb' 0 4).toNat = 4 * p + k :=
    (by decide : ∀ k < 4, ∀ p < 4, (BitVec.ofNat 8 (4 * p + k)).msb = false ∧
      ((BitVec.ofNat 8 (4 * p + k)).extractLsb' 0 4).toNat = 4 * p + k) k hk p hp
  have hi : 4 * k + p < 16 := by omega_using [hk, hp]
  rw [gather, byte_pshufb _ _ hi, hT _ hi, show (4 * k + p) % 4 = p by omega_using [hp],
    show (4 * k + p) / 4 = k by omega_using [hp], e.1, e.2, ite_eq_right Bool.false_ne_true,
    byte_punpcklqdq _ _ (by omega_using [hk, hp]), punpckldq_eq, punpckldq_eq, byte_low _ hk]
  rcases cases4 hp with rfl | rfl | rfl | rfl
  · rw [ite_eq_left (by omega_using [hk]), byte_at _ _ _ _ (by decide) hk]; rfl
  · rw [ite_eq_left (by omega_using [hk]), byte_at _ _ _ _ (by decide) hk]; rfl
  · rw [ite_eq_right (by omega_using [hk]), show 4 * 2 + k - 8 = 4 * 0 + k by omega_using [hk],
      byte_at _ _ _ _ (by decide) hk]; rfl
  · rw [ite_eq_right (by omega_using [hk]), show 4 * 3 + k - 8 = 4 * 1 + k by omega_using [hk],
      byte_at _ _ _ _ (by decide) hk]; rfl

end VG.X86.ByteLookup
