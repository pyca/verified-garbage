module

public import VerifiedGarbage.Impl.MlKem.X86_64.Encode12Avx2
public import VerifiedGarbage.Proof.MlKem.Bits
public import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Vec
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
meta import VerifiedGarbage.Impl.MlKem.X86_64.Encode12Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncodeAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncodeAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.YNttPack
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttPack
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.MlKem.X86_64.NttRegs
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
import VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp
meta import VerifiedGarbage.Impl.MlKem.X86_64.NttRegs
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
meta import VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp

/-!
# ML-KEM on x86-64: `vg_mlkem_encode12_avx2`

The numbers the registers hold. In each lane of a half (`e12Half`), the
eight words `w` of the coefficients become the doublewords `w₂ₖ + 2¹² w₂ₖ₊₁`
(`dword_pairV`), whose three low bytes `vpshufb` packs into the number
`Σ 2²⁴ᵏ (w₂ₖ + 2¹² w₂ₖ₊₁)` (`toNat_shufV`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.E12Y

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open CEY (toNat_eq_dwords toNat_ofBytes toNat_byte toNat_dword')
open VG.Proof.Sha3.X86_64 (WP.cons)
open S4 (LUpd wp_vbin wp_vld256 wp_vpermd wp_vst256 wp_addi' GUpd itT itF)
open D12Y (wp_vsh wp_subi' wp_vzu wp_mov32i yconst4_ok)

/-! ## A lane -/

/-- The pairs of the words of a lane, as the shifts and `vpaddd` make them. -/
abbrev pairV (X : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddd (XShiftOp.eval .psrld (XShiftOp.eval .pslld X 16) 16)
    (XShiftOp.eval .pslld (XShiftOp.eval .psrld X 16) 12)

theorem toNat_word (x : BitVec 128) (i : Nat) : (word x i).toNat = x.toNat / 2 ^ (16 * i) % 2 ^ 16 := by
  rw [word, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem toNat_dword_words (x : BitVec 128) (k : Nat) :
    (dword x k).toNat = (word x (2 * k)).toNat + 65536 * (word x (2 * k + 1)).toNat := by
  rw [toNat_dword', toNat_word, toNat_word, show 16 * (2 * k + 1) = 32 * k + 16 by omega,
    show 16 * (2 * k) = 32 * k by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x.toNat / 2 ^ (32 * k) = z
  omega

theorem dword_pairV (X : BitVec 128) {k : Nat} (hk : k < 4) :
    (dword (pairV X) k).toNat = (word X (2 * k)).toNat + 4096 * (word X (2 * k + 1)).toNat := by
  rw [dword_paddd _ _ hk, dword_psrld _ _ (by decide) hk, dword_pslld _ _ (by decide) hk,
    dword_pslld _ _ (by decide) hk, dword_psrld _ _ (by decide) hk, BitVec.toNat_add, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, toNat_dword_words]
  have h0 := (word X (2 * k)).isLt
  have h1 := (word X (2 * k + 1)).isLt
  simp only [show (16 : BitVec 8).toNat = 16 from rfl, show (12 : BitVec 8).toNat = 12 from rfl,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  generalize (word X (2 * k)).toNat = a at h0 ⊢
  generalize (word X (2 * k + 1)).toNat = b at h1 ⊢
  omega

/-- The mask of `vpshufb` in each lane. -/
def shufM : BitVec 128 := 0x808080800e0d0c0a0908060504020100#128

/-- The three low bytes of each doubleword, together. -/
abbrev shufV (P : BitVec 128) : BitVec 128 := XBinOp.eval .pshufb P shufM

theorem toNat_byte_dword (x : BitVec 128) (k e : Nat) (he : e < 4) :
    (byte x (4 * k + e)).toNat = (dword x k).toNat / 2 ^ (8 * e) % 256 := by
  rw [toNat_byte, toNat_dword', show 8 * (4 * k + e) = 32 * k + 8 * e by omega, Nat.pow_add,
    ← Nat.div_div_eq_div_mul]
  generalize x.toNat / 2 ^ (32 * k) = z
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;> omega

theorem toNat_shufV (P : BitVec 128) (h : ∀ k < 4, (dword P k).toNat < 2 ^ 24) :
    (shufV P).toNat = (dword P 0).toNat + 2 ^ 24 * (dword P 1).toNat + 2 ^ 48 * (dword P 2).toNat +
      2 ^ 72 * (dword P 3).toNat := by
  have b : ∀ k e, k < 4 → e < 3 → (byte P (4 * k + e)).toNat = (dword P k).toNat / 2 ^ (8 * e) % 256 :=
    fun k e _ he => toNat_byte_dword P k e (by omega)
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have e00 := b 0 0 (by decide) (by decide)
  have e01 := b 0 1 (by decide) (by decide)
  have e02 := b 0 2 (by decide) (by decide)
  have e10 := b 1 0 (by decide) (by decide)
  have e11 := b 1 1 (by decide) (by decide)
  have e12 := b 1 2 (by decide) (by decide)
  have e20 := b 2 0 (by decide) (by decide)
  have e21 := b 2 1 (by decide) (by decide)
  have e22 := b 2 2 (by decide) (by decide)
  have e30 := b 3 0 (by decide) (by decide)
  have e31 := b 3 1 (by decide) (by decide)
  have e32 := b 3 2 (by decide) (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reducePow] at e00 e01 e02 e10 e11 e12 e20 e21 e22 e30 e31 e32
  rw [shufV, XBinOp.eval, toNat_ofBytes]
  simp only [show byte shufM 0 = 0 by decide, show byte shufM 1 = 1 by decide, show byte shufM 2 = 2 by decide,
    show byte shufM 3 = 4 by decide, show byte shufM 4 = 5 by decide, show byte shufM 5 = 6 by decide,
    show byte shufM 6 = 8 by decide, show byte shufM 7 = 9 by decide, show byte shufM 8 = 10 by decide,
    show byte shufM 9 = 12 by decide, show byte shufM 10 = 13 by decide, show byte shufM 11 = 14 by decide,
    show byte shufM 12 = 0x80 by decide, show byte shufM 13 = 0x80 by decide, show byte shufM 14 = 0x80 by decide,
    show byte shufM 15 = 0x80 by decide]
  simp only [show (0 : BitVec 8).msb = false by decide, show (1 : BitVec 8).msb = false by decide, show (2 : BitVec 8).msb = false by decide, show (4 : BitVec 8).msb = false by decide, show (5 : BitVec 8).msb = false by decide, show (6 : BitVec 8).msb = false by decide, show (8 : BitVec 8).msb = false by decide, show (9 : BitVec 8).msb = false by decide, show (10 : BitVec 8).msb = false by decide, show (12 : BitVec 8).msb = false by decide, show (13 : BitVec 8).msb = false by decide, show (14 : BitVec 8).msb = false by decide, show (0x80 : BitVec 8).msb = true by decide, Bool.false_eq_true, ite_true, ite_false]
  simp only [show (BitVec.extractLsb' 0 4 (0 : BitVec 8)).toNat = 0 by decide, show (BitVec.extractLsb' 0 4 (1 : BitVec 8)).toNat = 1 by decide, show (BitVec.extractLsb' 0 4 (2 : BitVec 8)).toNat = 2 by decide, show (BitVec.extractLsb' 0 4 (4 : BitVec 8)).toNat = 4 by decide, show (BitVec.extractLsb' 0 4 (5 : BitVec 8)).toNat = 5 by decide, show (BitVec.extractLsb' 0 4 (6 : BitVec 8)).toNat = 6 by decide, show (BitVec.extractLsb' 0 4 (8 : BitVec 8)).toNat = 8 by decide, show (BitVec.extractLsb' 0 4 (9 : BitVec 8)).toNat = 9 by decide, show (BitVec.extractLsb' 0 4 (10 : BitVec 8)).toNat = 10 by decide, show (BitVec.extractLsb' 0 4 (12 : BitVec 8)).toNat = 12 by decide, show (BitVec.extractLsb' 0 4 (13 : BitVec 8)).toNat = 13 by decide, show (BitVec.extractLsb' 0 4 (14 : BitVec 8)).toNat = 14 by decide]
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22, e30, e31, e32, show (0 : BitVec 8).toNat = 0 from rfl]
  omega

/-- A lane of a half: the eight 12-bit words as one number. -/
theorem lane_val {Y : BitVec 128} (h : ∀ e < 8, (word Y e).toNat < 4096) :
    (shufV (pairV Y)).toNat = (word Y 0).toNat + 2 ^ 12 * (word Y 1).toNat + 2 ^ 24 * (word Y 2).toNat +
      2 ^ 36 * (word Y 3).toNat + 2 ^ 48 * (word Y 4).toNat + 2 ^ 60 * (word Y 5).toNat +
      2 ^ 72 * (word Y 6).toNat + 2 ^ 84 * (word Y 7).toNat := by
  have p : ∀ k < 4, (dword (pairV Y) k).toNat = (word Y (2 * k)).toNat + 4096 * (word Y (2 * k + 1)).toNat :=
    fun k hk => dword_pairV Y hk
  have p0 := p 0 (by decide)
  have p1 := p 1 (by decide)
  have p2 := p 2 (by decide)
  have p3 := p 3 (by decide)
  have w := fun e (he : e < 8) => h e he
  have w0 := w 0 (by decide)
  have w1 := w 1 (by decide)
  have w2 := w 2 (by decide)
  have w3 := w 3 (by decide)
  have w4 := w 4 (by decide)
  have w5 := w 5 (by decide)
  have w6 := w 6 (by decide)
  have w7 := w 7 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at p0 p1 p2 p3
  rw [toNat_shufV _ fun k hk => by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> omega, p0, p1, p2, p3]
  omega

/-! ## Across the lanes -/

/-- Doubleword `q` of two lanes. -/
theorem dword256 (h l : BitVec 128) {q : Nat} (hq : q < 8) :
    (h ++ l).extractLsb' (32 * q) 32 = if q < 4 then dword l q else dword h (q - 4) := by
  have hl := l.isLt
  have hh := h.isLt
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, CEY.toNat_app, dword, Nat.shiftRight_eq_div_pow, Nat.reduceMul,
      Nat.reduceLT, Nat.reduceSub, ite_true, ite_false] <;> omega

/-- Doubleword `i` of `vpermd`'s result. -/
abbrev pdw (idx x : BitVec 256) (i : Nat) : BitVec 32 := x.extractLsb' (32 * (idx.extractLsb' (32 * i) 3).toNat) 32

theorem permDwords_eq (idx x : BitVec 256) :
    permDwords idx x = pdw idx x 7 ++ pdw idx x 6 ++ pdw idx x 5 ++ pdw idx x 4 ++ pdw idx x 3 ++ pdw idx x 2 ++
      pdw idx x 1 ++ pdw idx x 0 := rfl

theorem lo8 (a7 a6 a5 a4 a3 a2 a1 a0 : BitVec 32) :
    (a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0).extractLsb' 0 128 = ofDwords a0 a1 a2 a3 := by
  apply BitVec.eq_of_toNat_eq
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
  have := a4.isLt; have := a5.isLt; have := a6.isLt; have := a7.isLt
  simp only [BitVec.extractLsb'_toNat, CEY.toNat_app, CEY.toNat_ofDwords, Nat.shiftRight_zero]
  omega

theorem hi8 (a7 a6 a5 a4 a3 a2 a1 a0 : BitVec 32) :
    (a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0).extractLsb' 128 128 = ofDwords a4 a5 a6 a7 := by
  apply BitVec.eq_of_toNat_eq
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
  have := a4.isLt; have := a5.isLt; have := a6.isLt; have := a7.isLt
  simp only [BitVec.extractLsb'_toNat, CEY.toNat_app, CEY.toNat_ofDwords, Nat.shiftRight_eq_div_pow]
  omega

/-- The indices of `vpermd` (`ymm9`, `ymm10`). -/
def I9 : BitVec 256 := (0 : BitVec 64) ++ (0x0000000600000005 : BitVec 64) ++ (0x0000000400000002 : BitVec 64) ++
  (0x0000000100000000 : BitVec 64)
def I10 : BitVec 256 := (0x0000000100000000 : BitVec 64) ++ (0 : BitVec 64) ++ (0x0000000600000005 : BitVec 64) ++
  (0x0000000400000002 : BitVec 64)

theorem dword3_zero {A : BitVec 128} (h : A.toNat < 2 ^ 96) : (dword A 3).toNat = 0 := by
  rw [toNat_dword']; omega

/-- The 48 bytes of four lanes of 12 bytes each, as `vpermd`, `vpblendd` and
the two stores leave them. -/
theorem gather_val (A0 A1 B0 B1 : BitVec 128) (ha0 : A0.toNat < 2 ^ 96) (ha1 : A1.toNat < 2 ^ 96)
    (hb0 : B0.toNat < 2 ^ 96) (hb1 : B1.toNat < 2 ^ 96) :
    (blendDwords ((permDwords I9 (A1 ++ A0)).extractLsb' 128 128) ((permDwords I10 (B1 ++ B0)).extractLsb' 128 128)
        ((0xC0 : BitVec 8).extractLsb' 4 4) ++
      blendDwords ((permDwords I9 (A1 ++ A0)).extractLsb' 0 128) ((permDwords I10 (B1 ++ B0)).extractLsb' 0 128)
        ((0xC0 : BitVec 8).extractLsb' 0 4)).toNat +
      2 ^ 256 * ((permDwords I10 (B1 ++ B0)).extractLsb' 0 128).toNat =
    A0.toNat + 2 ^ 96 * A1.toNat + 2 ^ 192 * (B0.toNat + 2 ^ 96 * B1.toNat) := by
  rw [permDwords_eq, permDwords_eq, lo8, hi8, lo8, hi8]
  simp only [pdw, show ((I9).extractLsb' (32 * 0) 3).toNat = 0 by decide, show ((I9).extractLsb' (32 * 1) 3).toNat = 1 by decide, show ((I9).extractLsb' (32 * 2) 3).toNat = 2 by decide, show ((I9).extractLsb' (32 * 3) 3).toNat = 4 by decide, show ((I9).extractLsb' (32 * 4) 3).toNat = 5 by decide, show ((I9).extractLsb' (32 * 5) 3).toNat = 6 by decide, show ((I9).extractLsb' (32 * 6) 3).toNat = 0 by decide, show ((I9).extractLsb' (32 * 7) 3).toNat = 0 by decide, show ((I10).extractLsb' (32 * 0) 3).toNat = 2 by decide, show ((I10).extractLsb' (32 * 1) 3).toNat = 4 by decide, show ((I10).extractLsb' (32 * 2) 3).toNat = 5 by decide, show ((I10).extractLsb' (32 * 3) 3).toNat = 6 by decide, show ((I10).extractLsb' (32 * 4) 3).toNat = 0 by decide, show ((I10).extractLsb' (32 * 5) 3).toNat = 0 by decide, show ((I10).extractLsb' (32 * 6) 3).toNat = 0 by decide, show ((I10).extractLsb' (32 * 7) 3).toNat = 1 by decide]
  simp only [dword256 _ _ (show (0 : Nat) < 8 by decide), dword256 _ _ (show (1 : Nat) < 8 by decide),
    dword256 _ _ (show (2 : Nat) < 8 by decide), dword256 _ _ (show (4 : Nat) < 8 by decide),
    dword256 _ _ (show (5 : Nat) < 8 by decide), dword256 _ _ (show (6 : Nat) < 8 by decide),
    Nat.reduceLT, Nat.reduceSub, ite_true, ite_false]
  simp only [blendDwords, BitVec.reduceGetLsb, BitVec.reduceExtractLsb']
  simp only [Bool.false_eq_true, ite_true, ite_false]
  simp only [CEY.toNat_app, CEY.toNat_ofDwords, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3]
  have za0 := dword3_zero ha0
  have za1 := dword3_zero ha1
  have zb0 := dword3_zero hb0
  have zb1 := dword3_zero hb1
  rw [CEY.toNat_eq_dwords A0, CEY.toNat_eq_dwords A1, CEY.toNat_eq_dwords B0, CEY.toNat_eq_dwords B1]
  omega

/-! ## The stores -/

theorem div_lo {X Y : Nat} {j : Nat} (hj : j < 32) : (X + 2 ^ 256 * Y) / 2 ^ (8 * j) % 256 = X / 2 ^ (8 * j) % 256 := by
  rw [show 2 ^ 256 * Y = 2 ^ (8 * j) * (256 * (2 ^ (248 - 8 * j) * Y)) by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, show 256 = 2 ^ 8 from rfl, ← Nat.pow_add, ← Nat.pow_add,
      show 8 * j + 8 + (248 - 8 * j) = 256 by omega],
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left]

theorem div_hi {X Y : Nat} (hX : X < 2 ^ 256) {j : Nat} (hj : 32 ≤ j) :
    (X + 2 ^ 256 * Y) / 2 ^ (8 * j) = Y / 2 ^ (8 * (j - 32)) := by
  rw [show 8 * j = 256 + 8 * (j - 32) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hX, Nat.zero_add]

/-- The bytes of a 256-bit and a 128-bit store, together: those of `N`. -/
theorem store_bytes (m : Mem) (o : Addr) (X : BitVec 256) (Y : BitVec 128) {N : Nat}
    (hN : X.toNat + 2 ^ 256 * Y.toNat = N) :
    Written m ((m.writeW o X).writeW (o + BitVec.ofNat 64 32) Y) o 48 fun b => BitVec.ofNat 8 (N / 2 ^ (8 * b)) := by
  have h1 : Written m (m.writeW o X) o 32 fun j => (X.setWidth (8 * (256 / 8))).extractLsb' (8 * j) 8 := fun _ => rfl
  have h2 : Written (m.writeW o X) ((m.writeW o X).writeW (o + BitVec.ofNat 64 32) Y) (o + BitVec.ofNat 64 32) 16
      fun j => (Y.setWidth (8 * (128 / 8))).extractLsb' (8 * j) 8 := fun _ => rfl
  refine (Written.append h1 h2 (by decide)).congr fun j hj => ?_
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← hN]
  split
  · rw [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.mod_eq_of_lt X.isLt, Nat.shiftRight_eq_div_pow,
      div_lo ‹j < 32›]
  · rw [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.mod_eq_of_lt Y.isLt, Nat.shiftRight_eq_div_pow,
      div_hi X.isLt (by omega)]

/-! ## The specification, 32 coefficients at a time -/

theorem range32 : List.range 32 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31] := rfl

/-- Bytes `48i … 48i + 47` of `ByteEncode₁₂(f)`: those of the number of
coefficients `32i … 32i + 31`. -/
theorem encode12_group48 (f : Poly) {i b : Nat} (hi : i < 8) (hb : b < 48) :
    (Spec.MlKem.encode12 f)[48 * i + b]! =
      BitVec.ofNat 8 (digits 12 ((List.range 32).map fun j => (f[32 * i + j]!).val) / 2 ^ (8 * b)) := by
  rw [Spec.MlKem.encode12, byteEncode_group (d := 12) (c := 32) (b := 48) (by decide) (by decide)
    (map_toList_lt f val_lt_4096) hb (by omega), take_drop_eq _ 0 (by simp only [Vector.length_toList, n]; omega)]
  congr 3
  refine List.map_congr_left fun j hj => ?_
  rw [map_toList_getD f _ (by have := List.mem_range.mp hj; omega)]

/-- The number of 32 coefficients, by groups of eight. -/
theorem digits32 (g : Nat → Nat) :
    digits 12 ((List.range 32).map g) =
      (g 0 + 2 ^ 12 * g 1 + 2 ^ 24 * g 2 + 2 ^ 36 * g 3 + 2 ^ 48 * g 4 + 2 ^ 60 * g 5 + 2 ^ 72 * g 6 +
        2 ^ 84 * g 7) +
      2 ^ 96 * (g 8 + 2 ^ 12 * g 9 + 2 ^ 24 * g 10 + 2 ^ 36 * g 11 + 2 ^ 48 * g 12 + 2 ^ 60 * g 13 +
        2 ^ 72 * g 14 + 2 ^ 84 * g 15) +
      2 ^ 192 * ((g 16 + 2 ^ 12 * g 17 + 2 ^ 24 * g 18 + 2 ^ 36 * g 19 + 2 ^ 48 * g 20 + 2 ^ 60 * g 21 +
        2 ^ 72 * g 22 + 2 ^ 84 * g 23) +
      2 ^ 96 * (g 24 + 2 ^ 12 * g 25 + 2 ^ 24 * g 26 + 2 ^ 36 * g 27 + 2 ^ 48 * g 28 + 2 ^ 60 * g 29 +
        2 ^ 72 * g 30 + 2 ^ 84 * g 31)) := by
  rw [range32]
  simp only [List.map_cons, List.map_nil, digits_cons, digits_nil]
  omega

/-! ## Steps -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_vpermqD8 {d r : XReg}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then XBinOp.eval .punpcklqdq (s.lane r 0) (s.lane r 1)
      else XBinOp.eval .punpckhqdq (s.lane r 0) (s.lane r 1)) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpermq d r 0xD8) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d ((permQwords (s.ymm r) 0xD8).extractLsb' 0 128)
      ((permQwords (s.ymm r) 0xD8).extractLsb' 128 128)) rfl (k _ (by
    have h := LUpd.setV256 s d ((permQwords (s.ymm r) 0xD8).extractLsb' 0 128)
      ((permQwords (s.ymm r) 0xD8).extractLsb' 128 128)
    rw [State.ymm_eq, permD8_lo, permD8_hi] at h ⊢
    exact h))

theorem wp_vblend {d a b : XReg} {n : BitVec 8}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then blendDwords (s.lane a 0) (s.lane b 0) (n.extractLsb' 0 4)
      else blendDwords (s.lane a 1) (s.lane b 1) (n.extractLsb' 4 4)) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpblendd .l256 d a b n) :: is)) s Q :=
  WP.cons rfl (k _ (LUpd.setV256 s d _ _))

end

/-! ## Half of an iteration -/

/-- The number of eight coefficients of `F` from `b`. -/
abbrev V8 (F : Poly) (b : Nat) : Nat :=
  (F[b]!).val + 2 ^ 12 * (F[b + 1]!).val + 2 ^ 24 * (F[b + 2]!).val + 2 ^ 36 * (F[b + 3]!).val +
    2 ^ 48 * (F[b + 4]!).val + 2 ^ 60 * (F[b + 5]!).val + 2 ^ 72 * (F[b + 6]!).val + 2 ^ 84 * (F[b + 7]!).val

theorem lane_ld {m : Mem} {p : Addr} {l : Nat} (hl : l < 2) :
    (m.readW p 256).extractLsb' (128 * l) 128 = m.readW (p + BitVec.ofNat 64 (16 * l)) 128 := by
  rcases lane01 hl with rfl | rfl
  · exact readW_extract m p (k := 0) (n := 16) (by decide)
  · exact readW_extract m p (k := 16) (n := 16) (by decide)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `e12Half d t off`: each lane of `d` holds the number of eight coefficients. -/
theorem half_ok {d t : XReg} (hdt : t ≠ d) (hd8 : d ≠ .xmm8) (ht8 : t ≠ .xmm8) (off : Nat) {fP : Addr} {F : Poly}
    {j : Nat} (hj : j + 16 ≤ 256) (hF : PolyIs s.mem fP F)
    (ha : s.gpr .rdi + BitVec.ofNat 64 off = coeffAddr fP j)
    (ha' : s.gpr .rdi + BitVec.ofNat 64 (off + 32) = coeffAddr fP (j + 8))
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr fP j) 32) (hin' : InRegions (s.rd ++ s.wr) (coeffAddr fP (j + 8)) 32)
    (h8 : ∀ l < 2, s.lane .xmm8 l = shufM)
    (k : ∀ s', (∀ l < 2, (s'.lane d l).toNat = V8 F (j + 8 * l)) →
      (∀ r, r ≠ d → r ≠ t → ∀ l < 2, s'.lane r l = s.lane r l) → s'.gpr = s.gpr → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (e12Half d t off ++ is)) s Q := by
  simp only [e12Half, List.cons_append, List.nil_append]
  refine wp_vld256 (a := coeffAddr fP j) (by rw [ea_at, ha]) hin fun s1 u1 => ?_
  refine wp_vld256 (a := coeffAddr fP (j + 8)) (by rw [ea_at, u1.gpr, ha']) (by rw [u1.rd, u1.wr]; exact hin')
    fun s2 u2 => ?_
  refine wp_vbin fun s3 u3 => wp_vpermqD8 fun s4 u4 => wp_vsh fun s5 u5 => wp_vsh fun s6 u6 => wp_vsh fun s7 u7 =>
    wp_vsh fun s8 u8 => wp_vbin fun s9 u9 => wp_vbin fun s10 u10 => k s10 ?_ ?_ ?_ ?_ ?_ ?_
  · -- the words after packing
    have hc : ∀ k, k < 256 → (coeffAt s.mem fP k).toNat = (F[k]!).val := fun k hk =>
      polyIs_toNat hF (by rw [n_eq]; exact hk)
    have pk : ∀ l < 2, Lanes (s3.lane d l) (fun e => if e < 4 then F[j + 4 * l + e]! else F[j + 8 + 4 * l + (e - 4)]!) :=
      fun l hl => by
        rw [u3.val l hl]
        simp only [VBinOp.sse]
        rw [u2.other d (Ne.symm hdt) l hl, u1.val l hl, u2.val l hl, lane_ld hl, lane_ld hl, u1.mem,
          show 16 * l = 4 * (4 * l) by omega, coeffAddr_off, coeffAddr_off]
        exact lanes_pack2 hF (by omega) (by omega)
    have Y : ∀ l < 2, Lanes (s4.lane d l) (fun e => F[j + 8 * l + e]!) := fun l hl => by
      rw [u4.val l hl]
      rcases lane01 hl with rfl | rfl
      · rw [itT rfl]; intro e he; rw [word_punpcklqdq _ _ he]
        split
        · rw [pk 0 (by decide) e he]; dsimp only; rw [itT ‹e < 4›]
        · rw [pk 1 (by decide) (e - 4) (by omega)]; dsimp only
          rw [itT (show e - 4 < 4 by omega)]
          exact congrArg _ (congrArg _ (by omega))
      · rw [itF (by decide)]; intro e he; rw [word_punpckhqdq _ _ he]
        split
        · rw [pk 0 (by decide) (4 + e) (by omega)]; dsimp only
          rw [itF (show ¬ 4 + e < 4 by omega)]
          exact congrArg _ (congrArg _ (by omega))
        · rw [pk 1 (by decide) e he]; dsimp only
          rw [itF ‹¬ e < 4›]
          exact congrArg _ (congrArg _ (by omega))
    intro l hl
    have x9 : s9.lane .xmm8 l = shufM := by
      rw [u9.other _ (Ne.symm hd8) l hl, u8.other _ (Ne.symm hd8) l hl, u7.other _ (Ne.symm hd8) l hl,
        u6.other _ (Ne.symm ht8) l hl, u5.other _ (Ne.symm ht8) l hl, u4.other _ (Ne.symm hd8) l hl,
        u3.other _ (Ne.symm hd8) l hl, u2.other _ (Ne.symm ht8) l hl, u1.other _ (Ne.symm hd8) l hl, h8 l hl]
    have t8 : s8.lane t l = XShiftOp.eval .pslld (XShiftOp.eval .psrld (s4.lane d l) 16) 12 := by
      rw [u8.other _ hdt l hl, u7.other _ hdt l hl, u6.val l hl, u5.val l hl]
    have d8 : s8.lane d l = XShiftOp.eval .psrld (XShiftOp.eval .pslld (s4.lane d l) 16) 16 := by
      rw [u8.val l hl, u7.val l hl, u6.other _ (Ne.symm hdt) l hl, u5.other _ (Ne.symm hdt) l hl]
    have e10 : s10.lane d l = shufV (pairV (s4.lane d l)) := by
      rw [u10.val l hl, u9.val l hl, x9, d8, t8]
      simp only [VBinOp.sse]
    have Yv : ∀ e < 8, (word (s4.lane d l) e).toNat = (F[j + 8 * l + e]!).val := fun e he => Y l hl e he
    rw [e10, lane_val fun e he => by rw [Yv e he]; have := val_lt F[j + 8 * l + e]!; omega,
      Yv 0 (by decide), Yv 1 (by decide), Yv 2 (by decide), Yv 3 (by decide), Yv 4 (by decide), Yv 5 (by decide),
      Yv 6 (by decide), Yv 7 (by decide), Nat.add_zero]
  · intro r hrd hrt l hl
    rw [u10.other r hrd l hl, u9.other r hrd l hl, u8.other r hrd l hl, u7.other r hrd l hl, u6.other r hrt l hl,
      u5.other r hrt l hl, u4.other r hrd l hl, u3.other r hrd l hl, u2.other r hrt l hl, u1.other r hrd l hl]
  · rw [u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

end

/-! ## The constants -/

/-- The constants in `ymm8` to `ymm10`. -/
structure EC (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = shufM
  c9 : s.ymm .xmm9 = I9
  c10 : s.ymm .xmm10 = I10

theorem EC.keep {s s' : State} (h : EC s) (hk : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 →
    ∀ l < 2, s'.lane r l = s.lane r l) : EC s' :=
  ⟨fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) l hl]; exact h.c8 l hl,
    by rw [State.ymm_eq, hk _ (by decide) (by decide) (by decide) (by decide) 0 (by decide),
      hk _ (by decide) (by decide) (by decide) (by decide) 1 (by decide), ← State.ymm_eq]; exact h.c9,
    by rw [State.ymm_eq, hk _ (by decide) (by decide) (by decide) (by decide) 0 (by decide),
      hk _ (by decide) (by decide) (by decide) (by decide) 1 (by decide), ← State.ymm_eq]; exact h.c10⟩

theorem consts_ok {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', EC s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) :
    WP isa (.block (e12Consts ++ is)) s Q := by
  simp only [e12Consts, List.append_assoc]
  refine yconst4_ok (by decide) (by decide) _ _ _ _ fun s1 a1 b1 o1 g1 m1 r1 w1 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s2 a2 b2 o2 g2 m2 r2 w2 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s3 a3 b3 o3 g3 m3 r3 w3 =>
    k s3 ⟨fun l hl => ?_, ?_, ?_⟩ (fun g hg => by rw [g3 g hg, g2 g hg, g1 g hg]) (by rw [m3, m2, m1])
      (by rw [r3, r2, r1]) (by rw [w3, w2, w1])
  · rw [o3 _ (by decide) (by decide) (by decide) l hl, o2 _ (by decide) (by decide) (by decide) l hl]
    rcases lane01 hl with rfl | rfl
    · rw [a1]; decide
    · rw [b1]; decide
  · rw [State.ymm_eq, o3 _ (by decide) (by decide) (by decide) 0 (by decide),
      o3 _ (by decide) (by decide) (by decide) 1 (by decide), a2, b2]; decide
  · rw [State.ymm_eq, a3, b3]; decide

/-! ## The loop -/

section
variable (s₀ : State)
abbrev fP : Addr := s₀.gpr .rdi
abbrev oP : Addr := s₀.gpr .rsi
abbrev FF : Poly := polyAt s₀.mem (fP s₀)
end

/-- After `i` iterations. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = coeffAddr (fP s₀) (32 * i)
  rsi : s.gpr .rsi = oP s₀ + BitVec.ofNat 64 (48 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ec : EC s
  frame : Frame [⟨oP s₀, 384⟩] s₀.mem s.mem
  done : ∀ k < 48 * i, s.mem (oP s₀ + BitVec.ofNat 64 k) = (Spec.MlKem.encode12 (FF s₀))[k]!

section
variable {s₀ : State} (hp : encode12K.pre s₀)
include hp

theorem polyIs₀ : PolyIs s₀.mem (fP s₀) (FF s₀) :=
  polyIs_of_toNat fun _ hi => (polyAt_val hp.2.2.2.2.2 hi).symm

theorem step {i : Nat} (hi : i < 8) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block (e12Body ++ e12Step)) s fun s' => Inv s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hrw : s.rd ++ s.wr = [pR (fP s₀), ⟨oP s₀, 384⟩] := by rw [hI.rd, hI.wr, hp.1, hp.2.1]; rfl
  have hF : PolyIs s.mem (fP s₀) (FF s₀) := polyIs_frame hI.frame (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hp.2.2.1) (polyIs₀ hp)
  have hin : ∀ j, j + 8 ≤ 256 → InRegions (s.rd ++ s.wr) (coeffAddr (fP s₀) j) 32 := fun j hj => by
    rw [hrw]; exact ⟨_, by simp, Offset.contains_base _ (show 4 * j + 32 ≤ 1024 by omega) (by omega)⟩
  rw [e12Body, List.append_assoc, List.append_assoc]
  refine half_ok (d := .xmm0) (t := .xmm1) (by decide) (by decide) (by decide) 0 (j := 32 * i) (by omega) hF
    (by rw [hI.rdi, add_ofNat_zero]) (by rw [hI.rdi, show 0 + 32 = 4 * 8 from rfl, coeffAddr_off])
    (hin _ (by omega)) (hin _ (by omega)) hI.ec.c8 fun s1 hA o1 g1 m1 r1 w1 => ?_
  refine half_ok (d := .xmm2) (t := .xmm3) (by decide) (by decide) (by decide) 64 (j := 32 * i + 16) (by omega)
    (by rw [m1]; exact hF)
    (by rw [g1, hI.rdi, show BitVec.ofNat 64 64 = BitVec.ofNat 64 (4 * 16) from rfl, coeffAddr_off])
    (by rw [g1, hI.rdi, show BitVec.ofNat 64 (64 + 32) = BitVec.ofNat 64 (4 * 24) from rfl, coeffAddr_off,
      show 32 * i + 24 = 32 * i + 16 + 8 by omega])
    (by rw [r1, w1]; exact hin _ (by omega))
    (by
      rw [r1, w1]
      exact hin _ (by omega))
    (fun l hl => by rw [o1 _ (by decide) (by decide) l hl]; exact hI.ec.c8 l hl) fun s2 hB o2 g2 m2 r2 w2 => ?_
  have ec2 : EC s2 := hI.ec.keep fun r h0 h1 h2 h3 l hl => by rw [o2 r h2 h3 l hl, o1 r h0 h1 l hl]
  -- the lanes of the two halves
  have eA : ∀ l < 2, s2.lane .xmm0 l = s1.lane .xmm0 l := fun l hl => o2 _ (by decide) (by decide) l hl
  generalize hA0 : s1.lane .xmm0 0 = A0 at hA eA
  generalize hA1 : s1.lane .xmm0 1 = A1 at hA eA
  generalize hB0 : s2.lane .xmm2 0 = B0 at hB
  generalize hB1 : s2.lane .xmm2 1 = B1 at hB
  have a0 := hA 0 (by decide)
  have a1 := hA 1 (by decide)
  have b0 := hB 0 (by decide)
  have b1 := hB 1 (by decide)
  rw [hA0] at a0
  rw [hA1] at a1
  rw [hB0] at b0
  rw [hB1] at b1
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at a0 a1 b0 b1
  have hv : ∀ b, (V8 (FF s₀) b) < 2 ^ 96 := fun b => by
    have := val_lt (FF s₀)[b]!; have := val_lt (FF s₀)[b + 1]!; have := val_lt (FF s₀)[b + 2]!
    have := val_lt (FF s₀)[b + 3]!; have := val_lt (FF s₀)[b + 4]!; have := val_lt (FF s₀)[b + 5]!
    have := val_lt (FF s₀)[b + 6]!; have := val_lt (FF s₀)[b + 7]!
    simp only [V8]; omega
  have y0 : s2.ymm .xmm0 = A1 ++ A0 := by rw [State.ymm_eq, eA 0 (by decide), eA 1 (by decide), hA0, hA1]
  have y2 : s2.ymm .xmm2 = B1 ++ B0 := by rw [State.ymm_eq, hB0, hB1]
  simp only [List.cons_append, List.nil_append]
  refine wp_vpermd fun s3 u3 => wp_vpermd fun s4 u4 => wp_vblend fun s5 u5 => ?_
  have hw : s5.wr = [⟨oP s₀, 384⟩] := by rw [u5.wr, u4.wr, u3.wr, w2, w1, hI.wr, hp.2.1]
  have g5 : s5.gpr = s.gpr := by rw [u5.gpr, u4.gpr, u3.gpr, g2, g1]
  have m5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, m2, m1]
  -- the two values stored
  have y3 : s3.ymm .xmm10 = I10 := by
    rw [State.ymm_eq, u3.other _ (by decide) 0 (by decide), u3.other _ (by decide) 1 (by decide), ← State.ymm_eq]
    exact ec2.c10
  have x3 : s3.ymm .xmm2 = B1 ++ B0 := by
    rw [State.ymm_eq, u3.other _ (by decide) 0 (by decide), u3.other _ (by decide) 1 (by decide), ← State.ymm_eq]
    exact y2
  have hX : s5.ymm .xmm0 =
      blendDwords ((permDwords I9 (A1 ++ A0)).extractLsb' 128 128) ((permDwords I10 (B1 ++ B0)).extractLsb' 128 128)
        ((0xC0 : BitVec 8).extractLsb' 4 4) ++
      blendDwords ((permDwords I9 (A1 ++ A0)).extractLsb' 0 128) ((permDwords I10 (B1 ++ B0)).extractLsb' 0 128)
        ((0xC0 : BitVec 8).extractLsb' 0 4) := by
    rw [State.ymm_eq, u5.val 0 (by decide), u5.val 1 (by decide), itT rfl, itF (by decide),
      u4.other _ (by decide) 0 (by decide), u4.other _ (by decide) 1 (by decide), u4.val 0 (by decide),
      u4.val 1 (by decide), u3.val 0 (by decide), u3.val 1 (by decide), y3, x3, ec2.c9, y0]
  have hY : s5.lane .xmm2 0 = (permDwords I10 (B1 ++ B0)).extractLsb' 0 128 := by
    rw [u5.other _ (by decide) 0 (by decide), u4.val 0 (by decide), y3, x3]
  have hN := gather_val A0 A1 B0 B1 (by rw [a0]; exact hv _) (by rw [a1]; exact hv _) (by rw [b0]; exact hv _)
    (by rw [b1]; exact hv _)
  rw [← hX, ← hY] at hN
  refine wp_vst256 (a := oP s₀ + BitVec.ofNat 64 (48 * i)) (by rw [ea_at, add_ofNat_zero, g5, hI.rsi])
    (by rw [hw]; exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (show 48 * i + 32 ≤ 384 by omega)
      (by omega)⟩) fun s6 g6 l6 m6 r6 w6 => ?_
  refine CEY.wp_vst128 (a := oP s₀ + BitVec.ofNat 64 (48 * i) + BitVec.ofNat 64 32)
    (by rw [ea_at, g6, g5, hI.rsi])
    (by rw [w6, hw, Offset.add_add]; exact ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (show 48 * i + 32 + 16 ≤ 384 by omega) (by omega)⟩) fun s7 g7 l7 m7 r7 w7 => ?_
  simp only [e12Step]
  refine wp_addi' fun s8 u8 => wp_addi' fun s9 u9 => wp_subi' fun s10 u10 hz => WP.block_nil ?_
  have m10 : s10.mem = (s.mem.writeW (oP s₀ + BitVec.ofNat 64 (48 * i)) (s5.ymm .xmm0)).writeW
      (oP s₀ + BitVec.ofNat 64 (48 * i) + BitVec.ofNat 64 32) (s5.lane .xmm2 0) := by
    rw [u10.mem, u9.mem, u8.mem, m7, m6, l6, m5]
  have g9 : ∀ r, s9.gpr r = s.gpr r ∨ r = .rdi ∨ r = .rsi := fun r => by
    by_cases h1 : r = .rdi
    · exact .inr (.inl h1)
    by_cases h2 : r = .rsi
    · exact .inr (.inr h2)
    exact .inl (by rw [u9.other r h2, u8.other r h1, g7, g6, g5])
  have rcx9 : s9.gpr .rcx = s.gpr .rcx := by rw [u9.other _ (by decide), u8.other _ (by decide), g7, g6, g5]
  -- the 48 bytes
  have hW := store_bytes s.mem (oP s₀ + BitVec.ofNat 64 (48 * i)) _ _ hN
  rw [← m10] at hW
  have hW' : Written s.mem s10.mem (oP s₀ + BitVec.ofNat 64 (48 * i)) 48
      fun j => (Spec.MlKem.encode12 (FF s₀))[48 * i + j]! := hW.congr fun j hj => by
    rw [encode12_group48 _ hi hj, a0, a1, b0, b1]
    refine congrArg (fun x => BitVec.ofNat 8 (x / 2 ^ (8 * j))) (Eq.trans ?_ (digits32 _).symm)
    simp only [V8, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]
  obtain ⟨hf', hd'⟩ := Written.step hI.frame hI.done hW' (by omega) (by decide)
  refine ⟨⟨?_, ?_, by rw [u10.rd, u9.rd, u8.rd, r7, r6, u5.rd, u4.rd, u3.rd, r2, r1, hI.rd],
    by rw [u10.wr, u9.wr, u8.wr, w7, w6, hw, hp.2.1], ?_, hf', fun k hk => hd' k (by omega)⟩, ?_, ?_⟩
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.gpr, g7, g6, g5, hI.rdi,
      show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 (4 * 32) by decide, coeffAddr_off,
      show 32 * i + 32 = 32 * (i + 1) by omega]
  · rw [u10.other _ (by decide), u9.gpr, u8.other _ (by decide), g7, g6, g5, hI.rsi,
      show BitVec.signExtend 64 (48 : BitVec 32) = BitVec.ofNat 64 48 by decide, Offset.add_add,
      show 48 * i + 48 = 48 * (i + 1) by omega]
  · refine ec2.keep fun r h0 h1 h2 h3 l hl => ?_
    rw [u10.lane, u9.lane, u8.lane, l7, l6, u5.other r h0 l hl, u4.other r h2 l hl, u3.other r h0 l hl]
  · rw [u10.gpr, rcx9]; rfl
  · rw [hz, rcx9]; rfl

theorem main : WP isa encode12Avx2 s₀ fun s => Frame [⟨oP s₀, 384⟩] s₀.mem s.mem ∧
    ∀ k < 384, s.mem (oP s₀ + BitVec.ofNat 64 k) = (Spec.MlKem.encode12 (FF s₀))[k]! := by
  unfold encode12Avx2
  refine WP.seq (consts_ok fun s1 hc1 hg1 hm1 hr1 hw1 => wp_mov32i fun s2 u2 => WP.block_nil ?_)
  refine WP.seq (wp_countdown (cnt := .rcx) (N := 8) (by decide) (by decide) (Inv s₀)
    (fun i hi s hI _ => step hp hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1], by rw [u2.wr, hw1],
      hc1.keep fun r _ _ _ _ l _ => by rw [u2.lane], by rw [u2.mem, hm1]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega)⟩
    (by rw [u2.gpr]; rfl))
  · exact wp_vzu fun s3 _ hm3 _ _ => WP.block_nil ⟨by rw [hm3]; exact hI.frame,
      fun k hk => by rw [hm3]; exact hI.done k (by omega)⟩
  · rw [u2.other _ (by decide), hg1 _ (by decide)]; simp [coeffAddr]
  · rw [u2.other _ (by decide), hg1 _ (by decide)]; simp

theorem correct : ∃ t s', Exec isa encode12Avx2 s₀ t s' ∧ abiPreserved s₀ s' ∧ encode12K.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hf, hd⟩, hk⟩ := WP.keep (c := encode12Avx2) [.rax, .rdi, .rsi, .rcx] (main hp)
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hp.2.2.2.2.1)), bytesAt_eq! (encode12_length _) hd⟩

end

end VG.Proof.MlKem.X86_64.E12Y

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

theorem encode12Y_correct (s : State) (hs : encode12K.pre s) :
    ∃ t s', Exec isa encode12Avx2 s t s' ∧ abiPreserved s s' ∧ encode12K.post s s' :=
  E12Y.correct hs

theorem encode12Y_ct : ConstantTime isa encode12K.pre encode12K.pub encode12Avx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

end VG.Proof.MlKem.X86_64
