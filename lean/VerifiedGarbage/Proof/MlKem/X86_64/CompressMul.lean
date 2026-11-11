module

public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncodeAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.Encode12Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncodeAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.Encode12Avx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# ML-KEM on x86-64: `ByteEncode_d ∘ Compress_d` with multiplications, in an MXCSR region

`cm10` and `cm4` (`Impl/MlKem/X86_64/CompressAvx2.lean`) meet the contract of
`vg_mlkem_compress_encode` for one width each.

* A word: what `cmHi` and `cmLo` make of a word less than `q` is its
  compression (`hiW`, `loW`), checked for each of the `q` words by the kernel
  (`word_formula`), as `Proof/MlKem/Compress.lean` checks its formulas.
* A lane: after `vpmaddwd`, each doubleword holds a pair of compressed
  coefficients (`dword_hiL`, `dword_loL`).
* A group of sixteen coefficients: the words `cmLd` loads (`ld_ok`), and the
  number its bytes are, the one whose base-`2ᵈ` digits are the compressed
  coefficients (`compressEncode_group`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.CMY

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Proof.MlKem (allBelow allBelow_spec)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.Sha3.X86_64 (WP.cons)
open S4 (LUpd wp_vbin wp_vvar wp_vld256 GUpd wp_addi' itT itF)
open D12Y (wp_vsh wp_subi' wp_vzu wp_mov32i yconst4_ok yconst_ok' wp_vbin128)
open CEY
open E12Y (wp_vpermqD8)

/-! ## A word -/

/-- The word `cmHi` makes of the word `x`, before `pmaddwd`: with `off`,
`2^(d + 2)` (`sh`) and `2ᵈ - 1` (`mk`). -/
def hiW (off sh mk x : BitVec 16) : BitVec 16 :=
  let f1 := (mulWordsSigned x 0x75F8).extractLsb' 0 16
  mulhrs ((mulWordsSigned (x <<< 3) 0x4EBF).extractLsb' 16 16 - ((~~~f1 &&& (f1 - (x + off))) >>> 15)) sh &&& mk

/-- The word `cmLo` makes of the word `x`, before `pmaddwd`. -/
def loW (sh mk x : BitVec 16) : BitVec 16 := mulhrs ((mulWordsSigned x 0x4EBF).extractLsb' 16 16) sh &&& mk

/-- A function of words that is `Compress_d` on every word less than `q`,
from the kernel's check of each. -/
theorem word_formula {f : BitVec 16 → BitVec 16} {d : Nat}
    (h : allBelow 3329 (fun x => Nat.beq (f (BitVec.ofNat 16 x)).toNat (roundDiv (2 ^ d * x) 3329 % 2 ^ d)) = true)
    {x : BitVec 16} {z : Zq} (hx : x.toNat = z.val) : (f x).toNat = compress d z := by
  have := Nat.eq_of_beq_eq_true (allBelow_spec h z.val z.isLt)
  rw [← hx, BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  rw [this, hx]; rfl

theorem hiW10 {x : BitVec 16} {z : Zq} (hx : x.toNat = z.val) : (hiW 15 0x1000 0x3FF x).toNat = compress 10 z :=
  word_formula (by decide +kernel) hx

theorem loW4 {x : BitVec 16} {z : Zq} (hx : x.toNat = z.val) : (loW 0x200 0xF x).toNat = compress 4 z :=
  word_formula (by decide +kernel) hx

/-! ## A lane -/

variable {a b : BitVec 128} {i : Nat}

theorem word_pandn (hi : i < 8) : word (XBinOp.eval .pandn a b) i = ~~~word a i &&& word b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [XBinOp.eval, word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_not, hj,
    decide_true, Bool.true_and, show 16 * i + j < 128 by omega_arith]

theorem word_psllw {n : BitVec 8} (hn : n.toNat ≤ 15) (hi : i < 8) :
    word (XShiftOp.eval .psllw a n) i = word a i <<< n.toNat := by
  simp only [XShiftOp.eval, ite_eq_right (show ¬ 15 < n.toNat by omega_arith)]; exact word_ofWords _ hi

theorem word_psrlw {n : BitVec 8} (hn : n.toNat ≤ 15) (hi : i < 8) :
    word (XShiftOp.eval .psrlw a n) i = word a i >>> n.toNat := by
  simp only [XShiftOp.eval, ite_eq_right (show ¬ 15 < n.toNat by omega_arith)]; exact word_ofWords _ hi

theorem word_pmulhrsw (hi : i < 8) : word (XBinOp.eval .pmulhrsw a b) i = mulhrs (word a i) (word b i) := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi

theorem dword_pmaddwd (a b : BitVec 128) (hi : i < 4) :
    dword (XBinOp.eval .pmaddwd a b) i = mulWordsSigned (word a (2 * i)) (word b (2 * i)) +
      mulWordsSigned (word a (2 * i + 1)) (word b (2 * i + 1)) := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> simp [XBinOp.eval]

/-- The product of two words that are not negative. -/
theorem mulWordsSigned_small {x y : BitVec 16} (hx : x.toNat < 2 ^ 15) (hy : y.toNat < 2 ^ 15) :
    (mulWordsSigned x y).toNat = x.toNat * y.toNat := by
  have ex : x.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by omega_arith)
  have ey : y.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by omega_arith)
  have e1 : (x.setWidth 32).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega_arith)
  have e2 : (y.setWidth 32).toNat = y.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega_arith)
  rw [mulWordsSigned, BitVec.signExtend_eq_setWidth_of_msb_false ex, BitVec.signExtend_eq_setWidth_of_msb_false ey,
    BitVec.toNat_mul, e1, e2]
  have := Nat.mul_lt_mul'' hx hy
  exact Nat.mod_eq_of_lt (by omega_arith)

/-- A pair of values less than `2ᵈ` in a doubleword: `vpmaddwd` by the words `1, 2ᵈ`. -/
theorem dword_pair {A K : BitVec 128} {d : Nat} (hd : d ≤ 11)
    (hK : ∀ i < 4, word K (2 * i) = 1 ∧ word K (2 * i + 1) = BitVec.ofNat 16 (2 ^ d))
    {c : Nat → Nat} (hc : ∀ j < 8, (word A j).toNat = c j) (hlt : ∀ j < 8, c j < 2 ^ d) (hi : i < 4) :
    (dword (XBinOp.eval .pmaddwd A K) i).toNat = c (2 * i) + 2 ^ d * c (2 * i + 1) := by
  have hp : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd
  have h0 := hlt (2 * i) (by omega_arith)
  have h1 := hlt (2 * i + 1) (by omega_arith)
  have e2 : (BitVec.ofNat 16 (2 ^ d)).toNat = 2 ^ d := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  rw [dword_pmaddwd _ _ hi, (hK i hi).1, (hK i hi).2, BitVec.toNat_add,
    mulWordsSigned_small (by rw [hc _ (by omega_arith)]; omega_arith) (by decide),
    mulWordsSigned_small (by rw [hc _ (by omega_arith)]; omega_arith) (by rw [e2]; omega_arith), e2,
    hc _ (by omega_arith), hc _ (by omega_arith)]
  have hm : c (2 * i + 1) * 2 ^ d < 2 ^ 22 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos d))
      (show 2 ^ d * 2 ^ d ≤ 2 ^ 11 * 2 ^ 11 from Nat.mul_le_mul hp hp)
  rw [show (1 : BitVec 16).toNat = 1 from rfl, Nat.mul_one, Nat.mul_comm (2 ^ d)]
  generalize c (2 * i + 1) * 2 ^ d = m at hm ⊢
  exact Nat.mod_eq_of_lt (by omega_arith)

/-- A lane of `cmHi`, with the constants `K8, …, K13`. -/
abbrev hiL (X K8 K9 K10 K11 K12 K13 : BitVec 128) : BitVec 128 :=
  let f1 := XBinOp.eval .pmullw X K8
  XBinOp.eval .pmaddwd (XBinOp.eval .pand (XBinOp.eval .pmulhrsw
    (XBinOp.eval .psubw (XBinOp.eval .pmulhw (XShiftOp.eval .psllw X 3) K10)
      (XShiftOp.eval .psrlw (XBinOp.eval .pandn f1 (XBinOp.eval .psubw f1 (XBinOp.eval .paddw X K9))) 15))
    K11) K12) K13

/-- A lane of `cmLo`, with the constants `K10, …, K13`. -/
abbrev loL (X K10 K11 K12 K13 : BitVec 128) : BitVec 128 :=
  XBinOp.eval .pmaddwd (XBinOp.eval .pand (XBinOp.eval .pmulhrsw (XBinOp.eval .pmulhw X K10) K11) K12) K13

/-- The doublewords of `hiL`: the pairs of the values `hiW` makes of the words of `X`. -/
theorem dword_hiL {X K8 K9 K10 K11 K12 K13 : BitVec 128} {off sh mk : BitVec 16} {d : Nat} (hd : d ≤ 11)
    (h8 : ∀ i < 8, word K8 i = 0x75F8) (h9 : ∀ i < 8, word K9 i = off) (h10 : ∀ i < 8, word K10 i = 0x4EBF)
    (h11 : ∀ i < 8, word K11 i = sh) (h12 : ∀ i < 8, word K12 i = mk)
    (h13 : ∀ i < 4, word K13 (2 * i) = 1 ∧ word K13 (2 * i + 1) = BitVec.ofNat 16 (2 ^ d))
    {c : Nat → Nat} (hc : ∀ j < 8, (hiW off sh mk (word X j)).toNat = c j) (hlt : ∀ j < 8, c j < 2 ^ d)
    (hi : i < 4) : (dword (hiL X K8 K9 K10 K11 K12 K13) i).toNat = c (2 * i) + 2 ^ d * c (2 * i + 1) := by
  refine dword_pair hd h13 (fun j hj => ?_) hlt hi
  rw [← hc j hj, word_pand, word_pmulhrsw hj, word_psubw _ _ hj, word_pmulhw _ _ hj, word_psllw (n := 3) (by decide) hj,
    word_psrlw (n := 15) (by decide) hj,
    word_pandn hj, word_psubw _ _ hj, word_paddw _ _ hj, word_pmullw _ _ hj, h8 j hj, h9 j hj, h10 j hj, h11 j hj, h12 j hj]
  rfl

/-- The doublewords of `loL`: the pairs of the values `loW` makes of the words of `X`. -/
theorem dword_loL {X K10 K11 K12 K13 : BitVec 128} {sh mk : BitVec 16} {d : Nat} (hd : d ≤ 11)
    (h10 : ∀ i < 8, word K10 i = 0x4EBF) (h11 : ∀ i < 8, word K11 i = sh) (h12 : ∀ i < 8, word K12 i = mk)
    (h13 : ∀ i < 4, word K13 (2 * i) = 1 ∧ word K13 (2 * i + 1) = BitVec.ofNat 16 (2 ^ d))
    {c : Nat → Nat} (hc : ∀ j < 8, (loW sh mk (word X j)).toNat = c j) (hlt : ∀ j < 8, c j < 2 ^ d)
    (hi : i < 4) : (dword (loL X K10 K11 K12 K13) i).toNat = c (2 * i) + 2 ^ d * c (2 * i + 1) := by
  refine dword_pair hd h13 (fun j hj => ?_) hlt hi
  rw [← hc j hj, word_pand, word_pmulhrsw hj, word_pmulhw _ _ hj, h10 j hj, h11 j hj, h12 j hj]
  rfl

/-! ## The number a lane holds -/

theorem toNat_byte_hi (x : BitVec 128) {i : Nat} (hi : i < 8) :
    (byte x (8 + i)).toNat = (qword x 1).toNat / 2 ^ (8 * i) % 2 ^ 8 := by
  rw [toNat_byte, toNat_qword]
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] <;>
    omega_arith

theorem toNat_qwords (x : BitVec 128) : x.toNat = (qword x 0).toNat + 2 ^ 64 * (qword x 1).toNat := by
  have := x.isLt
  simp only [toNat_qword, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one] at this ⊢; omega_arith

theorem toNat_word (x : BitVec 128) (j : Nat) : (word x j).toNat = x.toNat / 2 ^ (16 * j) % 2 ^ 16 := by
  rw [word, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem toNat_ofWords (f : Nat → BitVec 16) : (ofWords f).toNat =
    (f 0).toNat + 2 ^ 16 * (f 1).toNat + 2 ^ 32 * (f 2).toNat + 2 ^ 48 * (f 3).toNat + 2 ^ 64 * (f 4).toNat +
    2 ^ 80 * (f 5).toNat + 2 ^ 96 * (f 6).toNat + 2 ^ 112 * (f 7).toNat := by
  simp only [ofWords, toNat_app]; omega_arith

/-- `vpblendw` with `0xE0`: the low ten bytes of `a`, the high six of `b`. -/
theorem toNat_blendE0 (a b : BitVec 128) :
    (blendWords a b 0xE0).toNat = a.toNat % 2 ^ 80 + 2 ^ 80 * (b.toNat / 2 ^ 80) := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [blendWords, toNat_ofWords, show (0xE0 : BitVec 8).getLsbD 0 = false from rfl,
    show (0xE0 : BitVec 8).getLsbD 1 = false from rfl, show (0xE0 : BitVec 8).getLsbD 2 = false from rfl,
    show (0xE0 : BitVec 8).getLsbD 3 = false from rfl, show (0xE0 : BitVec 8).getLsbD 4 = false from rfl,
    show (0xE0 : BitVec 8).getLsbD 5 = true from rfl, show (0xE0 : BitVec 8).getLsbD 6 = true from rfl,
    show (0xE0 : BitVec 8).getLsbD 7 = true from rfl, ↓reduceIte, Bool.false_eq_true, toNat_word, Nat.reduceMul,
    Nat.reducePow, Nat.pow_zero, Nat.div_one] at ha hb ⊢
  omega_arith

/-! ## Packing ten bits -/

/-- The constants of `cmPack10`: the shifts of `vpsllvd`, and the masks of `vpshufb`. -/
def s12 : BitVec 128 := (12 : BitVec 64) ++ (12 : BitVec 64)
def m10a : BitVec 128 := (0x8080808080800c0b : BitVec 64) ++ (0x0a09080403020100 : BitVec 64)
def m10b : BitVec 128 := (0x0804030201008080 : BitVec 64) ++ (0x808080800c0b0a09 : BitVec 64)

/-- A lane of pairs after `vpsllvd` and `vpsrlq`. -/
abbrev q10 (D : BitVec 128) : BitVec 128 := XShiftOp.eval .psrlq (VVarOp.eval .vpsllvd D s12) 12

/-- The quadwords of `q10`: each holds two pairs, forty bits. -/
theorem qword_q10 {D : BitVec 128} {p : Nat → Nat} (hp : ∀ i < 4, (dword D i).toNat = p i)
    (hlt : ∀ i < 4, p i < 2 ^ 20) :
    (qword (q10 D) 0).toNat = p 0 + 2 ^ 20 * p 1 ∧ (qword (q10 D) 1).toNat = p 2 + 2 ^ 20 * p 3 := by
  have b0 := hlt 0 (by decide); have b1 := hlt 1 (by decide); have b2 := hlt 2 (by decide)
  have b3 := hlt 3 (by decide)
  have h0 : (dword (VVarOp.eval .vpsllvd D s12) 0).toNat = p 0 * 2 ^ 12 := by
    rw [dword_sllv _ _ (by decide), show (dword s12 0).toNat = 12 from rfl, itT (by decide), BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, hp 0 (by decide)]
    exact Nat.mod_eq_of_lt (by omega_arith)
  have h1 : (dword (VVarOp.eval .vpsllvd D s12) 1).toNat = p 1 := by
    rw [dword_sllv _ _ (by decide), show (dword s12 1).toNat = 0 from rfl, itT (by decide), BitVec.shiftLeft_zero,
      hp 1 (by decide)]
  have h2 : (dword (VVarOp.eval .vpsllvd D s12) 2).toNat = p 2 * 2 ^ 12 := by
    rw [dword_sllv _ _ (by decide), show (dword s12 2).toNat = 12 from rfl, itT (by decide), BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, hp 2 (by decide)]
    exact Nat.mod_eq_of_lt (by omega_arith)
  have h3 : (dword (VVarOp.eval .vpsllvd D s12) 3).toNat = p 3 := by
    rw [dword_sllv _ _ (by decide), show (dword s12 3).toNat = 0 from rfl, itT (by decide), BitVec.shiftLeft_zero,
      hp 3 (by decide)]
  dsimp only [q10]
  generalize VVarOp.eval .vpsllvd D s12 = A at h0 h1 h2 h3
  simp only [XShiftOp.eval, show (12 : BitVec 8).toNat = 12 from rfl, show ¬ 63 < 12 by decide, ↓reduceIte,
    qword_app0, qword_app1, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, toNat_qword0, toNat_qword1, h0, h1,
    h2, h3]
  constructor <;> omega_arith

/-- The bytes `vpshufb` gathers from the first lane: its ten bytes, in order. -/
theorem toNat_m10a {Q : BitVec 128} {a₀ a₁ : Nat} (h₀ : (qword Q 0).toNat = a₀) (h₁ : (qword Q 1).toNat = a₁)
    (l₀ : a₀ < 2 ^ 40) (l₁ : a₁ < 2 ^ 40) : (XBinOp.eval .pshufb Q m10a).toNat = a₀ + 2 ^ 40 * a₁ := by
  have e : XBinOp.eval .pshufb Q m10a =
      ofBytes fun i => if i < 5 then byte Q i else if i < 10 then byte Q (8 + (i - 5)) else 0 := by
    simp only [XBinOp.eval, ofBytes]; rfl
  rw [e, toNat_ofBytes]
  simp only [Nat.reduceLT, ↓reduceIte, Nat.reduceSub, toNat_byte_lo _ (show (0 : Nat) < 8 by decide),
    toNat_byte_lo _ (show (1 : Nat) < 8 by decide), toNat_byte_lo _ (show (2 : Nat) < 8 by decide),
    toNat_byte_lo _ (show (3 : Nat) < 8 by decide), toNat_byte_lo _ (show (4 : Nat) < 8 by decide),
    toNat_byte_hi _ (show (0 : Nat) < 8 by decide), toNat_byte_hi _ (show (1 : Nat) < 8 by decide),
    toNat_byte_hi _ (show (2 : Nat) < 8 by decide), toNat_byte_hi _ (show (3 : Nat) < 8 by decide),
    toNat_byte_hi _ (show (4 : Nat) < 8 by decide), h₀, h₁, show (0 : BitVec 8).toNat = 0 from rfl, Nat.reduceMul,
    Nat.reducePow, Nat.pow_zero, Nat.div_one]
  omega_arith

/-- The bytes `vpshufb` gathers from the second lane: its last four, then
(from byte 10) its first six. -/
theorem toNat_m10b {Q : BitVec 128} {b₀ b₁ : Nat} (h₀ : (qword Q 0).toNat = b₀) (h₁ : (qword Q 1).toNat = b₁)
    (l₀ : b₀ < 2 ^ 40) (l₁ : b₁ < 2 ^ 40) :
    (XBinOp.eval .pshufb Q m10b).toNat = (b₀ + 2 ^ 40 * b₁) / 2 ^ 48 + 2 ^ 80 * ((b₀ + 2 ^ 40 * b₁) % 2 ^ 48) := by
  have e : XBinOp.eval .pshufb Q m10b = ofBytes fun i =>
      if i < 4 then byte Q (8 + (1 + i)) else if i < 10 then 0 else if i < 15 then byte Q (i - 10) else byte Q (8 + 0) := by
    simp only [XBinOp.eval, ofBytes]; rfl
  rw [e, toNat_ofBytes]
  simp only [Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd, toNat_byte_lo _ (show (0 : Nat) < 8 by decide),
    toNat_byte_lo _ (show (1 : Nat) < 8 by decide), toNat_byte_lo _ (show (2 : Nat) < 8 by decide),
    toNat_byte_lo _ (show (3 : Nat) < 8 by decide), toNat_byte_lo _ (show (4 : Nat) < 8 by decide),
    toNat_byte_hi _ (show (0 : Nat) < 8 by decide), show byte Q 9 = byte Q (8 + 1) from rfl,
    show byte Q 10 = byte Q (8 + 2) from rfl, show byte Q 11 = byte Q (8 + 3) from rfl,
    show byte Q 12 = byte Q (8 + 4) from rfl, toNat_byte_hi _ (show (1 : Nat) < 8 by decide),
    toNat_byte_hi _ (show (2 : Nat) < 8 by decide), toNat_byte_hi _ (show (3 : Nat) < 8 by decide),
    toNat_byte_hi _ (show (4 : Nat) < 8 by decide), h₀, h₁, show (0 : BitVec 8).toNat = 0 from rfl, Nat.reduceMul,
    Nat.reducePow, Nat.pow_zero, Nat.div_one]
  omega_arith

/-- `cmPack10` on the two lanes `D₀`, `D₁` of pairs `p`, `p'`: the sixteen
bytes it stores first are the low ones of the number `V` whose twenty bytes
are the group's, and the doubleword it stores next the others. -/
theorem pack10 {D₀ D₁ : BitVec 128} {p p' : Nat → Nat} (hp : ∀ i < 4, (dword D₀ i).toNat = p i)
    (hp' : ∀ i < 4, (dword D₁ i).toNat = p' i) (hlt : ∀ i < 4, p i < 2 ^ 20) (hlt' : ∀ i < 4, p' i < 2 ^ 20)
    {V : Nat} (hV : V = p 0 + 2 ^ 20 * p 1 + 2 ^ 40 * (p 2 + 2 ^ 20 * p 3) +
      2 ^ 80 * (p' 0 + 2 ^ 20 * p' 1 + 2 ^ 40 * (p' 2 + 2 ^ 20 * p' 3))) :
    blendWords (XBinOp.eval .pshufb (q10 D₀) m10a) (XBinOp.eval .pshufb (q10 D₁) m10b) 0xE0 = BitVec.ofNat 128 V ∧
      dword (XBinOp.eval .pshufb (q10 D₁) m10b) 0 = BitVec.ofNat 32 (V / 2 ^ 128) := by
  obtain ⟨a0, a1⟩ := qword_q10 hp hlt
  obtain ⟨b0, b1⟩ := qword_q10 hp' hlt'
  have c0 := hlt 0 (by decide); have c1 := hlt 1 (by decide); have c2 := hlt 2 (by decide)
  have c3 := hlt 3 (by decide); have d0 := hlt' 0 (by decide); have d1 := hlt' 1 (by decide)
  have d2 := hlt' 2 (by decide); have d3 := hlt' 3 (by decide)
  have eA := toNat_m10a a0 a1 (by omega_arith) (by omega_arith)
  have eB := toNat_m10b b0 b1 (by omega_arith) (by omega_arith)
  have hA : p 0 + 2 ^ 20 * p 1 + 2 ^ 40 * (p 2 + 2 ^ 20 * p 3) < 2 ^ 80 := by omega_arith
  have hN : p' 0 + 2 ^ 20 * p' 1 + 2 ^ 40 * (p' 2 + 2 ^ 20 * p' 3) < 2 ^ 80 := by omega_arith
  generalize XBinOp.eval .pshufb (q10 D₀) m10a = E₀ at eA
  generalize XBinOp.eval .pshufb (q10 D₁) m10b = E₁ at eB
  generalize p 0 + 2 ^ 20 * p 1 + 2 ^ 40 * (p 2 + 2 ^ 20 * p 3) = A at hV eA hA
  generalize p' 0 + 2 ^ 20 * p' 1 + 2 ^ 40 * (p' 2 + 2 ^ 20 * p' 3) = N at hV eB hN
  have e1 : (N / 2 ^ 48 + 2 ^ 80 * (N % 2 ^ 48)) / 2 ^ 80 = N % 2 ^ 48 := by
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 80), Nat.div_eq_of_lt (by omega_arith), Nat.zero_add]
  have e2 : (A + 2 ^ 80 * N) % 2 ^ 128 = A + 2 ^ 80 * (N % 2 ^ 48) := by omega_arith
  have e3 : (A + 2 ^ 80 * N) / 2 ^ 128 = N / 2 ^ 48 := by omega_arith
  have e4 : (N / 2 ^ 48 + 2 ^ 80 * (N % 2 ^ 48)) % 2 ^ 32 = N / 2 ^ 48 := by omega_arith
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [toNat_blendE0, eA, eB, BitVec.toNat_ofNat, hV, e1, e2, Nat.mod_eq_of_lt hA]
  · apply BitVec.eq_of_toNat_eq
    rw [toNat_dword', eB, BitVec.toNat_ofNat, hV, e3, Nat.mul_zero, Nat.pow_zero, Nat.div_one, e4]
    exact (Nat.mod_eq_of_lt (by omega_arith)).symm

/-! ## Packing four bits -/

/-- The masks of `cmPack4`. -/
def m4a : BitVec 128 := (0x8080808080808080 : BitVec 64) ++ (0x808080800c080400 : BitVec 64)
def m4b : BitVec 128 := (0x8080808080808080 : BitVec 64) ++ (0x0c08040080808080 : BitVec 64)

theorem toNat_byte4 (x : BitVec 128) {i : Nat} (hi : i < 4) : (byte x (4 * i)).toNat = (dword x i).toNat % 2 ^ 8 := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    simp only [toNat_byte, toNat_dword', Nat.reduceMul, Nat.reducePow] <;> omega_arith

/-- `cmPack4` on the two lanes `D₀`, `D₁` of pairs `p`, `p'`: the quadword it stores. -/
theorem pack4 {D₀ D₁ : BitVec 128} {p p' : Nat → Nat} (hp : ∀ i < 4, (dword D₀ i).toNat = p i)
    (hp' : ∀ i < 4, (dword D₁ i).toNat = p' i) (hlt : ∀ i < 4, p i < 2 ^ 8) (hlt' : ∀ i < 4, p' i < 2 ^ 8) :
    (XBinOp.eval .por (XBinOp.eval .pshufb D₀ m4a) (XBinOp.eval .pshufb D₁ m4b)).extractLsb' 0 64 =
      BitVec.ofNat 64 (p 0 + 2 ^ 8 * p 1 + 2 ^ 16 * p 2 + 2 ^ 24 * p 3 +
        2 ^ 32 * (p' 0 + 2 ^ 8 * p' 1 + 2 ^ 16 * p' 2 + 2 ^ 24 * p' 3)) := by
  have ea : XBinOp.eval .pshufb D₀ m4a = ofBytes fun i => if i < 4 then byte D₀ (4 * i) else 0 := by
    simp only [XBinOp.eval, ofBytes]; rfl
  have eb : XBinOp.eval .pshufb D₁ m4b =
      ofBytes fun i => if i < 4 then 0 else if i < 8 then byte D₁ (4 * (i - 4)) else 0 := by
    simp only [XBinOp.eval, ofBytes]; rfl
  have c0 := hlt 0 (by decide); have c1 := hlt 1 (by decide); have c2 := hlt 2 (by decide)
  have c3 := hlt 3 (by decide); have d0 := hlt' 0 (by decide); have d1 := hlt' 1 (by decide)
  have d2 := hlt' 2 (by decide); have d3 := hlt' 3 (by decide)
  have e : XBinOp.eval .por (XBinOp.eval .pshufb D₀ m4a) (XBinOp.eval .pshufb D₁ m4b) =
      BitVec.ofNat 128 (p 0 + 2 ^ 8 * p 1 + 2 ^ 16 * p 2 + 2 ^ 24 * p 3 +
        2 ^ 32 * (p' 0 + 2 ^ 8 * p' 1 + 2 ^ 16 * p' 2 + 2 ^ 24 * p' 3)) := by
    rw [ea, eb]
    refine ext_byte fun t ht => ?_
    simp only [XBinOp.eval, byte_or, byte_ofBytes _ ht, toNat_byte (BitVec.ofNat 128 _), BitVec.toNat_ofNat]
    rcases (by omega_arith : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
      t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceLT, ↓reduceIte, Nat.reduceSub, BitVec.toNat_or, Nat.or_zero, Nat.zero_or,
      show (4 * 0 : Nat) = 4 * 0 from rfl, toNat_byte4 _ (show (0 : Nat) < 4 by decide),
      toNat_byte4 _ (show (1 : Nat) < 4 by decide), toNat_byte4 _ (show (2 : Nat) < 4 by decide),
      toNat_byte4 _ (show (3 : Nat) < 4 by decide), hp 0 (by decide), hp 1 (by decide), hp 2 (by decide),
      hp 3 (by decide), hp' 0 (by decide), hp' 1 (by decide), hp' 2 (by decide), hp' 3 (by decide),
      show (0 : BitVec 8).toNat = 0 from rfl, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one] <;>
    omega_arith
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega_arith

/-! ## Steps -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movr {d r : Reg} (k : ∀ s', GUpd s s' d (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.setReg _ _ _))

theorem wp_vblendw128 {d a b : XReg} {n : BitVec 8}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then blendWords (s.lane a 0) (s.lane b 0) n else 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpblendw .l128 d a b n) :: is)) s Q :=
  WP.cons rfl (k _ (LUpd.setV128 s d _ (blendWords (s.lane a 1) (s.lane b 1) n)))

theorem wp_store64 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.lane x l = s.lane x l) → s'.mem = s.mem.writeW a (s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl)
  simp [exec, State.store64, ha, hout]

/-- `cmLd`: the sixteen coefficients `x` at `rdi + o`, the words of `ymm0`, in order. -/
theorem ld_ok {o : Nat} (hin0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 o) 32)
    (hin1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (o + 32)) 32) {x : Nat → Nat}
    (hx : ∀ j < 16, (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (o + 4 * j)) 32).toNat = x j)
    (hq : ∀ j < 16, x j < 3329)
    (k : ∀ s', (∀ l < 2, ∀ j < 8, (word (s'.lane .xmm0 l) j).toNat = x (8 * l + j)) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (cmLd o ++ is)) s Q := by
  simp only [cmLd, yb, List.cons_append, List.nil_append]
  refine wp_vld256 (a := s.gpr .rdi + BitVec.ofNat 64 o) (by rw [ea_at]) hin0 fun s1 u1 => ?_
  refine wp_vld256 (a := s.gpr .rdi + BitVec.ofNat 64 (o + 32)) (by rw [ea_at, u1.gpr])
    (by rw [u1.rd, u1.wr]; exact hin1) fun s2 u2 => ?_
  refine wp_vbin fun s3 u3 => wp_vpermqD8 fun s4 u4 => k s4 (fun l hl j hj => ?_) (fun r a b l hl => ?_) ?_ ?_ ?_ ?_
  · have eA : ∀ l < 2, ∀ i < 4, (dword ((s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 o) 256).extractLsb' (128 * l) 128)
        i).toNat = x (4 * l + i) := fun l hl i hi => by
      rw [dword_ld _ _ hl hi, Offset.add_add, show o + (16 * l + 4 * i) = o + 4 * (4 * l + i) by omega_arith,
        hx _ (by omega_arith)]
    have eB : ∀ l < 2, ∀ i < 4, (dword ((s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (o + 32)) 256).extractLsb'
        (128 * l) 128) i).toNat = x (8 + 4 * l + i) := fun l hl i hi => by
      rw [dword_ld _ _ hl hi, Offset.add_add, show o + 32 + (16 * l + 4 * i) = o + 4 * (8 + 4 * l + i) by omega_arith,
        hx _ (by omega_arith)]
    have eP : ∀ l < 2, ∀ e < 8, (word (s3.lane .xmm0 l) e).toNat =
        if e < 4 then x (4 * l + e) else x (8 + 4 * l + (e - 4)) := fun l hl e he => by
      rw [u3.val l hl, u2.other .xmm0 (by decide) l hl, u1.val l hl, u2.val l hl, u1.mem]
      show (word (XBinOp.eval .packssdw _ _) e).toNat = _
      rw [word_packssdw_small _ _ he
        (fun i hi => by rw [eA l hl i hi]; have := hq (4 * l + i) (by omega_arith); omega_arith)
        (fun i hi => by rw [eB l hl i hi]; have := hq (8 + 4 * l + i) (by omega_arith); omega_arith)]
      split
      · rw [eA l hl e (by omega_arith)]
      · rw [eB l hl (e - 4) (by omega_arith)]
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    · rw [u4.val 0 (by decide), itT rfl, word_punpcklqdq _ _ hj]
      split
      · rename_i h; rw [eP 0 (by decide) j hj, itT h]
      · rename_i h; rw [eP 1 (by decide) (j - 4) (by omega_arith), itT (by omega_arith)]
        exact congrArg x (by omega_arith)
    · rw [u4.val 1 (by decide), itF (by decide), word_punpckhqdq _ _ hj]
      split
      · rw [eP 0 (by decide) (4 + j) (by omega_arith), itF (by omega_arith)]
        exact congrArg x (by omega_arith)
      · rename_i h; rw [eP 1 (by decide) j hj, itF h]
        exact congrArg x (by omega_arith)
  · rw [u4.other r a l hl, u3.other r a l hl, u2.other r b l hl, u1.other r a l hl]
  · rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u4.wr, u3.wr, u2.wr, u1.wr]

theorem toY_cmHi : toY cmHi =
    [yb .vpmullw .xmm1 .xmm0 .xmm8, yb .vpaddw .xmm2 .xmm0 .xmm9, .vop (.vshift .psllw .l256 .xmm0 .xmm0 3),
      yb .vpmulhw .xmm0 .xmm0 .xmm10, yb .vpsubw .xmm3 .xmm1 .xmm2, yb .vpandn .xmm1 .xmm1 .xmm3,
      .vop (.vshift .psrlw .l256 .xmm1 .xmm1 15), yb .vpsubw .xmm0 .xmm0 .xmm1, yb .vpmulhrsw .xmm0 .xmm0 .xmm11,
      yb .vpand .xmm0 .xmm0 .xmm12, yb .vpmaddwd .xmm0 .xmm0 .xmm13] := by decide +kernel

theorem toY_cmLo : toY cmLo =
    [yb .vpmulhw .xmm0 .xmm0 .xmm10, yb .vpmulhrsw .xmm0 .xmm0 .xmm11, yb .vpand .xmm0 .xmm0 .xmm12,
      yb .vpmaddwd .xmm0 .xmm0 .xmm13] := by decide +kernel

/-- `cmHi`: each lane of `ymm0` is `hiL` of it. -/
theorem hi_ok
    (k : ∀ s', (∀ l < 2, s'.lane .xmm0 l = hiL (s.lane .xmm0 l) (s.lane .xmm8 l) (s.lane .xmm9 l) (s.lane .xmm10 l)
        (s.lane .xmm11 l) (s.lane .xmm12 l) (s.lane .xmm13 l)) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (toY cmHi ++ is)) s Q := by
  rw [toY_cmHi]
  simp only [yb, List.cons_append, List.nil_append]
  refine wp_vbin fun s1 u1 => wp_vbin fun s2 u2 => wp_vsh fun s3 u3 => wp_vbin fun s4 u4 => wp_vbin fun s5 u5 =>
    wp_vbin fun s6 u6 => wp_vsh fun s7 u7 => wp_vbin fun s8 u8 => wp_vbin fun s9 u9 => wp_vbin fun s10 u10 =>
    wp_vbin fun s11 u11 => k s11 (fun l hl => ?_) (fun r a b c d l hl => ?_) ?_ ?_ ?_ ?_
  · simp only [laneEq u11 hl, laneEq u10 hl, laneEq u9 hl, laneEq u8 hl, laneEq u7 hl, laneEq u6 hl, laneEq u5 hl,
      laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, reduceCtorEq, ↓reduceIte]
    rfl
  · simp only [laneEq u11 hl, laneEq u10 hl, laneEq u9 hl, laneEq u8 hl, laneEq u7 hl, laneEq u6 hl, laneEq u5 hl,
      laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, a, b, c, d, ↓reduceIte]
  · rw [u11.gpr, u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

/-- `cmLo`: each lane of `ymm0` is `loL` of it. -/
theorem lo_ok
    (k : ∀ s', (∀ l < 2, s'.lane .xmm0 l = loL (s.lane .xmm0 l) (s.lane .xmm10 l) (s.lane .xmm11 l)
        (s.lane .xmm12 l) (s.lane .xmm13 l)) →
      (∀ r, r ≠ .xmm0 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (toY cmLo ++ is)) s Q := by
  rw [toY_cmLo]
  simp only [yb, List.cons_append, List.nil_append]
  refine wp_vbin fun s1 u1 => wp_vbin fun s2 u2 => wp_vbin fun s3 u3 => wp_vbin fun s4 u4 =>
    k s4 (fun l hl => ?_) (fun r a l hl => ?_) ?_ ?_ ?_ ?_
  · simp only [laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, reduceCtorEq, ↓reduceIte]
    rfl
  · simp only [laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, a, ↓reduceIte]
  · rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u4.wr, u3.wr, u2.wr, u1.wr]

end

/-! ## The constants -/

/-- A constant of `yconst`: the doubleword `v`, four times. -/
abbrev wc (v : BitVec 32) : BitVec 128 := ofDwords v v v v

/-- The constants of `cm10`. -/
structure C10 (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = wc 0x75F875F8
  c9 : ∀ l < 2, s.lane .xmm9 l = wc 0x000F000F
  c10 : ∀ l < 2, s.lane .xmm10 l = wc 0x4EBF4EBF
  c11 : ∀ l < 2, s.lane .xmm11 l = wc 0x10001000
  c12 : ∀ l < 2, s.lane .xmm12 l = wc 0x03FF03FF
  c13 : ∀ l < 2, s.lane .xmm13 l = wc 0x04000001
  c14 : ∀ l < 2, s.lane .xmm14 l = s12
  c7 : ∀ l < 2, s.lane .xmm7 l = if l = 0 then m10a else m10b

theorem C10.pres {s s' : State} (h : C10 s) (hk : Hi7 s s') : C10 s' :=
  ⟨fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c8 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c9 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c10 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c11 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c12 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c13 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c14 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c7 l hl]⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem consts10_ok
    (k : ∀ s', C10 s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (cm10Consts ++ is)) s Q := by
  simp only [cm10Consts, List.append_assoc]
  refine yconst_ok' _ _ fun s1 a1 o1 g1 m1 r1 w1 => yconst_ok' _ _ fun s2 a2 o2 g2 m2 r2 w2 =>
    yconst_ok' _ _ fun s3 a3 o3 g3 m3 r3 w3 => yconst_ok' _ _ fun s4 a4 o4 g4 m4 r4 w4 =>
    yconst_ok' _ _ fun s5 a5 o5 g5 m5 r5 w5 => yconst_ok' _ _ fun s6 a6 o6 g6 m6 r6 w6 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s7 a7 b7 o7 g7 m7 r7 w7 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s8 a8 b8 o8 g8 m8 r8 w8 =>
    k s8 ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_,
      fun l hl => ?_, fun l hl => ?_⟩ (fun g hg => ?_) ?_ ?_ ?_
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) l hl, o3 _ (by decide) l hl,
      o2 _ (by decide) l hl, a1 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) l hl, o3 _ (by decide) l hl, a2 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) l hl, a3 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) l hl, o5 _ (by decide) l hl, a4 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) l hl, a5 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl, a6 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl]
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    exacts [a7, b7]
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    · rw [itT rfl]; exact a8
    · rw [itF (by decide)]; exact b8
  · rw [g8 g hg, g7 g hg, g6 g hg, g5 g hg, g4 g hg, g3 g hg, g2 g hg, g1 g hg]
  · rw [m8, m7, m6, m5, m4, m3, m2, m1]
  · rw [r8, r7, r6, r5, r4, r3, r2, r1]
  · rw [w8, w7, w6, w5, w4, w3, w2, w1]

/-! ## A group of ten bits -/

theorem dig16_10 (c : Nat → Nat) : digits 10 ((List.range 16).map c) =
    c 0 + 2 ^ 10 * c 1 + 2 ^ 20 * (c 2 + 2 ^ 10 * c 3) +
        2 ^ 40 * (c 4 + 2 ^ 10 * c 5 + 2 ^ 20 * (c 6 + 2 ^ 10 * c 7)) +
      2 ^ 80 * (c 8 + 2 ^ 10 * c 9 + 2 ^ 20 * (c 10 + 2 ^ 10 * c 11) +
        2 ^ 40 * (c 12 + 2 ^ 10 * c 13 + 2 ^ 20 * (c 14 + 2 ^ 10 * c 15))) := by
  show digits 10 [c 0, c 1, c 2, c 3, c 4, c 5, c 6, c 7, c 8, c 9, c 10, c 11, c 12, c 13, c 14, c 15] = _
  simp only [digits_cons, digits_nil, Nat.reducePow]
  omega_arith

/-- A group of `d = 10`: the sixteen coefficients `z` at `rdi`, compressed,
and the twenty bytes of the number whose digits they are stored at `r8`. -/
theorem grp10_ok (hc : C10 s) (hin0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 0) 32)
    (hin1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (0 + 32)) 32) {z : Nat → Zq}
    (hx : ∀ j < 16, (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (0 + 4 * j)) 32).toNat = (z j).val)
    (hw16 : InRegions s.wr (s.gpr .r8) 16) (hw4 : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 16) 4)
    (k : ∀ s', s'.mem = (s.mem.writeW (s.gpr .r8)
          (BitVec.ofNat 128 (digits 10 ((List.range 16).map fun j => compress 10 (z j))))).writeW
        (s.gpr .r8 + BitVec.ofNat 64 16)
          (BitVec.ofNat 32 (digits 10 ((List.range 16).map fun j => compress 10 (z j)) / 2 ^ 128)) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (cmLd 0 ++ (toY cmHi ++ (cmPack10 ++ is)))) s Q := by
  refine ld_ok hin0 hin1 hx (fun j _ => val_lt _) fun s1 h1 o1 g1 m1 r1 w1 => ?_
  refine hi_ok fun s2 h2 o2 g2 m2 r2 w2 => ?_
  simp only [cmPack10, yb, List.cons_append, List.nil_append]
  refine wp_vvar fun s3 u3 => wp_vsh fun s4 u4 => wp_vbin fun s5 u5 => wp_vext1 fun s6 u6 =>
    wp_vblendw128 fun s7 u7 => ?_
  have cK : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s2.lane r l = s.lane r l :=
    fun r a b c d l hl => by rw [o2 r a b c d l hl, o1 r a b l hl]
  have D : ∀ l < 2, ∀ i < 4, (dword (s2.lane .xmm0 l) i).toNat =
      compress 10 (z (8 * l + 2 * i)) + 2 ^ 10 * compress 10 (z (8 * l + (2 * i + 1))) := fun l hl i hi => by
    rw [h2 l hl, o1 .xmm8 (by decide) (by decide) l hl, o1 .xmm9 (by decide) (by decide) l hl,
      o1 .xmm10 (by decide) (by decide) l hl, o1 .xmm11 (by decide) (by decide) l hl,
      o1 .xmm12 (by decide) (by decide) l hl, o1 .xmm13 (by decide) (by decide) l hl, hc.c8 l hl, hc.c9 l hl,
      hc.c10 l hl, hc.c11 l hl, hc.c12 l hl, hc.c13 l hl]
    exact dword_hiL (d := 10) (off := 15) (sh := 0x1000) (mk := 0x3FF) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (c := fun j => compress 10 (z (8 * l + j)))
      (fun j hj => hiW10 (h1 l hl j hj)) (fun j _ => compress_lt _ _) hi
  have E : ∀ l < 2, s5.lane .xmm0 l =
      XBinOp.eval .pshufb (q10 (s2.lane .xmm0 l)) (if l = 0 then m10a else m10b) := fun l hl => by
    rw [u5.val l hl, u4.val l hl, u3.val l hl, u4.other .xmm7 (by decide) l hl, u3.other .xmm7 (by decide) l hl,
      cK .xmm7 (by decide) (by decide) (by decide) (by decide) l hl, hc.c7 l hl,
      cK .xmm14 (by decide) (by decide) (by decide) (by decide) l hl, hc.c14 l hl]
    rfl
  have lt : ∀ l < 2, ∀ i < 4, compress 10 (z (8 * l + 2 * i)) + 2 ^ 10 * compress 10 (z (8 * l + (2 * i + 1))) <
      2 ^ 20 := fun l _ i _ => by
    have := compress_lt 10 (z (8 * l + 2 * i)); have := compress_lt 10 (z (8 * l + (2 * i + 1))); omega_arith
  obtain ⟨hR, hT⟩ := pack10 (D 0 (by decide)) (D 1 (by decide)) (lt 0 (by decide)) (lt 1 (by decide))
    (V := digits 10 ((List.range 16).map fun j => compress 10 (z j))) (by rw [dig16_10])
  have g7 : s7.gpr = s.gpr := by rw [u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, g2, g1]
  have m7 : s7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, m2, m1]
  have w7 : s7.wr = s.wr := by rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, w2, w1]
  have r7 : s7.rd = s.rd := by rw [u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, r2, r1]
  have x0 : s7.lane .xmm0 0 = BitVec.ofNat 128 (digits 10 ((List.range 16).map fun j => compress 10 (z j))) := by
    rw [u7.val 0 (by decide), itT rfl, u6.other .xmm0 (by decide) 0 (by decide), u6.val 0 (by decide), itT rfl,
      E 0 (by decide), E 1 (by decide), itT rfl, itF (by decide)]
    exact hR
  have x1 : s7.lane .xmm1 0 = XBinOp.eval .pshufb (q10 (s2.lane .xmm0 1)) m10b := by
    rw [u7.other .xmm1 (by decide) 0 (by decide), u6.val 0 (by decide), itT rfl, E 1 (by decide), itF (by decide)]
  refine wp_vst128 (a := s.gpr .r8) (by rw [ea_at, add_ofNat_zero, g7]) (by rw [w7]; exact hw16)
    fun s8 g8 l8 m8 r8 w8 => wp_movqR fun s9 u9 => ?_
  refine wp_store32 (a := s.gpr .r8 + BitVec.ofNat 64 16) (by rw [ea_at, u9.other _ (by decide), g8, g7])
    (by rw [u9.wr, w8, w7]; exact hw4) fun s10 g10 l10 m10 r10 w10 => k s10 ?_ (fun r a b c d l hl => ?_)
      (fun g hg => ?_) ?_ ?_
  · rw [m10, u9.mem, m8, m7, x0, u9.gpr, show s8.xmm .xmm1 = s8.lane .xmm1 0 from rfl, l8, x1, setWidth_ext64, hT]
  · rw [l10, u9.lane, l8, u7.other r a l hl, u6.other r b l hl, u5.other r a l hl, u4.other r a l hl,
      u3.other r a l hl, cK r a b c d l hl]
  · rw [g10, u9.other g hg, g8, g7]
  · rw [r10, u9.rd, r8, r7]
  · rw [w10, u9.wr, w8, w7]

/-! ## A group of four bits -/

/-- The constants of `cm4`. -/
structure C4 (s : State) : Prop where
  c10 : ∀ l < 2, s.lane .xmm10 l = wc 0x4EBF4EBF
  c11 : ∀ l < 2, s.lane .xmm11 l = wc 0x02000200
  c12 : ∀ l < 2, s.lane .xmm12 l = wc 0x000F000F
  c13 : ∀ l < 2, s.lane .xmm13 l = wc 0x00100001
  c7 : ∀ l < 2, s.lane .xmm7 l = if l = 0 then m4a else m4b

theorem C4.pres {s s' : State} (h : C4 s) (hk : Hi7 s s') : C4 s' :=
  ⟨fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c10 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c11 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c12 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c13 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c7 l hl]⟩

theorem consts4_ok
    (k : ∀ s', C4 s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (cm4Consts ++ is)) s Q := by
  simp only [cm4Consts, List.append_assoc]
  refine yconst_ok' _ _ fun s1 a1 o1 g1 m1 r1 w1 => yconst_ok' _ _ fun s2 a2 o2 g2 m2 r2 w2 =>
    yconst_ok' _ _ fun s3 a3 o3 g3 m3 r3 w3 => yconst_ok' _ _ fun s4 a4 o4 g4 m4 r4 w4 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s5 a5 b5 o5 g5 m5 r5 w5 =>
    k s5 ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩ (fun g hg => ?_) ?_ ?_ ?_
  · rw [o5 _ (by decide) (by decide) (by decide) l hl, o4 _ (by decide) l hl, o3 _ (by decide) l hl,
      o2 _ (by decide) l hl, a1 l hl]
  · rw [o5 _ (by decide) (by decide) (by decide) l hl, o4 _ (by decide) l hl, o3 _ (by decide) l hl, a2 l hl]
  · rw [o5 _ (by decide) (by decide) (by decide) l hl, o4 _ (by decide) l hl, a3 l hl]
  · rw [o5 _ (by decide) (by decide) (by decide) l hl, a4 l hl]
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    · rw [itT rfl]; exact a5
    · rw [itF (by decide)]; exact b5
  · rw [g5 g hg, g4 g hg, g3 g hg, g2 g hg, g1 g hg]
  · rw [m5, m4, m3, m2, m1]
  · rw [r5, r4, r3, r2, r1]
  · rw [w5, w4, w3, w2, w1]

theorem dig16_4 (c : Nat → Nat) : digits 4 ((List.range 16).map c) =
    c 0 + 2 ^ 4 * c 1 + 2 ^ 8 * (c 2 + 2 ^ 4 * c 3) + 2 ^ 16 * (c 4 + 2 ^ 4 * c 5) + 2 ^ 24 * (c 6 + 2 ^ 4 * c 7) +
      2 ^ 32 * (c 8 + 2 ^ 4 * c 9 + 2 ^ 8 * (c 10 + 2 ^ 4 * c 11) + 2 ^ 16 * (c 12 + 2 ^ 4 * c 13) +
        2 ^ 24 * (c 14 + 2 ^ 4 * c 15)) := by
  show digits 4 [c 0, c 1, c 2, c 3, c 4, c 5, c 6, c 7, c 8, c 9, c 10, c 11, c 12, c 13, c 14, c 15] = _
  simp only [digits_cons, digits_nil, Nat.reducePow]
  omega_arith

/-- A group of `d = 4`: the sixteen coefficients `z` at `rdi`, compressed,
and the eight bytes of the number whose digits they are stored at `r8`. -/
theorem grp4_ok (hc : C4 s) (hin0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 0) 32)
    (hin1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (0 + 32)) 32) {z : Nat → Zq}
    (hx : ∀ j < 16, (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (0 + 4 * j)) 32).toNat = (z j).val)
    (hw8 : InRegions s.wr (s.gpr .r8) 8)
    (k : ∀ s', s'.mem = s.mem.writeW (s.gpr .r8)
          (BitVec.ofNat 64 (digits 4 ((List.range 16).map fun j => compress 4 (z j)))) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → ∀ l < 2, s'.lane r l = s.lane r l) →
      (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (cmLd 0 ++ (toY cmLo ++ (cmPack4 ++ is)))) s Q := by
  refine ld_ok hin0 hin1 hx (fun j _ => val_lt _) fun s1 h1 o1 g1 m1 r1 w1 => ?_
  refine lo_ok fun s2 h2 o2 g2 m2 r2 w2 => ?_
  simp only [cmPack4, yb, List.cons_append, List.nil_append]
  refine wp_vbin fun s3 u3 => wp_vext1 fun s4 u4 => wp_vbin128 fun s5 u5 => wp_movqR fun s6 u6 => ?_
  have cK : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → ∀ l < 2, s2.lane r l = s.lane r l :=
    fun r a b l hl => by rw [o2 r a l hl, o1 r a b l hl]
  have D : ∀ l < 2, ∀ i < 4, (dword (s2.lane .xmm0 l) i).toNat =
      compress 4 (z (8 * l + 2 * i)) + 2 ^ 4 * compress 4 (z (8 * l + (2 * i + 1))) := fun l hl i hi => by
    rw [h2 l hl, o1 .xmm10 (by decide) (by decide) l hl, o1 .xmm11 (by decide) (by decide) l hl,
      o1 .xmm12 (by decide) (by decide) l hl, o1 .xmm13 (by decide) (by decide) l hl, hc.c10 l hl, hc.c11 l hl,
      hc.c12 l hl, hc.c13 l hl]
    exact dword_loL (d := 4) (sh := 0x200) (mk := 0xF) (by decide) (by decide) (by decide) (by decide) (by decide)
      (c := fun j => compress 4 (z (8 * l + j))) (fun j hj => loW4 (h1 l hl j hj)) (fun j _ => compress_lt _ _) hi
  have lt : ∀ l < 2, ∀ i < 4, compress 4 (z (8 * l + 2 * i)) + 2 ^ 4 * compress 4 (z (8 * l + (2 * i + 1))) <
      2 ^ 8 := fun l _ i _ => by
    have := compress_lt 4 (z (8 * l + 2 * i)); have := compress_lt 4 (z (8 * l + (2 * i + 1))); omega_arith
  have hR := pack4 (D 0 (by decide)) (D 1 (by decide)) (lt 0 (by decide)) (lt 1 (by decide))
  have g5 : s5.gpr = s.gpr := by rw [u5.gpr, u4.gpr, u3.gpr, g2, g1]
  have x0 : (s6.gpr .rax) = BitVec.ofNat 64 (digits 4 ((List.range 16).map fun j => compress 4 (z j))) := by
    rw [u6.gpr, show s5.xmm .xmm0 = s5.lane .xmm0 0 from rfl, u5.val 0 (by decide), itT rfl,
      u4.other .xmm0 (by decide) 0 (by decide), u4.val 0 (by decide), itT rfl, u3.val 0 (by decide),
      u3.val 1 (by decide), cK .xmm7 (by decide) (by decide) 0 (by decide),
      cK .xmm7 (by decide) (by decide) 1 (by decide), hc.c7 0 (by decide), hc.c7 1 (by decide), itT rfl,
      itF (by decide), dig16_4]
    exact hR
  refine wp_store64 (a := s.gpr .r8) (by rw [ea_at, add_ofNat_zero, u6.other _ (by decide), g5])
    (by rw [u6.wr, u5.wr, u4.wr, u3.wr, w2, w1]; exact hw8) fun s7 g7 l7 m7 r7 w7 =>
      k s7 ?_ (fun r a b l hl => ?_) (fun g hg => ?_) ?_ ?_
  · rw [m7, u6.mem, u5.mem, u4.mem, u3.mem, m2, m1, x0]
  · rw [l7, u6.lane, u5.other r a l hl, u4.other r b l hl, u3.other r a l hl, cK r a b l hl]
  · rw [g7, u6.other g hg, g5]
  · rw [r7, u6.rd, u5.rd, u4.rd, u3.rd, r2, r1]
  · rw [w7, u6.wr, u5.wr, u4.wr, u3.wr, w2, w1]

end

/-! ## The loops -/

/-- After `i` groups, of `st` bytes of coefficients and `b` bytes each, with the constants `C`. -/
structure Inv (C : State → Prop) (st d b : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = CE.fP s₀ + BitVec.ofNat 64 (st * i)
  r8 : s.gpr .r8 = CE.oP s₀ + BitVec.ofNat 64 (b * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : C s
  frame : Frame [⟨CE.oP s₀, 32 * d⟩] s₀.mem s.mem
  done : ∀ k < b * i, s.mem (CE.oP s₀ + BitVec.ofNat 64 k) = (compressEncode d (CE.F s₀))[k]!

theorem byte_ofNat128' (V : Nat) {j : Nat} (hj : j < 16) :
    byte (BitVec.ofNat 128 V) j = BitVec.ofNat 8 (V / 2 ^ (8 * j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_byte, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨
    j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one] <;> omega_arith

theorem written8 (m : Mem) (o : Addr) (X : BitVec 64) :
    Written m (m.writeW o X) o 8 fun j => X.extractLsb' (8 * j) 8 := by
  intro x
  simp only [Mem.writeW, Mem.write, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem ext8_ofNat64 {U : Nat} (hU : U < 2 ^ 64) (j : Nat) :
    (BitVec.ofNat 64 U).extractLsb' (8 * j) 8 = BitVec.ofNat 8 (U / 2 ^ (8 * j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hU, Nat.shiftRight_eq_div_pow]

section
variable {ws : List Nat} {s₀ : State} (hp : (compressEncodeWK ws).pre s₀)
include hp

/-- The coefficient `c` of `f` in memory `m`, the output aside. -/
theorem coeffV {d : Nat} (hdd : dArg s₀ .rsi = d) {m : Mem} (hf : Frame [⟨CE.oP s₀, 32 * d⟩] s₀.mem m) {c : Nat}
    (hc : c < 256) : (m.readW (CE.fP s₀ + BitVec.ofNat 64 (4 * c)) 32).toNat = ((CE.F s₀)[c]!).val := by
  rw [← coeffAt_eq m (CE.fP s₀) c, CE.coeff hp hdd hf hc]
  exact (polyAt_val hp.2.2.2.2.2.2.2 (by rw [n_eq]; exact hc)).symm

theorem inR {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {o : Nat} (ho : o + 32 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (CE.fP s₀ + BitVec.ofNat 64 o) 32 := by
  rw [hrd, hwr, hp.1]
  exact ⟨_, List.mem_cons_self .., Offset.contains_base _ ho (by omega_arith)⟩

theorem outN {d : Nat} (hdd : dArg s₀ .rsi = d) {s : State} (hwr : s.wr = s₀.wr) {o n : Nat}
    (ho : o + n ≤ 32 * d) : InRegions s.wr (CE.oP s₀ + BitVec.ofNat 64 o) n := by
  have := (CE.lenEq hp hdd)
  rw [hwr, hp.2.1, this]
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ ho (by omega_arith)⟩

theorem step10 (hdd : dArg s₀ .rsi = 10) {i : Nat} (hi : i < 16) {s : State} (hI : Inv C10 64 10 20 s₀ i s) :
    WP isa (.block (cmLd 0 ++ toY cmHi ++ cmPack10 ++ ([.alu .add .rdi (.imm 64), .alu .add .r8 (.imm 20)] : List Instr) ++
        ([.alu .sub .rcx (.imm 1)] : List Instr))) s
      fun s' => Inv C10 64 10 20 s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) := by
  rw [show cmLd 0 ++ toY cmHi ++ cmPack10 ++ [.alu .add .rdi (.imm 64), .alu .add .r8 (.imm 20)] ++
      [.alu .sub .rcx (.imm 1)] = cmLd 0 ++ (toY cmHi ++ (cmPack10 ++
        ([.alu .add .rdi (.imm 64), .alu .add .r8 (.imm 20), .alu .sub .rcx (.imm 1)] : List Instr))) by
    simp only [List.append_assoc, List.cons_append, List.nil_append]]
  refine grp10_ok (z := fun j => (CE.F s₀)[16 * i + j]!) hI.c
    (by rw [hI.rdi, Offset.add_add]; exact inR hp hI.rd hI.wr (by omega_arith))
    (by rw [hI.rdi, Offset.add_add]; exact inR hp hI.rd hI.wr (by omega_arith))
    (fun j hj => by rw [hI.rdi, Offset.add_add, show 64 * i + (0 + 4 * j) = 4 * (16 * i + j) by omega_arith,
      coeffV hp hdd hI.frame (by omega_arith)])
    (by rw [hI.r8]; exact outN hp hdd hI.wr (by omega_arith))
    (by rw [hI.r8, Offset.add_add]; exact outN hp hdd hI.wr (by omega_arith))
    fun s1 m1 o1 g1 r1 w1 => ?_
  refine wp_addi' fun s2 u2 => wp_addi' fun s3 u3 => wp_subi' fun s4 u4 hz => WP.block_nil ?_
  have hV := digits_lt (w := 10) (L := (List.range 16).map fun (j : Nat) => compress 10 (CE.F s₀)[16 * i + j]!)
    (fun a ha => by obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha; exact compress_lt _ _)
  rw [List.length_map, List.length_range, show 10 * 16 = 160 from rfl] at hV
  have hV' : digits 10 ((List.range 16).map fun (j : Nat) => compress 10 (CE.F s₀)[16 * i + j]!) / 2 ^ 128 < 2 ^ 32 :=
    Nat.div_lt_of_lt_mul (by omega_arith)
  have hw : Written s.mem s1.mem (CE.oP s₀ + BitVec.ofNat 64 (20 * i)) (16 + 4) fun j =>
      (compressEncode 10 (CE.F s₀))[20 * i + j]! := by
    rw [m1, hI.r8]
    refine ((written16 _ _ _).append (written4 _ _ _) (by decide)).congr fun j hj => ?_
    rw [compressEncode_group (c := 16) (b := 20) (by decide) (by decide) _ (by omega_arith) hj]
    by_cases h : j < 16
    · rw [itT h, byte_ofNat128' _ h]
    · obtain ⟨t, rfl⟩ : ∃ t, j = 16 + t := ⟨j - 16, by omega_arith⟩
      rw [itF h, Nat.add_sub_cancel_left, ext8_ofNat hV' t, Nat.div_div_eq_div_mul, ← Nat.pow_add,
        show 128 + 8 * t = 8 * (16 + t) by omega_arith]
  obtain ⟨hf', hd'⟩ := Written.step (val := fun k => (compressEncode 10 (CE.F s₀))[k]!) hI.frame hI.done hw
    (show 20 * i + (16 + 4) ≤ 32 * 10 by omega_arith) (by decide)
  have hm4 : s4.mem = s1.mem := by rw [u4.mem, u3.mem, u2.mem]
  refine ⟨⟨?_, ?_, by rw [u4.rd, u3.rd, u2.rd, r1, hI.rd], by rw [u4.wr, u3.wr, u2.wr, w1, hI.wr],
    (((hI.c.pres fun r a b c d _ _ _ l hl => o1 r a b c d l hl).pres (Hi7.of_lane u2.lane)).pres
      (Hi7.of_lane u3.lane)).pres (Hi7.of_lane u4.lane),
    by rw [hm4]; exact hf', fun k hk => by rw [hm4]; exact hd' k (by omega_arith)⟩, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, g1 _ (by decide), hI.rdi,
      show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 64 * i + 64 = 64 * (i + 1) by omega_arith]
  · rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), g1 _ (by decide), hI.r8,
      show BitVec.signExtend 64 (20 : BitVec 32) = BitVec.ofNat 64 20 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 20 * i + 20 = 20 * (i + 1) by omega_arith]
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), g1 _ (by decide)]; rfl
  · rw [hz, u3.other _ (by decide), u2.other _ (by decide), g1 _ (by decide)]; rfl

theorem main10 (hdd : dArg s₀ .rsi = 10) :
    WP isa cm10 s₀ fun s' => bytesAt s'.mem (CE.oP s₀) (32 * 10) = compressEncode 10 (CE.F s₀) ∧
      Frame [⟨CE.oP s₀, 32 * 10⟩] s₀.mem s'.mem := by
  unfold cm10 rcxLoop
  rw [show (.mov .r8 (.reg .rdx) :: cm10Consts : List Instr) = .mov .r8 (.reg .rdx) :: (cm10Consts ++ []) by
    rw [List.append_nil]]
  refine WP.seq (wp_movr fun s0 u0 => consts10_ok fun s1 hc1 hg1 hm1 hr1 hw1 => WP.block_nil ?_)
  refine WP.seq (WP.seq (wp_mov32i fun s2 u2 => WP.block_nil ?_))
  refine wp_countdown (cnt := .rcx) (N := 16) (by decide) (by decide) (Inv C10 64 10 20 s₀)
    (fun i hi s hI _ => step10 hp hdd hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1, u0.rd],
      by rw [u2.wr, hw1, u0.wr], (hc1.pres (Hi7.of_lane u2.lane)), by rw [u2.mem, hm1, u0.mem]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega_arith)⟩ (by rw [u2.gpr]; rfl)
  · exact wp_vzu fun s3 _ m3 _ _ => WP.block_nil ⟨bytesAt_eq! (compressEncode_length _ _) fun k hk => by
      rw [m3]; exact hI.done k (by omega_arith), by rw [m3]; exact hI.frame⟩
  · rw [u2.other _ (by decide), hg1 _ (by decide), u0.other _ (by decide)]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide), u0.gpr]; simp

theorem step4 (hdd : dArg s₀ .rsi = 4) {i : Nat} (hi : i < 16) {s : State} (hI : Inv C4 64 4 8 s₀ i s) :
    WP isa (.block (cmLd 0 ++ toY cmLo ++ cmPack4 ++ ([.alu .add .rdi (.imm 64), .alu .add .r8 (.imm 8)] : List Instr) ++
        ([.alu .sub .rcx (.imm 1)] : List Instr))) s
      fun s' => Inv C4 64 4 8 s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) := by
  rw [show cmLd 0 ++ toY cmLo ++ cmPack4 ++ [.alu .add .rdi (.imm 64), .alu .add .r8 (.imm 8)] ++
      [.alu .sub .rcx (.imm 1)] = cmLd 0 ++ (toY cmLo ++ (cmPack4 ++
        ([.alu .add .rdi (.imm 64), .alu .add .r8 (.imm 8), .alu .sub .rcx (.imm 1)] : List Instr))) by
    simp only [List.append_assoc, List.cons_append, List.nil_append]]
  refine grp4_ok (z := fun j => (CE.F s₀)[16 * i + j]!) hI.c
    (by rw [hI.rdi, Offset.add_add]; exact inR hp hI.rd hI.wr (by omega_arith))
    (by rw [hI.rdi, Offset.add_add]; exact inR hp hI.rd hI.wr (by omega_arith))
    (fun j hj => by rw [hI.rdi, Offset.add_add, show 64 * i + (0 + 4 * j) = 4 * (16 * i + j) by omega_arith,
      coeffV hp hdd hI.frame (by omega_arith)])
    (by rw [hI.r8]; exact outN hp hdd hI.wr (by omega_arith)) fun s1 m1 o1 g1 r1 w1 => ?_
  refine wp_addi' fun s2 u2 => wp_addi' fun s3 u3 => wp_subi' fun s4 u4 hz => WP.block_nil ?_
  have hV := digits_lt (w := 4) (L := (List.range 16).map fun (j : Nat) => compress 4 (CE.F s₀)[16 * i + j]!)
    (fun a ha => by obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha; exact compress_lt _ _)
  rw [List.length_map, List.length_range, show 4 * 16 = 64 from rfl] at hV
  have hw : Written s.mem s1.mem (CE.oP s₀ + BitVec.ofNat 64 (8 * i)) 8 fun j =>
      (compressEncode 4 (CE.F s₀))[8 * i + j]! := by
    rw [m1, hI.r8]
    refine (written8 _ _ _).congr fun j hj => ?_
    rw [compressEncode_group (c := 16) (b := 8) (by decide) (by decide) _ (by omega_arith) hj, ext8_ofNat64 hV]
  obtain ⟨hf', hd'⟩ := Written.step (val := fun k => (compressEncode 4 (CE.F s₀))[k]!) hI.frame hI.done hw
    (show 8 * i + 8 ≤ 32 * 4 by omega_arith) (by decide)
  have hm4 : s4.mem = s1.mem := by rw [u4.mem, u3.mem, u2.mem]
  refine ⟨⟨?_, ?_, by rw [u4.rd, u3.rd, u2.rd, r1, hI.rd], by rw [u4.wr, u3.wr, u2.wr, w1, hI.wr],
    (((hI.c.pres fun r a b _ _ _ _ _ l hl => o1 r a b l hl).pres (Hi7.of_lane u2.lane)).pres
      (Hi7.of_lane u3.lane)).pres (Hi7.of_lane u4.lane),
    by rw [hm4]; exact hf', fun k hk => by rw [hm4]; exact hd' k (by omega_arith)⟩, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, g1 _ (by decide), hI.rdi,
      show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 64 * i + 64 = 64 * (i + 1) by omega_arith]
  · rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), g1 _ (by decide), hI.r8,
      show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 8 * i + 8 = 8 * (i + 1) by omega_arith]
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), g1 _ (by decide)]; rfl
  · rw [hz, u3.other _ (by decide), u2.other _ (by decide), g1 _ (by decide)]; rfl

theorem main4 (hdd : dArg s₀ .rsi = 4) :
    WP isa cm4 s₀ fun s' => bytesAt s'.mem (CE.oP s₀) (32 * 4) = compressEncode 4 (CE.F s₀) ∧
      Frame [⟨CE.oP s₀, 32 * 4⟩] s₀.mem s'.mem := by
  unfold cm4 rcxLoop
  rw [show (.mov .r8 (.reg .rdx) :: cm4Consts : List Instr) = .mov .r8 (.reg .rdx) :: (cm4Consts ++ []) by
    rw [List.append_nil]]
  refine WP.seq (wp_movr fun s0 u0 => consts4_ok fun s1 hc1 hg1 hm1 hr1 hw1 => WP.block_nil ?_)
  refine WP.seq (WP.seq (wp_mov32i fun s2 u2 => WP.block_nil ?_))
  refine wp_countdown (cnt := .rcx) (N := 16) (by decide) (by decide) (Inv C4 64 4 8 s₀)
    (fun i hi s hI _ => step4 hp hdd hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1, u0.rd],
      by rw [u2.wr, hw1, u0.wr], (hc1.pres (Hi7.of_lane u2.lane)), by rw [u2.mem, hm1, u0.mem]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega_arith)⟩ (by rw [u2.gpr]; rfl)
  · exact wp_vzu fun s3 _ m3 _ _ => WP.block_nil ⟨bytesAt_eq! (compressEncode_length _ _) fun k hk => by
      rw [m3]; exact hI.done k (by omega_arith), by rw [m3]; exact hI.frame⟩
  · rw [u2.other _ (by decide), hg1 _ (by decide), u0.other _ (by decide)]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide), u0.gpr]; simp

end

/-! ## The contracts -/

theorem wp10 {s₀ : State} (hp : (compressEncodeWK [10]).pre s₀) :
    WP isa cm10 s₀ fun s' =>
      bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = compressEncode (dArg s₀ .rsi) (CE.F s₀) ∧
        Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  have h10 : dArg s₀ .rsi = 10 := List.mem_singleton.mp hp.2.2.2.2.2.1
  rw [CE.lenEq hp h10, h10]
  exact main10 hp h10

theorem wp4 {s₀ : State} (hp : (compressEncodeWK [4]).pre s₀) :
    WP isa cm4 s₀ fun s' =>
      bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = compressEncode (dArg s₀ .rsi) (CE.F s₀) ∧
        Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  have h4 : dArg s₀ .rsi = 4 := List.mem_singleton.mp hp.2.2.2.2.2.1
  rw [CE.lenEq hp h4, h4]
  exact main4 hp h4

theorem correct10 (s : State) (hs : (compressEncodeWK [10]).pre s) :
    ∃ t s', Exec isa cm10 s t s' ∧ abiPreserved s s' ∧ (compressEncodeWK [10]).post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := cm10) [.rax, .rcx, .rdi, .r8] (wp10 hs) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem correct4 (s : State) (hs : (compressEncodeWK [4]).pre s) :
    ∃ t s', Exec isa cm4 s t s' ∧ abiPreserved s s' ∧ (compressEncodeWK [4]).post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := cm4) [.rax, .rcx, .rdi, .r8] (wp4 hs) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

end VG.Proof.MlKem.X86_64.CMY

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- The public inputs of a compression: its pointers and `len`, and `d`. -/
theorem cm_pub {ws : List Nat} (s₁ s₂ : State) (_ : (compressEncodeWK ws).pre s₁) (_ : (compressEncodeWK ws).pre s₂)
    (hp : (compressEncodeWK ws).pub s₁ s₂) : taint.Agree (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi]) s₁ s₂ :=
  agree_regsLo (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
    fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2

theorem cm10_ct : ConstantTime isa (compressEncodeWK [10]).pre (compressEncodeWK [10]).pub cm10 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi]) cm_pub (by taint_decide)

theorem cm4_ct : ConstantTime isa (compressEncodeWK [4]).pre (compressEncodeWK [4]).pub cm4 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi]) cm_pub (by taint_decide)

end VG.Proof.MlKem.X86_64
