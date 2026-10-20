module

public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompressAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Vec
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompressAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Vec
meta import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-KEM on x86-64: `ByteEncode_d ∘ Compress_d` with AVX2, which the K-PKE functions inline

The doublewords of a group are compressed by sums of shifts (`dword_ceV`),
and a lane of four values is packed into the number whose base-`2ᵈ` digits
they are (`pk10_lo`, `pk10_hi`, `pk4_lo`, `pk4_hi`): each step is followed
through the number the 128 bits hold (`toNat_eq_dwords`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.CEY

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.Sha3.X86_64 (WP.cons)
open S4 (LUpd wp_vbin wp_vvar wp_vld256 GUpd wp_addi' itT itF ext_app2 toNat_dword_ofBytes)
open D12Y (wp_vsh wp_subi' wp_vzu wp_mov32i yconst4_ok yconst_ok' wp_vbin128)
open DDY (mk rc dword_mk dword_rc toNat_and_mk lane4)

/-! ## The number a register holds -/

theorem toNat_app {m n : Nat} (a : BitVec m) (b : BitVec n) : (a ++ b).toNat = 2 ^ n * a.toNat + b.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt b.isLt]

theorem toNat_ofDwords (a b c d : BitVec 32) :
    (ofDwords a b c d).toNat = a.toNat + 2 ^ 32 * b.toNat + 2 ^ 64 * c.toNat + 2 ^ 96 * d.toNat := by
  simp only [ofDwords, toNat_app]; omega

theorem toNat_eq_dwords (x : BitVec 128) : x.toNat =
    (dword x 0).toNat + 2 ^ 32 * (dword x 1).toNat + 2 ^ 64 * (dword x 2).toNat + 2 ^ 96 * (dword x 3).toNat := by
  conv => lhs; rw [← ofDwords_dword x]
  rw [toNat_ofDwords]

theorem toNat_dword' (x : BitVec 128) (j : Nat) : (dword x j).toNat = x.toNat / 2 ^ (32 * j) % 2 ^ 32 := by
  rw [dword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem toNat_qword (x : BitVec 128) (j : Nat) : (qword x j).toNat = x.toNat / 2 ^ (64 * j) % 2 ^ 64 := by
  rw [qword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem toNat_byte (x : BitVec 128) (j : Nat) : (byte x j).toNat = x.toNat / 2 ^ (8 * j) % 2 ^ 8 := by
  rw [byte, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem toNat_ofBytes (f : Nat → BitVec 8) : (ofBytes f).toNat =
    (f 0).toNat + 2 ^ 8 * (f 1).toNat + 2 ^ 16 * (f 2).toNat + 2 ^ 24 * (f 3).toNat +
    2 ^ 32 * ((f 4).toNat + 2 ^ 8 * (f 5).toNat + 2 ^ 16 * (f 6).toNat + 2 ^ 24 * (f 7).toNat) +
    2 ^ 64 * ((f 8).toNat + 2 ^ 8 * (f 9).toNat + 2 ^ 16 * (f 10).toNat + 2 ^ 24 * (f 11).toNat) +
    2 ^ 96 * ((f 12).toNat + 2 ^ 8 * (f 13).toNat + 2 ^ 16 * (f 14).toNat + 2 ^ 24 * (f 15).toNat) := by
  rw [toNat_eq_dwords, toNat_dword_ofBytes _ (show 0 < 4 by decide), toNat_dword_ofBytes _ (show 1 < 4 by decide),
    toNat_dword_ofBytes _ (show 2 < 4 by decide), toNat_dword_ofBytes _ (show 3 < 4 by decide)]

/-! ## Compression of a doubleword -/

/-- `x · 161271` and `x · 2520`, by sums of shifts (`ceMul10`, `ceMul4`). -/
abbrev mul10 (x : BitVec 128) : BitVec 128 :=
  XBinOp.eval .psubd (XBinOp.eval .psubd (XBinOp.eval .paddd (XShiftOp.eval .pslld x (BitVec.ofNat 8 17))
      (XShiftOp.eval .pslld x (BitVec.ofNat 8 15)))
    (XBinOp.eval .paddd (XShiftOp.eval .pslld x (BitVec.ofNat 8 11)) (XShiftOp.eval .pslld x (BitVec.ofNat 8 9))))
    (XBinOp.eval .paddd (XShiftOp.eval .pslld x (BitVec.ofNat 8 3)) x)

abbrev mul4 (x : BitVec 128) : BitVec 128 :=
  XBinOp.eval .psubd (XBinOp.eval .paddd (XShiftOp.eval .pslld x (BitVec.ofNat 8 11))
      (XShiftOp.eval .pslld x (BitVec.ofNat 8 9)))
    (XBinOp.eval .paddd (XShiftOp.eval .pslld x (BitVec.ofNat 8 5)) (XShiftOp.eval .pslld x (BitVec.ofNat 8 3)))

/-- `((y + 262080) >> 19) ∧ (2ᵈ - 1)` (`ceRound`). -/
abbrev rnd (y : BitVec 128) (d : Nat) : BitVec 128 :=
  XBinOp.eval .pand (XShiftOp.eval .psrld (XBinOp.eval .paddd y (rc 262080)) (BitVec.ofNat 8 19)) (mk d)

theorem dword_mul10 (x : BitVec 128) {j : Nat} (hj : j < 4) (hx : (dword x j).toNat < 3329) :
    (dword (mul10 x) j).toNat = (dword x j).toNat * 161271 := by
  rw [dword_psubd _ _ hj, dword_psubd _ _ hj, dword_paddd _ _ hj, dword_paddd _ _ hj, dword_paddd _ _ hj,
    dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj,
    dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj]
  generalize dword x j = y at hx ⊢
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod]
  omega

theorem dword_mul4 (x : BitVec 128) {j : Nat} (hj : j < 4) (hx : (dword x j).toNat < 3329) :
    (dword (mul4 x) j).toNat = (dword x j).toNat * 2520 := by
  rw [dword_psubd _ _ hj, dword_paddd _ _ hj, dword_paddd _ _ hj,
    dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj,
    dword_pslld _ _ (by decide) hj]
  generalize dword x j = y at hx ⊢
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod]
  omega

theorem dword_rnd (y : BitVec 128) {d : Nat} (hd : d ≤ 31) {j : Nat} (hj : j < 4)
    (hy : (dword y j).toNat + 262080 < 2 ^ 32) :
    (dword (rnd y d) j).toNat = ((dword y j).toNat + 262080) / 2 ^ 19 % 2 ^ d := by
  rw [dword_pand, dword_mk hj, toNat_and_mk hd, dword_psrld _ _ (by decide) hj, dword_paddd _ _ hj, dword_rc hj,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [show (BitVec.ofNat 8 19).toNat = 19 from rfl]
  rw [Nat.mod_eq_of_lt hy]

/-! ## Packing -/

/-- The constants of the packing: the shifts of `vpsllvd` (`ymm8`), the mask of
`d = 10` (`ymm9`), the shifts of `vpsllvq` (`ymm10`), the masks of `vpshufb`
(`ymm11`). -/
def sv10 : BitVec 128 := 0x0000000a000000000000000a00000000#128
def qm20 : BitVec 128 := 0x00000000000fffff00000000000fffff#128
def qs20 : BitVec 128 := 0x00000000000000140000000000000000#128
def pm10a : BitVec 128 := 0x80808080808080808080800403020100#128
def pm10b : BitVec 128 := 0x80808080808004030201008080808080#128
def sv4 : BitVec 128 := 0x00000004000000000000000400000000#128
def pm4a : BitVec 128 := 0x80808080808080808080808080800800#128
def pm4b : BitVec 128 := 0x80808080808080808080808008008080#128

/-- The odd values shifted left by `d` and added to the even ones (`cePack`, before `vpshufb`). -/
abbrev pairs (R S : BitVec 128) : BitVec 128 :=
  let A := VVarOp.eval .vpsllvd R S
  XBinOp.eval .paddd A (XShiftOp.eval .psrlq A 32)

/-- A lane of `d = 10` packed, with the mask `M` of `vpshufb`. -/
abbrev pk10 (R M : BitVec 128) : BitVec 128 :=
  let E := VVarOp.eval .vpsllvq (XBinOp.eval .pand (pairs R sv10) qm20) qs20
  XBinOp.eval .pshufb (XBinOp.eval .paddq E (XShiftOp.eval .psrldq E 8)) M

/-- A lane of `d = 4` packed, with the mask `M` of `vpshufb`. -/
abbrev pk4 (R M : BitVec 128) : BitVec 128 := XBinOp.eval .pshufb (pairs R sv4) M

theorem qword_app0 (h l : BitVec 64) : qword (h ++ l) 0 = l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_zero, Nat.zero_add,
    decide_true, Bool.true_and, hi', ite_true]

theorem qword_app1 (h l : BitVec 64) : qword (h ++ l) 1 = h := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_one, hi', decide_true,
    Bool.true_and, show ¬64 + i < 64 by omega, ite_false, Nat.add_sub_cancel_left]

theorem byte_or (a b : BitVec 128) (i : Nat) : byte (a ||| b) i = byte a i ||| byte b i :=
  BitVec.extractLsb'_or

theorem byte_ofBytes (f : Nat → BitVec 8) {i : Nat} (hi : i < 16) : byte (ofBytes f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [byte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
  exact getLsbD_ofBytes f hi hr

theorem ext_byte {a b : BitVec 128} (h : ∀ i < 16, (byte a i).toNat = (byte b i).toNat) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (BitVec.getLsbD · (j % 8)) (BitVec.eq_of_toNat_eq (h (j / 8) (by omega)))
  simp only [byte, BitVec.getLsbD_extractLsb', decide_eq_true (Nat.mod_lt j (by omega : 8 > 0)),
    Bool.true_and] at this
  rwa [show 8 * (j / 8) + j % 8 = j by omega] at this

theorem toNat_qword0 (x : BitVec 128) : (qword x 0).toNat = (dword x 0).toNat + 2 ^ 32 * (dword x 1).toNat := by
  simp only [toNat_qword, toNat_dword', Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one]; omega

theorem toNat_qword1 (x : BitVec 128) : (qword x 1).toNat = (dword x 2).toNat + 2 ^ 32 * (dword x 3).toNat := by
  have := x.isLt
  simp only [toNat_qword, toNat_dword', Nat.reduceMul, Nat.reducePow] at this ⊢; omega

theorem toNat_byte_lo (x : BitVec 128) {i : Nat} (hi : i < 8) :
    (byte x i).toNat = (qword x 0).toNat / 2 ^ (8 * i) % 2 ^ 8 := by
  rw [toNat_byte, toNat_qword]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceMul, Nat.reducePow] <;> omega

theorem toNat_byte0 (x : BitVec 128) : (byte x 0).toNat = (dword x 0).toNat % 2 ^ 8 := by
  simp only [toNat_byte, toNat_dword', Nat.reduceMul, Nat.reducePow]; omega

theorem toNat_byte8 (x : BitVec 128) : (byte x 8).toNat = (dword x 2).toNat % 2 ^ 8 := by
  simp only [toNat_byte, toNat_dword', Nat.reduceMul, Nat.reducePow]; omega

theorem psrlq32 (A : BitVec 128) : XShiftOp.eval .psrlq A 32 = ofDwords (dword A 1) 0 (dword A 3) 0 := by
  apply BitVec.eq_of_toNat_eq
  have := A.isLt
  simp only [XShiftOp.eval, show (32 : BitVec 8).toNat = 32 from rfl, show ¬ 63 < 32 by decide, ↓reduceIte,
    toNat_app, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, toNat_qword, toNat_ofDwords, toNat_dword',
    show (0 : BitVec 32).toNat = 0 from rfl, Nat.reduceMul, Nat.reducePow] at this ⊢
  omega

/-- The doublewords of `pairs`: each odd value shifted left by `d` and added to the even one before it. -/
theorem dword_pairs {d : Nat} (hd : d ≤ 10) {R S : BitVec 128}
    (hS : (dword S 0).toNat = 0 ∧ (dword S 1).toNat = d ∧ (dword S 2).toNat = 0 ∧ (dword S 3).toNat = d)
    {a : Nat → Nat} (ha : ∀ j < 4, (dword R j).toNat = a j) (hb : ∀ j < 4, a j < 2 ^ d) :
    (dword (pairs R S) 0).toNat = a 0 + a 1 * 2 ^ d ∧ (dword (pairs R S) 2).toNat = a 2 + a 3 * 2 ^ d := by
  dsimp only [pairs]
  obtain ⟨h0, h1, h2, h3⟩ := hS
  have hd'' : 2 ^ d ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hd
  have b0 := hb 0 (by decide); have b1 := hb 1 (by decide); have b2 := hb 2 (by decide)
  have b3 := hb 3 (by decide)
  have hp20 : 2 ^ d * 2 ^ d ≤ 2 ^ 20 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have m1 : a 1 * 2 ^ d < 2 ^ 20 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right b1 (Nat.two_pow_pos d)) hp20
  have m3 : a 3 * 2 ^ d < 2 ^ 20 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right b3 (Nat.two_pow_pos d)) hp20
  rw [psrlq32, dword_paddd _ _ (by decide), dword_paddd _ _ (by decide), dword_ofDwords_0, dword_ofDwords_2]
  simp only [VVarOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, h0, h1, h2, h3,
    show 0 < 32 by decide, show d < 32 by omega, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), Nat.pow_zero,
    Nat.mul_one]
  generalize a 1 * 2 ^ d = c1 at m1 ⊢
  generalize a 3 * 2 ^ d = c3 at m3 ⊢
  omega

/-- The value of four values `< 2ᵈ` packed. -/
abbrev W (d : Nat) (a : Nat → Nat) : Nat := a 0 + 2 ^ d * a 1 + 2 ^ (2 * d) * a 2 + 2 ^ (3 * d) * a 3

/-- `pk10` before `vpshufb`: its low quadword holds the four values packed. -/
theorem pk10_G (R M : BitVec 128) {a : Nat → Nat} (ha : ∀ j < 4, (dword R j).toNat = a j)
    (hb : ∀ j < 4, a j < 2 ^ 10) :
    ∃ G, pk10 R M = XBinOp.eval .pshufb G M ∧ (qword G 0).toNat = W 10 a := by
  obtain ⟨hC0, hC2⟩ := dword_pairs (d := 10) (S := sv10) (Nat.le_refl _) ⟨rfl, rfl, rfl, rfl⟩ ha hb
  have b0 := hb 0 (by decide); have b1 := hb 1 (by decide); have b2 := hb 2 (by decide)
  have b3 := hb 3 (by decide)
  refine ⟨_, rfl, ?_⟩
  generalize pairs R sv10 = C at hC0 hC2
  have hD0 : (qword (XBinOp.eval .pand C qm20) 0).toNat = a 0 + a 1 * 2 ^ 10 := by
    rw [toNat_qword0, dword_pand, dword_pand, show dword qm20 0 = BitVec.ofNat 32 (2 ^ 20 - 1) from rfl,
      show dword qm20 1 = 0#32 from rfl, toNat_and_mk (by decide), BitVec.and_zero, hC0]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega
  have hD1 : (qword (XBinOp.eval .pand C qm20) 1).toNat = a 2 + a 3 * 2 ^ 10 := by
    rw [toNat_qword1, dword_pand, dword_pand, show dword qm20 2 = BitVec.ofNat 32 (2 ^ 20 - 1) from rfl,
      show dword qm20 3 = 0#32 from rfl, toNat_and_mk (by decide), BitVec.and_zero, hC2]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega
  generalize XBinOp.eval .pand C qm20 = D at hD0 hD1
  have hE : VVarOp.eval .vpsllvq D qs20 = (qword D 1 <<< 20) ++ (qword D 0 <<< 0) := by
    simp only [VVarOp.eval, show (qword qs20 0).toNat = 0 from rfl, show (qword qs20 1).toNat = 20 from rfl,
      show 0 < 64 by decide, show 20 < 64 by decide, ↓reduceIte]
  have hF : ∀ E : BitVec 128, (qword (XShiftOp.eval .psrldq E 8) 0).toNat = (qword E 1).toNat := fun E => by
    simp only [XShiftOp.eval, show (8 : BitVec 8).toNat = 8 from rfl, show min 8 16 * 8 = 64 from rfl, toNat_qword,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  simp only [XBinOp.eval, qword_app0, qword_app1, BitVec.toNat_add, hF, hE, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    hD0, hD1, Nat.pow_zero, Nat.mul_one, W]
  omega

/-- The two lanes of `d = 10` packed and combined (`vextracti128`, `vpor`): the eight values packed. -/
theorem pack10 {R₀ R₁ : BitVec 128} {a b : Nat → Nat} (ha : ∀ j < 4, (dword R₀ j).toNat = a j)
    (hb : ∀ j < 4, (dword R₁ j).toNat = b j) (ha' : ∀ j < 4, a j < 2 ^ 10) (hb' : ∀ j < 4, b j < 2 ^ 10) :
    XBinOp.eval .por (pk10 R₀ pm10a) (pk10 R₁ pm10b) = BitVec.ofNat 128 (W 10 a + 2 ^ 40 * W 10 b) := by
  obtain ⟨G₀, e₀, h₀⟩ := pk10_G R₀ pm10a ha ha'
  obtain ⟨G₁, e₁, h₁⟩ := pk10_G R₁ pm10b hb hb'
  have ea : XBinOp.eval .pshufb G₀ pm10a = ofBytes fun i => if i < 5 then byte G₀ i else 0 := by
    simp only [XBinOp.eval, ofBytes]; rfl
  have eb : XBinOp.eval .pshufb G₁ pm10b = ofBytes fun i => if 5 ≤ i ∧ i < 10 then byte G₁ (i - 5) else 0 := by
    simp only [XBinOp.eval, ofBytes]; rfl
  have a0 := ha' 0 (by decide); have a1 := ha' 1 (by decide); have a2 := ha' 2 (by decide)
  have a3 := ha' 3 (by decide); have b0 := hb' 0 (by decide); have b1 := hb' 1 (by decide)
  have b2 := hb' 2 (by decide); have b3 := hb' 3 (by decide)
  simp only [W, Nat.reduceMul, Nat.reducePow] at h₀ h₁ ⊢
  rw [e₀, e₁, ea, eb]
  refine ext_byte fun t ht => ?_
  simp only [XBinOp.eval, byte_or, byte_ofBytes _ ht, toNat_byte (BitVec.ofNat 128 _), BitVec.toNat_ofNat]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
    t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceLT, Nat.reduceLeDiff, and_true, and_false, ↓reduceIte, Nat.reduceSub,
    BitVec.toNat_or, Nat.or_zero, Nat.zero_or, toNat_byte_lo _ (show (0 : Nat) < 8 by decide),
    toNat_byte_lo _ (show (1 : Nat) < 8 by decide), toNat_byte_lo _ (show (2 : Nat) < 8 by decide),
    toNat_byte_lo _ (show (3 : Nat) < 8 by decide), toNat_byte_lo _ (show (4 : Nat) < 8 by decide), h₀, h₁,
    show (0 : BitVec 8).toNat = 0 from rfl, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one] <;>
  omega

/-- The two lanes of `d = 4` packed and combined: the eight values packed. -/
theorem pack4 {R₀ R₁ : BitVec 128} {a b : Nat → Nat} (ha : ∀ j < 4, (dword R₀ j).toNat = a j)
    (hb : ∀ j < 4, (dword R₁ j).toNat = b j) (ha' : ∀ j < 4, a j < 2 ^ 4) (hb' : ∀ j < 4, b j < 2 ^ 4) :
    XBinOp.eval .por (pk4 R₀ pm4a) (pk4 R₁ pm4b) = BitVec.ofNat 128 (W 4 a + 2 ^ 16 * W 4 b) := by
  obtain ⟨hA0, hA2⟩ := dword_pairs (d := 4) (S := sv4) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ha ha'
  obtain ⟨hB0, hB2⟩ := dword_pairs (d := 4) (S := sv4) (by decide) ⟨rfl, rfl, rfl, rfl⟩ hb hb'
  have a0 := ha' 0 (by decide); have a1 := ha' 1 (by decide); have a2 := ha' 2 (by decide)
  have a3 := ha' 3 (by decide); have b0 := hb' 0 (by decide); have b1 := hb' 1 (by decide)
  have b2 := hb' 2 (by decide); have b3 := hb' 3 (by decide)
  dsimp only [pk4]
  generalize pairs R₀ sv4 = C₀ at hA0 hA2
  generalize pairs R₁ sv4 = C₁ at hB0 hB2
  have ea : XBinOp.eval .pshufb C₀ pm4a =
      ofBytes fun i => if i = 0 then byte C₀ 0 else if i = 1 then byte C₀ 8 else 0 := by
    simp only [XBinOp.eval, ofBytes]; rfl
  have eb : XBinOp.eval .pshufb C₁ pm4b =
      ofBytes fun i => if i = 2 then byte C₁ 0 else if i = 3 then byte C₁ 8 else 0 := by
    simp only [XBinOp.eval, ofBytes]; rfl
  rw [ea, eb]
  simp only [W, Nat.reduceMul, Nat.reducePow] at hA0 hA2 hB0 hB2 ⊢
  refine ext_byte fun t ht => ?_
  simp only [XBinOp.eval, byte_or, byte_ofBytes _ ht, toNat_byte (BitVec.ofNat 128 _), BitVec.toNat_ofNat]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
    t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_or, Nat.or_zero, Nat.zero_or, toNat_byte0, toNat_byte8, hA0, hA2,
    hB0, hB2, show (0 : BitVec 8).toNat = 0 from rfl, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one] <;>
  omega

/-! ## The code of a group -/

theorem laneEq {s s' : State} {d : XReg} {v : Nat → BitVec 128} (u : LUpd s s' d v) {l : Nat} (hl : l < 2)
    (r : XReg) : s'.lane r l = if r = d then v l else s.lane r l := by
  by_cases h : r = d
  · subst h; rw [itT rfl]; exact u.val l hl
  · rw [itF h]; exact u.other r h l hl

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_vsh128 {op : XShiftOp} {d a : XReg} {n : BitVec 8}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then op.eval (s.lane a 0) n else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vshift op .l128 d a n) :: is)) s Q :=
  WP.cons rfl (k _ (LUpd.setV128 s d _ (op.eval (s.lane a 1) n)))

theorem wp_vmovdqa128 {d a : XReg}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then s.lane a 0 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vmovdqa .l128 d a) :: is)) s Q :=
  WP.cons rfl (k _ (LUpd.setV128 s d _ (s.lane a 1)))

theorem wp_vext1 {d a : XReg}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then s.lane a 1 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vextracti128 d a 1) :: is)) s Q :=
  WP.cons rfl (k _ (LUpd.setV128 s d _ 0))

theorem wp_vst128 {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.lane x l = s.lane x l) → s'.mem = s.mem.writeW a (s.lane r 0) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l128 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.lane r 0) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl)
  simp [exec, State.store128, ha, hout]; rfl

/-- `ceMul10` and `ceRound`: the doublewords of `ymm0` compressed to `ymm1`. -/
theorem mulRnd10_ok (hc12 : ∀ l < 2, s.lane .xmm12 l = rc 262080) (hc13 : ∀ l < 2, s.lane .xmm13 l = mk 10)
    (k : ∀ s', (∀ l < 2, s'.lane .xmm1 l = rnd (mul10 (s.lane .xmm0 l)) 10) →
      (∀ r, r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ceMul10 ++ ceRound ++ is)) s Q := by
  simp only [ceMul10, ceRound, ysl, ysr, yb, List.cons_append, List.nil_append]
  refine wp_vsh fun s1 u1 => wp_vsh fun s2 u2 => wp_vbin fun s3 u3 => wp_vsh fun s4 u4 => wp_vsh fun s5 u5 =>
    wp_vbin fun s6 u6 => wp_vbin fun s7 u7 => wp_vsh fun s8 u8 => wp_vbin fun s9 u9 => wp_vbin fun s10 u10 =>
    wp_vbin fun s11 u11 => wp_vsh fun s12 u12 => wp_vbin fun s13 u13 =>
      k s13 (fun l hl => ?_) (fun r a b c l hl => ?_) ?_ ?_ ?_ ?_
  · simp only [laneEq u13 hl, laneEq u12 hl, laneEq u11 hl, laneEq u10 hl, laneEq u9 hl, laneEq u8 hl,
      laneEq u7 hl, laneEq u6 hl, laneEq u5 hl, laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl,
      reduceCtorEq, ↓reduceIte, hc12 l hl, hc13 l hl]
    rfl
  · simp only [laneEq u13 hl, laneEq u12 hl, laneEq u11 hl, laneEq u10 hl, laneEq u9 hl, laneEq u8 hl,
      laneEq u7 hl, laneEq u6 hl, laneEq u5 hl, laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, a, b,
      c, ↓reduceIte]
  · rw [u13.gpr, u12.gpr, u11.gpr, u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · rw [u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u13.rd, u12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u13.wr, u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

/-- `ceMul4` and `ceRound`. -/
theorem mulRnd4_ok (hc12 : ∀ l < 2, s.lane .xmm12 l = rc 262080) (hc13 : ∀ l < 2, s.lane .xmm13 l = mk 4)
    (k : ∀ s', (∀ l < 2, s'.lane .xmm1 l = rnd (mul4 (s.lane .xmm0 l)) 4) →
      (∀ r, r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ceMul4 ++ ceRound ++ is)) s Q := by
  simp only [ceMul4, ceRound, ysl, ysr, yb, List.cons_append, List.nil_append]
  refine wp_vsh fun s1 u1 => wp_vsh fun s2 u2 => wp_vbin fun s3 u3 => wp_vsh fun s4 u4 => wp_vsh fun s5 u5 =>
    wp_vbin fun s6 u6 => wp_vbin fun s7 u7 => wp_vbin fun s8 u8 => wp_vsh fun s9 u9 => wp_vbin fun s10 u10 =>
      k s10 (fun l hl => ?_) (fun r a b c l hl => ?_) ?_ ?_ ?_ ?_
  · simp only [laneEq u10 hl, laneEq u9 hl, laneEq u8 hl, laneEq u7 hl, laneEq u6 hl, laneEq u5 hl,
      laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, reduceCtorEq, ↓reduceIte, hc12 l hl, hc13 l hl]
    rfl
  · simp only [laneEq u10 hl, laneEq u9 hl, laneEq u8 hl, laneEq u7 hl, laneEq u6 hl, laneEq u5 hl,
      laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, a, b, c, ↓reduceIte]
  · rw [u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

/-- `cePack true`: the lanes of `ymm1` packed into `xmm1`. -/
theorem pack10_ok (h8 : ∀ l < 2, s.lane .xmm8 l = sv10) (h9 : ∀ l < 2, s.lane .xmm9 l = qm20)
    (h10 : ∀ l < 2, s.lane .xmm10 l = qs20) (h11 : ∀ l < 2, s.lane .xmm11 l = if l = 0 then pm10a else pm10b)
    (k : ∀ s', s'.lane .xmm1 0 = XBinOp.eval .por (pk10 (s.lane .xmm1 0) pm10a) (pk10 (s.lane .xmm1 1) pm10b) →
      (∀ r, r ≠ .xmm1 → r ≠ .xmm2 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (cePack true ++ is)) s Q := by
  simp only [cePack, ↓reduceIte, yb, List.cons_append, List.nil_append]
  refine wp_vvar fun s1 u1 => wp_vsh fun s2 u2 => wp_vbin fun s3 u3 => wp_vbin fun s4 u4 => wp_vvar fun s5 u5 =>
    wp_vsh fun s6 u6 => wp_vbin fun s7 u7 => wp_vbin fun s8 u8 => wp_vext1 fun s9 u9 => wp_vbin128 fun s10 u10 =>
      k s10 ?_ (fun r a b l hl => ?_) ?_ ?_ ?_ ?_
  · have e8 : ∀ l < 2, s8.lane .xmm1 l = pk10 (s.lane .xmm1 l) (if l = 0 then pm10a else pm10b) := fun l hl => by
      simp only [laneEq u8 hl, laneEq u7 hl, laneEq u6 hl, laneEq u5 hl, laneEq u4 hl, laneEq u3 hl,
        laneEq u2 hl, laneEq u1 hl, reduceCtorEq, ↓reduceIte, h8 l hl, h9 l hl, h10 l hl, h11 l hl]
      rfl
    rw [u10.val 0 (by decide), itT rfl, u9.other .xmm1 (by decide) 0 (by decide), u9.val 0 (by decide), itT rfl,
      e8 0 (by decide), e8 1 (by decide)]
    rfl
  · simp only [laneEq u10 hl, laneEq u9 hl, laneEq u8 hl, laneEq u7 hl, laneEq u6 hl, laneEq u5 hl,
      laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, a, b, ↓reduceIte]
  · rw [u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

/-- `cePack false`. -/
theorem pack4_ok (h8 : ∀ l < 2, s.lane .xmm8 l = sv4) (h11 : ∀ l < 2, s.lane .xmm11 l = if l = 0 then pm4a else pm4b)
    (k : ∀ s', s'.lane .xmm1 0 = XBinOp.eval .por (pk4 (s.lane .xmm1 0) pm4a) (pk4 (s.lane .xmm1 1) pm4b) →
      (∀ r, r ≠ .xmm1 → r ≠ .xmm2 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (cePack false ++ is)) s Q := by
  simp only [cePack, Bool.false_eq_true, ↓reduceIte, yb, List.cons_append, List.nil_append]
  refine wp_vvar fun s1 u1 => wp_vsh fun s2 u2 => wp_vbin fun s3 u3 => wp_vbin fun s4 u4 => wp_vext1 fun s5 u5 =>
    wp_vbin128 fun s6 u6 => k s6 ?_ (fun r a b l hl => ?_) ?_ ?_ ?_ ?_
  · have e4 : ∀ l < 2, s4.lane .xmm1 l = pk4 (s.lane .xmm1 l) (if l = 0 then pm4a else pm4b) := fun l hl => by
      simp only [laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, reduceCtorEq, ↓reduceIte, h8 l hl,
        h11 l hl]
      rfl
    rw [u6.val 0 (by decide), itT rfl, u5.other .xmm1 (by decide) 0 (by decide), u5.val 0 (by decide), itT rfl,
      e4 0 (by decide), e4 1 (by decide)]
    rfl
  · simp only [laneEq u6 hl, laneEq u5 hl, laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, a, b,
      ↓reduceIte]
  · rw [u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

end

/-! ## The constants -/

/-- The constants of `d = 10`. -/
structure C10 (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = sv10
  c9 : ∀ l < 2, s.lane .xmm9 l = qm20
  c10 : ∀ l < 2, s.lane .xmm10 l = qs20
  c11 : ∀ l < 2, s.lane .xmm11 l = if l = 0 then pm10a else pm10b
  c12 : ∀ l < 2, s.lane .xmm12 l = rc 262080
  c13 : ∀ l < 2, s.lane .xmm13 l = mk 10

/-- The constants of `d = 4`. -/
structure C4 (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = sv4
  c11 : ∀ l < 2, s.lane .xmm11 l = if l = 0 then pm4a else pm4b
  c12 : ∀ l < 2, s.lane .xmm12 l = rc 262080
  c13 : ∀ l < 2, s.lane .xmm13 l = mk 4

/-- The vector registers from `ymm7` on are those of `s`. -/
def Hi7 (s s' : State) : Prop :=
  ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → r ≠ .xmm4 → r ≠ .xmm5 → r ≠ .xmm6 → ∀ l < 2,
    s'.lane r l = s.lane r l

theorem Hi7.of_lane {s s' : State} (h : ∀ x l, s'.lane x l = s.lane x l) : Hi7 s s' :=
  fun r _ _ _ _ _ _ _ l _ => h r l

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
      h.c13 l hl]⟩

theorem C4.pres {s s' : State} (h : C4 s) (hk : Hi7 s s') : C4 s' :=
  ⟨fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c8 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c11 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c12 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c13 l hl]⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem consts10_ok
    (k : ∀ s', C10 s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce10Consts ++ is)) s Q := by
  simp only [ce10Consts, List.append_assoc]
  refine yconst4_ok (by decide) (by decide) _ _ _ _ fun s1 a1 b1 o1 g1 m1 r1 w1 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s2 a2 b2 o2 g2 m2 r2 w2 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s3 a3 b3 o3 g3 m3 r3 w3 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s4 a4 b4 o4 g4 m4 r4 w4 =>
    yconst_ok' _ _ fun s5 a5 o5 g5 m5 r5 w5 => yconst_ok' _ _ fun s6 a6 o6 g6 m6 r6 w6 =>
    k s6 ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
      (fun g hg => ?_) ?_ ?_ ?_
  · rw [o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) (by decide) (by decide) l hl,
      o3 _ (by decide) (by decide) (by decide) l hl, o2 _ (by decide) (by decide) (by decide) l hl]
    exact (lane4 a1 b1 rfl rfl l hl).trans (by split <;> rfl)
  · rw [o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) (by decide) (by decide) l hl,
      o3 _ (by decide) (by decide) (by decide) l hl]
    exact (lane4 a2 b2 rfl rfl l hl).trans (by split <;> rfl)
  · rw [o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) (by decide) (by decide) l hl]
    exact (lane4 a3 b3 rfl rfl l hl).trans (by split <;> rfl)
  · rw [o6 _ (by decide) l hl, o5 _ (by decide) l hl]
    exact lane4 a4 b4 rfl rfl l hl
  · rw [o6 _ (by decide) l hl, a5 l hl]; rfl
  · rw [a6 l hl]; rfl
  · rw [g6 g hg, g5 g hg, g4 g hg, g3 g hg, g2 g hg, g1 g hg]
  · rw [m6, m5, m4, m3, m2, m1]
  · rw [r6, r5, r4, r3, r2, r1]
  · rw [w6, w5, w4, w3, w2, w1]

theorem consts4_ok
    (k : ∀ s', C4 s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce4Consts ++ is)) s Q := by
  simp only [ce4Consts, List.append_assoc]
  refine yconst4_ok (by decide) (by decide) _ _ _ _ fun s1 a1 b1 o1 g1 m1 r1 w1 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s2 a2 b2 o2 g2 m2 r2 w2 =>
    yconst_ok' _ _ fun s3 a3 o3 g3 m3 r3 w3 => yconst_ok' _ _ fun s4 a4 o4 g4 m4 r4 w4 =>
    k s4 ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩ (fun g hg => ?_) ?_ ?_ ?_
  · rw [o4 _ (by decide) l hl, o3 _ (by decide) l hl, o2 _ (by decide) (by decide) (by decide) l hl]
    exact (lane4 a1 b1 rfl rfl l hl).trans (by split <;> rfl)
  · rw [o4 _ (by decide) l hl, o3 _ (by decide) l hl]
    exact lane4 a2 b2 rfl rfl l hl
  · rw [o4 _ (by decide) l hl, a3 l hl]; rfl
  · rw [a4 l hl]; rfl
  · rw [g4 g hg, g3 g hg, g2 g hg, g1 g hg]
  · rw [m4, m3, m2, m1]
  · rw [r4, r3, r2, r1]
  · rw [w4, w3, w2, w1]

/-! ## A group -/

/-- A value compressed with the multiplier `M` to `d` bits. -/
abbrev cv (M d y : Nat) : Nat := (y * M + 262080) / 2 ^ 19 % 2 ^ d

theorem dword_ld (m : Mem) (a : Addr) {l i : Nat} (hl : l < 2) (hi : i < 4) :
    dword ((m.readW a 256).extractLsb' (128 * l) 128) i = m.readW (a + BitVec.ofNat 64 (16 * l + 4 * i)) 32 := by
  have := dword_load256 m a hl hi
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact this

theorem dv10 {X : BitVec 128} {j : Nat} (hj : j < 4) {y : Nat} (hy : (dword X j).toNat = y) (hq : y < 3329) :
    (dword (rnd (mul10 X) 10) j).toNat = cv 161271 10 y := by
  have hm := dword_mul10 X hj (by omega); rw [hy] at hm
  rw [dword_rnd _ (by decide) hj (by rw [hm]; omega), hm]

theorem dv4 {X : BitVec 128} {j : Nat} (hj : j < 4) {y : Nat} (hy : (dword X j).toNat = y) (hq : y < 3329) :
    (dword (rnd (mul4 X) 4) j).toNat = cv 2520 4 y := by
  have hm := dword_mul4 X hj (by omega); rw [hy] at hm
  rw [dword_rnd _ (by decide) hj (by rw [hm]; omega), hm]

/-- A group of `d = 10`: the eight coefficients `x` at `rdi + o`, compressed and packed into `xmm1`. -/
theorem grp10_ok {o : Nat} (hc : C10 s) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 o) 32)
    {x : Nat → Nat} (hx : ∀ j < 8, (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (o + 4 * j)) 32).toNat = x j)
    (hq : ∀ j < 8, x j < 3329)
    (k : ∀ s', s'.lane .xmm1 0 = BitVec.ofNat 128 (W 10 (fun j => cv 161271 10 (x j)) +
        2 ^ 40 * W 10 (fun j => cv 161271 10 (x (4 + j)))) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce10Grp o ++ is)) s Q := by
  rw [show ce10Grp o ++ is = .vmovdquLoad .l256 .xmm0 (at_ .rdi o) :: (ceMul10 ++ ceRound ++ (cePack true ++ is))
    by simp [ce10Grp]]
  refine wp_vld256 (a := s.gpr .rdi + BitVec.ofNat 64 o) (by rw [ea_at]) hin fun s1 u1 => ?_
  refine mulRnd10_ok (fun l hl => by rw [u1.other _ (by decide) l hl, hc.c12 l hl])
    (fun l hl => by rw [u1.other _ (by decide) l hl, hc.c13 l hl]) fun s2 h2 o2 g2 m2 r2 w2 => ?_
  refine pack10_ok (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl,
      hc.c8 l hl])
    (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl, hc.c9 l hl])
    (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl, hc.c10 l hl])
    (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl, hc.c11 l hl])
    fun s3 h3 o3 g3 m3 r3 w3 => k s3 ?_ (fun r a b c d l hl => by rw [o3 r b c l hl, o2 r b c d l hl,
      u1.other r a l hl]) (by rw [g3, g2, u1.gpr]) (by rw [m3, m2, u1.mem]) (by rw [r3, r2, u1.rd])
      (by rw [w3, w2, u1.wr])
  rw [h3, h2 0 (by decide), h2 1 (by decide), u1.val 0 (by decide), u1.val 1 (by decide)]
  refine pack10 (fun j hj => dv10 hj ?_ (hq j (by omega))) (fun j hj => dv10 hj ?_ (hq (4 + j) (by omega)))
    (fun _ _ => Nat.mod_lt _ (by decide)) (fun _ _ => Nat.mod_lt _ (by decide))
  · rw [dword_ld _ _ (by decide) hj, Offset.add_add, show o + (16 * 0 + 4 * j) = o + 4 * j by omega,
      hx j (by omega)]
  · rw [dword_ld _ _ (by decide) hj, Offset.add_add, show o + (16 * 1 + 4 * j) = o + 4 * (4 + j) by omega,
      hx (4 + j) (by omega)]

/-- A group of `d = 4`. -/
theorem grp4_ok {o : Nat} (hc : C4 s) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 o) 32)
    {x : Nat → Nat} (hx : ∀ j < 8, (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (o + 4 * j)) 32).toNat = x j)
    (hq : ∀ j < 8, x j < 3329)
    (k : ∀ s', s'.lane .xmm1 0 = BitVec.ofNat 128 (W 4 (fun j => cv 2520 4 (x j)) +
        2 ^ 16 * W 4 (fun j => cv 2520 4 (x (4 + j)))) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce4Grp o ++ is)) s Q := by
  rw [show ce4Grp o ++ is = .vmovdquLoad .l256 .xmm0 (at_ .rdi o) :: (ceMul4 ++ ceRound ++ (cePack false ++ is))
    by simp [ce4Grp]]
  refine wp_vld256 (a := s.gpr .rdi + BitVec.ofNat 64 o) (by rw [ea_at]) hin fun s1 u1 => ?_
  refine mulRnd4_ok (fun l hl => by rw [u1.other _ (by decide) l hl, hc.c12 l hl])
    (fun l hl => by rw [u1.other _ (by decide) l hl, hc.c13 l hl]) fun s2 h2 o2 g2 m2 r2 w2 => ?_
  refine pack4_ok (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl,
      hc.c8 l hl])
    (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl, hc.c11 l hl])
    fun s3 h3 o3 g3 m3 r3 w3 => k s3 ?_ (fun r a b c d l hl => by rw [o3 r b c l hl, o2 r b c d l hl,
      u1.other r a l hl]) (by rw [g3, g2, u1.gpr]) (by rw [m3, m2, u1.mem]) (by rw [r3, r2, u1.rd])
      (by rw [w3, w2, u1.wr])
  rw [h3, h2 0 (by decide), h2 1 (by decide), u1.val 0 (by decide), u1.val 1 (by decide)]
  refine pack4 (fun j hj => dv4 hj ?_ (hq j (by omega))) (fun j hj => dv4 hj ?_ (hq (4 + j) (by omega)))
    (fun _ _ => Nat.mod_lt _ (by decide)) (fun _ _ => Nat.mod_lt _ (by decide))
  · rw [dword_ld _ _ (by decide) hj, Offset.add_add, show o + (16 * 0 + 4 * j) = o + 4 * j by omega,
      hx j (by omega)]
  · rw [dword_ld _ _ (by decide) hj, Offset.add_add, show o + (16 * 1 + 4 * j) = o + 4 * (4 + j) by omega,
      hx (4 + j) (by omega)]

end

/-! ## The bytes of the encoding -/

theorem written16 (m : Mem) (o : Addr) (X : BitVec 128) : Written m (m.writeW o X) o 16 fun j => byte X j := by
  intro x
  simp only [Mem.writeW, Mem.write, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq, byte]

theorem byte_ofNat128 {V : Nat} (hV : V < 2 ^ 128) (j : Nat) : byte (BitVec.ofNat 128 V) j = BitVec.ofNat 8 (V / 2 ^ (8 * j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_byte, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV]

theorem dig8_10 (f : Nat → Nat) : digits 10 ((List.range 8).map f) = W 10 f + 2 ^ 40 * W 10 (fun j => f (4 + j)) := by
  show digits 10 [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] = _
  simp only [digits_cons, digits_nil, W, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd]
  omega

theorem dig32_4 (f : Nat → Nat) : digits 4 ((List.range 32).map f) =
    (W 4 (fun j => f (8 * 0 + j)) + 2 ^ 16 * W 4 (fun j => f (8 * 0 + (4 + j)))) +
    2 ^ 32 * (W 4 (fun j => f (8 * 1 + j)) + 2 ^ 16 * W 4 (fun j => f (8 * 1 + (4 + j)))) +
    2 ^ 64 * (W 4 (fun j => f (8 * 2 + j)) + 2 ^ 16 * W 4 (fun j => f (8 * 2 + (4 + j)))) +
    2 ^ 96 * (W 4 (fun j => f (8 * 3 + j)) + 2 ^ 16 * W 4 (fun j => f (8 * 3 + (4 + j)))) := by
  show digits 4 [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17,
    f 18, f 19, f 20, f 21, f 22, f 23, f 24, f 25, f 26, f 27, f 28, f 29, f 30, f 31] = _
  simp only [digits_cons, digits_nil, W, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd]
  omega

theorem cv10_eq (x : Zq) : cv 161271 10 x.val = compress 10 x := (compress_eq (d := 10) (by decide) x).symm

theorem cv4_eq (x : Zq) : cv 2520 4 x.val = compress 4 x := (compress_eq (d := 4) (by decide) x).symm

section
variable (s₀ : State)
/-- The eight values of group `g` of `d = 10`, packed. -/
abbrev Vg (g : Nat) : Nat := digits 10 ((List.range 8).map fun t => compress 10 (CE.F s₀)[8 * g + t]!)
/-- The four bytes of the eight values from `32 i + 8 k` of `d = 4`, packed. -/
abbrev Ug (i k : Nat) : Nat := W 4 (fun j => compress 4 (CE.F s₀)[32 * i + (8 * k + j)]!) +
  2 ^ 16 * W 4 (fun j => compress 4 (CE.F s₀)[32 * i + (8 * k + (4 + j))]!)
end

theorem Vg_lt (s₀ : State) (g : Nat) : Vg s₀ g < 2 ^ 80 := by
  have := digits_lt (w := 10) (L := (List.range 8).map fun (t : Nat) => compress 10 (CE.F s₀)[8 * g + t]!)
    (fun a ha => by
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
      exact compress_lt _ _)
  simpa using this

theorem Ug_lt (s₀ : State) (i k : Nat) : Ug s₀ i k < 2 ^ 32 := by
  have h := fun (t : Nat) => compress_lt 4 (CE.F s₀)[t]!
  simp only [Ug, W, Nat.reducePow] at h ⊢
  have := h (32 * i + (8 * k + 0)); have := h (32 * i + (8 * k + 1)); have := h (32 * i + (8 * k + 2))
  have := h (32 * i + (8 * k + 3)); have := h (32 * i + (8 * k + (4 + 0))); have := h (32 * i + (8 * k + (4 + 1)))
  have := h (32 * i + (8 * k + (4 + 2))); have := h (32 * i + (8 * k + (4 + 3)))
  omega

/-! ## The loops -/

/-- The bytes `E` below `n`, then those of `X` from `a`. -/
def mix (E : List Byte) (n : Nat) (X : BitVec 128) (a k : Nat) : Byte := if k < n then E[k]! else byte X (k - a)

/-- After `i` groups of `d = 10`. -/
structure Inv10 (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = CE.fP s₀ + BitVec.ofNat 64 (32 * i)
  r8 : s.gpr .r8 = CE.oP s₀ + BitVec.ofNat 64 (10 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : C10 s
  frame : Frame [⟨CE.oP s₀, 32 * 10⟩] s₀.mem s.mem
  done : ∀ k < 10 * i, s.mem (CE.oP s₀ + BitVec.ofNat 64 k) = (compressEncode 10 (CE.F s₀))[k]!
  last : 0 < i → s.lane .xmm1 0 = BitVec.ofNat 128 (Vg s₀ (i - 1))

/-- After `i` iterations of `d = 4`. -/
structure Inv4 (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = CE.fP s₀ + BitVec.ofNat 64 (128 * i)
  r8 : s.gpr .r8 = CE.oP s₀ + BitVec.ofNat 64 (16 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : C4 s
  frame : Frame [⟨CE.oP s₀, 32 * 4⟩] s₀.mem s.mem
  done : ∀ k < 16 * i, s.mem (CE.oP s₀ + BitVec.ofNat 64 k) = (compressEncode 4 (CE.F s₀))[k]!

/-- The 16 bytes of the last group of `d = 10`: the last six of the group before, then its ten. -/
theorem lastY {V₀ V₁ : Nat} (h₀ : V₀ < 2 ^ 80) (h₁ : V₁ < 2 ^ 80) {j : Nat} (hj : j < 16) :
    byte (XBinOp.eval .por (XShiftOp.eval .pslldq (BitVec.ofNat 128 V₁) 6)
      (XShiftOp.eval .psrldq (BitVec.ofNat 128 V₀) 4)) j =
      BitVec.ofNat 8 (if j < 6 then V₀ / 2 ^ (8 * (4 + j)) else V₁ / 2 ^ (8 * (j - 6))) := by
  have hY : (XBinOp.eval .por (XShiftOp.eval .pslldq (BitVec.ofNat 128 V₁) 6)
      (XShiftOp.eval .psrldq (BitVec.ofNat 128 V₀) 4)).toNat = 2 ^ 48 * V₁ + V₀ / 2 ^ 32 := by
    simp only [XBinOp.eval, XShiftOp.eval, show (6 : BitVec 8).toNat = 6 from rfl,
      show (4 : BitVec 8).toNat = 4 from rfl, show min 6 16 * 8 = 48 from rfl, show min 4 16 * 8 = 32 from rfl,
      BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    rw [show V₁ % 2 ^ 128 * 2 ^ 48 % 2 ^ 128 = 2 ^ 48 * V₁ by omega, show V₀ % 2 ^ 128 / 2 ^ 32 = V₀ / 2 ^ 32 by omega,
      ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_byte, hY, BitVec.toNat_ofNat]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨
    j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow] <;> omega

/-- The 16 bytes of an iteration of `d = 4`, interleaved from four groups. -/
theorem zbyte {U₀ U₁ U₂ U₃ : Nat} (h₀ : U₀ < 2 ^ 32) (h₁ : U₁ < 2 ^ 32) (h₂ : U₂ < 2 ^ 32) (h₃ : U₃ < 2 ^ 32)
    (j : Nat) :
    byte (XBinOp.eval .punpcklqdq (XBinOp.eval .punpckldq (BitVec.ofNat 128 U₀) (BitVec.ofNat 128 U₁))
      (XBinOp.eval .punpckldq (BitVec.ofNat 128 U₂) (BitVec.ofNat 128 U₃))) j =
      BitVec.ofNat 8 ((U₀ + 2 ^ 32 * U₁ + 2 ^ 64 * U₂ + 2 ^ 96 * U₃) / 2 ^ (8 * j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_byte, BitVec.toNat_ofNat]
  congr 2
  simp only [XBinOp.eval, toNat_app, toNat_qword0, dword_ofDwords_0, dword_ofDwords_1, toNat_dword',
    BitVec.toNat_ofNat, Nat.reduceMul, Nat.reducePow]
  omega

section
variable {s₀ : State} (hp : compressEncodeK.pre s₀)
include hp

/-- The coefficient `c` of `f` in memory `m`, the output aside. -/
theorem coeffV {d : Nat} (hdd : dArg s₀ .rsi = d) {m : Mem} (hf : Frame [⟨CE.oP s₀, 32 * d⟩] s₀.mem m) {c : Nat}
    (hc : c < 256) : (m.readW (CE.fP s₀ + BitVec.ofNat 64 (4 * c)) 32).toNat = ((CE.F s₀)[c]!).val := by
  rw [← coeffAt_eq m (CE.fP s₀) c, CE.coeff hp hdd hf hc]
  exact (polyAt_val hp.2.2.2.2.2.2.2 (by rw [n_eq]; exact hc)).symm

theorem inR {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {o : Nat} (ho : o + 32 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (CE.fP s₀ + BitVec.ofNat 64 o) 32 := by
  rw [hrd, hwr, hp.1]
  exact ⟨_, List.mem_cons_self .., Offset.contains_base _ ho (by omega)⟩

theorem outR {d : Nat} (hdd : dArg s₀ .rsi = d) {s : State} (hwr : s.wr = s₀.wr) {o : Nat} (ho : o + 16 ≤ 32 * d) :
    InRegions s.wr (CE.oP s₀ + BitVec.ofNat 64 o) 16 := by
  have := (CE.lenEq hp hdd)
  rw [hwr, hp.2.1, this]
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ ho (by omega)⟩

theorem step10 (hdd : dArg s₀ .rsi = 10) {i : Nat} (hi : i < 31) {s : State} (hI : Inv10 s₀ i s) :
    WP isa (.block (ce10Grp 0 ++ ([.vmovdquStore .l128 (at_ .r8 0) .xmm1, .alu .add .rdi (.imm 32),
        .alu .add .r8 (.imm 10), .alu .sub .rcx (.imm 1)] : List Instr))) s
      fun s' => Inv10 s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  refine grp10_ok (o := 0) (x := fun j => ((CE.F s₀)[8 * i + j]!).val) hI.c
    (by rw [hI.rdi, Offset.add_add]; exact inR hp hI.rd hI.wr (by omega))
    (fun j hj => by rw [hI.rdi, Offset.add_add, show 32 * i + (0 + 4 * j) = 4 * (8 * i + j) by omega,
      coeffV hp hdd hI.frame (by omega)]) (fun j _ => val_lt _) fun s1 h1 o1 g1 m1 r1 w1 => ?_
  have hX : s1.lane .xmm1 0 = BitVec.ofNat 128 (Vg s₀ i) := by
    rw [h1, Vg, dig8_10]; simp only [W, cv10_eq]
  refine wp_vst128 (a := CE.oP s₀ + BitVec.ofNat 64 (10 * i)) (by rw [ea_at, add_ofNat_zero, g1, hI.r8])
    (by rw [w1]; exact outR hp hdd hI.wr (by omega)) fun s2 g2 l2 m2 r2 w2 => ?_
  refine wp_addi' fun s3 u3 => wp_addi' fun s4 u4 => wp_subi' fun s5 u5 hz => WP.block_nil ?_
  have hw : Written s.mem s2.mem (CE.oP s₀ + BitVec.ofNat 64 (10 * i)) 16 fun j =>
      mix (compressEncode 10 (CE.F s₀)) (10 * (i + 1)) (BitVec.ofNat 128 (Vg s₀ i)) (10 * i) (10 * i + j) := by
    rw [m2, m1, hX]
    refine (written16 _ _ _).congr fun j hj => ?_
    rw [mix]
    by_cases h : j < 10
    · rw [itT (show 10 * i + j < 10 * (i + 1) by omega), compressEncode_group (c := 8) (b := 10) (by decide)
        (by decide) _ (by omega) h, byte_ofNat128 (Nat.lt_trans (Vg_lt s₀ i) (by decide))]
    · rw [itF (show ¬ 10 * i + j < 10 * (i + 1) by omega), show 10 * i + j - 10 * i = j by omega]
  obtain ⟨hf', hd'⟩ := Written.step (val := mix (compressEncode 10 (CE.F s₀)) (10 * (i + 1))
    (BitVec.ofNat 128 (Vg s₀ i)) (10 * i)) hI.frame (fun k hk => by
      rw [mix, itT (show k < 10 * (i + 1) by omega)]; exact hI.done k hk) hw
    (show 10 * i + 16 ≤ 32 * 10 by omega) (by decide)
  have hm5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  have hg2 : s2.gpr = s.gpr := by rw [g2, g1]
  refine ⟨⟨?_, ?_, by rw [u5.rd, u4.rd, u3.rd, r2, r1, hI.rd], by rw [u5.wr, u4.wr, u3.wr, w2, w1, hI.wr],
    ((((hI.c.pres fun r a b c d _ _ _ l hl => o1 r a b c d l hl).pres (Hi7.of_lane l2)).pres
      (Hi7.of_lane u3.lane)).pres (Hi7.of_lane u4.lane)).pres (Hi7.of_lane u5.lane),
    by rw [hm5]; exact hf', fun k hk => by rw [hm5, hd' k (by omega), mix, itT hk],
    fun _ => by rw [u5.lane, u4.lane, u3.lane, l2, hX, show i + 1 - 1 = i by omega]⟩, ?_, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, hg2, hI.rdi,
      show BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 32 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 32 * i + 32 = 32 * (i + 1) by omega]
  · rw [u5.other _ (by decide), u4.gpr, u3.other _ (by decide), hg2, hI.r8,
      show BitVec.signExtend 64 (10 : BitVec 32) = BitVec.ofNat 64 10 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 10 * i + 10 = 10 * (i + 1) by omega]
  · rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), hg2]; rfl
  · rw [hz, u4.other _ (by decide), u3.other _ (by decide), hg2]; rfl

/-- Group `g` of `d = 10`, from `rdi = fP + 32 g`. -/
theorem group10 (hdd : dArg s₀ .rsi = 10) {g : Nat} (hg : g < 32) {is : List Instr} {s : State}
    {Q : State → Prop} (hdi : s.gpr .rdi = CE.fP s₀ + BitVec.ofNat 64 (32 * g)) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hc : C10 s) (hf : Frame [⟨CE.oP s₀, 32 * 10⟩] s₀.mem s.mem)
    (k : ∀ s', s'.lane .xmm1 0 = BitVec.ofNat 128 (Vg s₀ g) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce10Grp 0 ++ is)) s Q :=
  grp10_ok (o := 0) (x := fun j => ((CE.F s₀)[8 * g + j]!).val) hc
    (by rw [hdi, Offset.add_add]; exact inR hp hrd hwr (by omega))
    (fun j hj => by rw [hdi, Offset.add_add, show 32 * g + (0 + 4 * j) = 4 * (8 * g + j) by omega,
      coeffV hp hdd hf (by omega)]) (fun j _ => val_lt _) fun s' h o gg m r w =>
    k s' (by rw [h, Vg, dig8_10]; simp only [W, cv10_eq]) o gg m r w

/-- Group `k` of iteration `i` of `d = 4`, from `rdi = fP + 128 i`. -/
theorem group4 (hdd : dArg s₀ .rsi = 4) {i k : Nat} (hi : i < 8) (hk : k < 4) {is : List Instr} {s : State}
    {Q : State → Prop} (hdi : s.gpr .rdi = CE.fP s₀ + BitVec.ofNat 64 (128 * i)) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hc : C4 s) (hf : Frame [⟨CE.oP s₀, 32 * 4⟩] s₀.mem s.mem)
    (K : ∀ s', s'.lane .xmm1 0 = BitVec.ofNat 128 (Ug s₀ i k) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce4Grp (32 * k) ++ is)) s Q :=
  grp4_ok (o := 32 * k) (x := fun j => ((CE.F s₀)[32 * i + (8 * k + j)]!).val) hc
    (by rw [hdi, Offset.add_add]; exact inR hp hrd hwr (by omega))
    (fun j hj => by rw [hdi, Offset.add_add, show 128 * i + (32 * k + 4 * j) = 4 * (32 * i + (8 * k + j)) by omega,
      coeffV hp hdd hf (by omega)]) (fun j _ => val_lt _) fun s' h o gg m r w =>
    K s' (by rw [h, Ug]; simp only [W, cv4_eq]) o gg m r w

theorem main10 (hdd : dArg s₀ .rsi = 10) {s : State} (hdi : s.gpr .rdi = CE.fP s₀) (h8 : s.gpr .r8 = CE.oP s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa ce10V s fun s' => bytesAt s'.mem (CE.oP s₀) (32 * 10) = compressEncode 10 (CE.F s₀) ∧
      Frame [⟨CE.oP s₀, 32 * 10⟩] s₀.mem s'.mem := by
  unfold ce10V
  refine WP.seq (consts10_ok fun s1 hc1 hg1 hm1 hr1 hw1 => wp_mov32i fun s2 u2 => WP.block_nil ?_)
  refine WP.seq (wp_countdown (cnt := .rcx) (N := 31) (by decide) (by decide) (Inv10 s₀)
    (fun i hi s hI _ => step10 hp hdd hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1, hrd],
      by rw [u2.wr, hw1, hwr], hc1.pres (Hi7.of_lane u2.lane), by rw [u2.mem, hm1, hm]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega), fun h => absurd h (by decide)⟩ (by rw [u2.gpr]; rfl))
  · have hL := hI.last (by decide)
    simp only [Nat.reduceSub] at hL
    refine wp_vsh128 fun s1 u1 => group10 hp hdd (g := 31) (by decide) (by rw [u1.gpr, hI.rdi]) (by rw [u1.rd, hI.rd])
      (by rw [u1.wr, hI.wr]) (hI.c.pres fun r _ _ _ _ a _ _ l hl => u1.other r a l hl) (by rw [u1.mem]; exact hI.frame)
      fun s2 h2 o2 g2 m2 r2 w2 => wp_vsh128 fun s3 u3 => wp_vbin128 fun s4 u4 => wp_subi' fun s5 u5 _ => ?_
    have hY : s5.lane .xmm1 0 = XBinOp.eval .por (XShiftOp.eval .pslldq (BitVec.ofNat 128 (Vg s₀ 31)) 6)
        (XShiftOp.eval .psrldq (BitVec.ofNat 128 (Vg s₀ 30)) 4) := by
      rw [u5.lane, u4.val 0 (by decide), itT rfl, u3.val 0 (by decide), itT rfl, u3.other .xmm4 (by decide) 0 (by decide),
        o2 .xmm4 (by decide) (by decide) (by decide) (by decide) 0 (by decide), u1.val 0 (by decide), itT rfl, h2, hL]
      rfl
    have hr8 : s5.gpr .r8 = CE.oP s₀ + BitVec.ofNat 64 304 := by
      rw [u5.gpr, u4.gpr, u3.gpr, g2, u1.gpr, hI.r8, show BitVec.signExtend 64 (6 : BitVec 32) = BitVec.ofNat 64 6 by decide,
        Offset.add_ofNat_sub _ (by decide)]
    refine wp_vst128 (a := CE.oP s₀ + BitVec.ofNat 64 304) (by rw [ea_at, add_ofNat_zero, hr8])
      (by rw [u5.wr, u4.wr, u3.wr, w2, u1.wr]; exact outR hp hdd hI.wr (by omega)) fun s6 g6 l6 m6 r6 w6 =>
      wp_vzu fun s7 _ m7 _ _ => WP.block_nil ?_
    have hw : Written s.mem s6.mem (CE.oP s₀ + BitVec.ofNat 64 304) 16 fun j =>
        (compressEncode 10 (CE.F s₀))[304 + j]! := by
      rw [m6, u5.mem, u4.mem, u3.mem, m2, u1.mem, hY]
      refine (written16 _ _ _).congr fun j hj => ?_
      rw [lastY (Vg_lt s₀ 30) (Vg_lt s₀ 31) hj]
      by_cases h : j < 6
      · rw [itT h, show 304 + j = 10 * 30 + (4 + j) by omega, compressEncode_group (c := 8) (b := 10) (by decide)
          (by decide) _ (by omega) (show 4 + j < 10 by omega)]
      · rw [itF h, show 304 + j = 10 * 31 + (j - 6) by omega, compressEncode_group (c := 8) (b := 10) (by decide)
          (by decide) _ (by omega) (show j - 6 < 10 by omega)]
    obtain ⟨hf', hd'⟩ := Written.step (val := fun k => (compressEncode 10 (CE.F s₀))[k]!) hI.frame
      (fun k hk => hI.done k (by omega)) hw (show 304 + 16 ≤ 32 * 10 by omega) (by decide)
    exact ⟨bytesAt_eq! (compressEncode_length _ _) fun k hk => by rw [m7]; exact hd' k (by omega),
      by rw [m7]; exact hf'⟩
  · rw [u2.other _ (by decide), hg1 _ (by decide), hdi]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide), h8]; simp

theorem step4 (hdd : dArg s₀ .rsi = 4) {i : Nat} (hi : i < 8) {s : State} (hI : Inv4 s₀ i s) :
    WP isa (.block (ce4Grp 0 ++ ([.vop (.vmovdqa .l128 .xmm4 .xmm1)] : List Instr) ++ ce4Grp 32 ++
        ([.vop (.vmovdqa .l128 .xmm5 .xmm1)] : List Instr) ++ ce4Grp 64 ++
        ([.vop (.vmovdqa .l128 .xmm6 .xmm1)] : List Instr) ++ ce4Grp 96 ++
        ([.vop (.vbin .vpunpckldq .l128 .xmm4 .xmm4 .xmm5), .vop (.vbin .vpunpckldq .l128 .xmm6 .xmm6 .xmm1),
          .vop (.vbin .vpunpcklqdq .l128 .xmm4 .xmm4 .xmm6), .vmovdquStore .l128 (at_ .r8 0) .xmm4,
          .alu .add .rdi (.imm 128), .alu .add .r8 (.imm 16), .alu .sub .rcx (.imm 1)] : List Instr))) s
      fun s' => Inv4 s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine group4 hp hdd (k := 0) hi (by decide) hI.rdi hI.rd hI.wr hI.c hI.frame fun s1 h1 o1 g1 m1 r1 w1 => ?_
  refine wp_vmovdqa128 fun s2 u2 => ?_
  have c2 := (hI.c.pres fun r a b c d _ _ _ l hl => o1 r a b c d l hl).pres fun r _ _ _ _ a _ _ l hl => u2.other r a l hl
  refine group4 hp hdd (k := 1) hi (by decide) (by rw [u2.gpr, g1, hI.rdi]) (by rw [u2.rd, r1, hI.rd])
    (by rw [u2.wr, w1, hI.wr]) c2 (by rw [u2.mem, m1]; exact hI.frame) fun s3 h3 o3 g3 m3 r3 w3 => ?_
  refine wp_vmovdqa128 fun s4 u4 => ?_
  have c4 := (c2.pres fun r a b c d _ _ _ l hl => o3 r a b c d l hl).pres fun r _ _ _ _ _ a _ l hl => u4.other r a l hl
  refine group4 hp hdd (k := 2) hi (by decide) (by rw [u4.gpr, g3, u2.gpr, g1, hI.rdi])
    (by rw [u4.rd, r3, u2.rd, r1, hI.rd]) (by rw [u4.wr, w3, u2.wr, w1, hI.wr]) c4
    (by rw [u4.mem, m3, u2.mem, m1]; exact hI.frame) fun s5 h5 o5 g5 m5 r5 w5 => ?_
  refine wp_vmovdqa128 fun s6 u6 => ?_
  have c6 := (c4.pres fun r a b c d _ _ _ l hl => o5 r a b c d l hl).pres fun r _ _ _ _ _ _ a l hl => u6.other r a l hl
  refine group4 hp hdd (k := 3) hi (by decide) (by rw [u6.gpr, g5, u4.gpr, g3, u2.gpr, g1, hI.rdi])
    (by rw [u6.rd, r5, u4.rd, r3, u2.rd, r1, hI.rd]) (by rw [u6.wr, w5, u4.wr, w3, u2.wr, w1, hI.wr]) c6
    (by rw [u6.mem, m5, u4.mem, m3, u2.mem, m1]; exact hI.frame) fun s7 h7 o7 g7 m7 r7 w7 => ?_
  refine wp_vbin128 fun s8 u8 => wp_vbin128 fun s9 u9 => wp_vbin128 fun s10 u10 => ?_
  have hg : s10.gpr = s.gpr := by
    rw [u10.gpr, u9.gpr, u8.gpr, g7, u6.gpr, g5, u4.gpr, g3, u2.gpr, g1]
  have hZ : s10.lane .xmm4 0 = XBinOp.eval .punpcklqdq
      (XBinOp.eval .punpckldq (BitVec.ofNat 128 (Ug s₀ i 0)) (BitVec.ofNat 128 (Ug s₀ i 1)))
      (XBinOp.eval .punpckldq (BitVec.ofNat 128 (Ug s₀ i 2)) (BitVec.ofNat 128 (Ug s₀ i 3))) := by
    rw [u10.val 0 (by decide), itT rfl, u9.val 0 (by decide), itT rfl,
      u9.other .xmm4 (by decide) 0 (by decide), u8.val 0 (by decide), itT rfl, u8.other .xmm6 (by decide) 0 (by decide),
      u8.other .xmm1 (by decide) 0 (by decide), h7,
      o7 .xmm4 (by decide) (by decide) (by decide) (by decide) 0 (by decide),
      o7 .xmm5 (by decide) (by decide) (by decide) (by decide) 0 (by decide),
      o7 .xmm6 (by decide) (by decide) (by decide) (by decide) 0 (by decide), u6.val 0 (by decide), itT rfl,
      u6.other .xmm4 (by decide) 0 (by decide), u6.other .xmm5 (by decide) 0 (by decide), h5,
      o5 .xmm4 (by decide) (by decide) (by decide) (by decide) 0 (by decide),
      o5 .xmm5 (by decide) (by decide) (by decide) (by decide) 0 (by decide), u4.val 0 (by decide), itT rfl,
      u4.other .xmm4 (by decide) 0 (by decide), h3, o3 .xmm4 (by decide) (by decide) (by decide) (by decide) 0 (by decide),
      u2.val 0 (by decide), itT rfl, h1]
    rfl
  refine wp_vst128 (a := CE.oP s₀ + BitVec.ofNat 64 (16 * i)) (by rw [ea_at, add_ofNat_zero, hg, hI.r8])
    (by rw [u10.wr, u9.wr, u8.wr, w7, u6.wr, w5, u4.wr, w3, u2.wr, w1]; exact outR hp hdd hI.wr (by omega))
    fun s11 g11 l11 m11 r11 w11 => ?_
  refine wp_addi' fun s12 u12 => wp_addi' fun s13 u13 => wp_subi' fun s14 u14 hz => WP.block_nil ?_
  have hw : Written s.mem s11.mem (CE.oP s₀ + BitVec.ofNat 64 (16 * i)) 16 fun j =>
      (compressEncode 4 (CE.F s₀))[16 * i + j]! := by
    rw [m11, u10.mem, u9.mem, u8.mem, m7, u6.mem, m5, u4.mem, m3, u2.mem, m1, hZ]
    refine (written16 _ _ _).congr fun j hj => ?_
    rw [zbyte (Ug_lt s₀ i 0) (Ug_lt s₀ i 1) (Ug_lt s₀ i 2) (Ug_lt s₀ i 3),
      compressEncode_group (c := 32) (b := 16) (by decide) (by decide) _ (by omega) hj, dig32_4]
  obtain ⟨hf', hd'⟩ := Written.step (val := fun k => (compressEncode 4 (CE.F s₀))[k]!) hI.frame hI.done hw
    (show 16 * i + 16 ≤ 32 * 4 by omega) (by decide)
  have hm14 : s14.mem = s11.mem := by rw [u14.mem, u13.mem, u12.mem]
  have hc14 : C4 s14 := ((((((c6.pres fun r a b c d _ _ _ l hl => o7 r a b c d l hl).pres
    fun r _ _ _ _ a _ _ l hl => u8.other r a l hl).pres fun r _ _ _ _ _ _ a l hl => u9.other r a l hl).pres
    fun r _ _ _ _ a _ _ l hl => u10.other r a l hl).pres (Hi7.of_lane l11)).pres
    (Hi7.of_lane u12.lane)).pres (Hi7.of_lane u13.lane) |>.pres (Hi7.of_lane u14.lane)
  refine ⟨⟨?_, ?_, by rw [u14.rd, u13.rd, u12.rd, r11, u10.rd, u9.rd, u8.rd, r7, u6.rd, r5, u4.rd, r3, u2.rd, r1, hI.rd],
    by rw [u14.wr, u13.wr, u12.wr, w11, u10.wr, u9.wr, u8.wr, w7, u6.wr, w5, u4.wr, w3, u2.wr, w1, hI.wr], hc14,
    by rw [hm14]; exact hf', fun k hk => by rw [hm14]; exact hd' k (by omega)⟩, ?_, ?_⟩
  · rw [u14.other _ (by decide), u13.other _ (by decide), u12.gpr, g11, hg, hI.rdi,
      show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 128 * i + 128 = 128 * (i + 1) by omega]
  · rw [u14.other _ (by decide), u13.gpr, u12.other _ (by decide), g11, hg, hI.r8,
      show BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 16 * i + 16 = 16 * (i + 1) by omega]
  · rw [u14.gpr, u13.other _ (by decide), u12.other _ (by decide), g11, hg]; rfl
  · rw [hz, u13.other _ (by decide), u12.other _ (by decide), g11, hg]; rfl

theorem main4 (hdd : dArg s₀ .rsi = 4) {s : State} (hdi : s.gpr .rdi = CE.fP s₀) (h8 : s.gpr .r8 = CE.oP s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa ce4V s fun s' => bytesAt s'.mem (CE.oP s₀) (32 * 4) = compressEncode 4 (CE.F s₀) ∧
      Frame [⟨CE.oP s₀, 32 * 4⟩] s₀.mem s'.mem := by
  unfold ce4V
  refine WP.seq (consts4_ok fun s1 hc1 hg1 hm1 hr1 hw1 => wp_mov32i fun s2 u2 => WP.block_nil ?_)
  refine WP.seq (wp_countdown (cnt := .rcx) (N := 8) (by decide) (by decide) (Inv4 s₀)
    (fun i hi s hI _ => step4 hp hdd hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1, hrd],
      by rw [u2.wr, hw1, hwr], hc1.pres (Hi7.of_lane u2.lane), by rw [u2.mem, hm1, hm]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega)⟩ (by rw [u2.gpr]; rfl))
  · exact wp_vzu fun s3 _ m3 _ _ => WP.block_nil ⟨bytesAt_eq! (compressEncode_length _ _) fun k hk => by
      rw [m3]; exact hI.done k (by omega), by rw [m3]; exact hI.frame⟩
  · rw [u2.other _ (by decide), hg1 _ (by decide), hdi]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide), h8]; simp

end

theorem wp {s₀ : State} (hp : compressEncodeK.pre s₀) :
    WP isa compressEncodeAvx2 s₀ fun s' =>
      bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = compressEncode (dArg s₀ .rsi) (CE.F s₀) ∧
        Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  have hd := hp.2.2.2.2.2.1
  rw [CE.lenEq hp rfl]
  unfold compressEncodeAvx2
  refine WP.seq (WP.mono (cePrologue_ok s₀) fun s₁ ⟨⟨si₁, r8₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    have h1 : dArg s₀ .rsi = 1 := by simp only [dArg, h]; rfl
    rw [h1]
    exact CE.loop_ok (d := 1) (c := 8) (b := 1) hp (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h1 (M := ceMul 1) (r := 262080) (fun x => ⟨compress_arg_lt (by decide) x, compress_eq (by decide) x⟩)
      (fun i hi s hs => CE.grp_ok (by decide) (by decide) (by decide) (by decide) _ (by omega) (by omega) hs)
      (by decide) di₁ r8₁ k₁.2.1 k₁.2.2 m₁
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    refine WP.seq (WP.mono (cmp32_ok .rsi 4 s₁) fun s₂ ⟨⟨z₂, m₂⟩, k₂⟩ => ?_)
    rw [si₁, BitVec.setWidth_32_64_32] at z₂
    have di₂ : s₂.gpr .rdi = CE.fP s₀ := by rw [k₂.gpr (by decide), di₁]
    have r8₂ : s₂.gpr .r8 = CE.oP s₀ := by rw [k₂.gpr (by decide), r8₁]
    refine WP.ite (M := isa) _ (show isa.eval .e s₂ = _ from z₂) (fun h' => ?_) (fun h' => ?_)
    · rw [sub_beq_zero32, decide_eq_true_eq] at h'
      have h4 : dArg s₀ .rsi = 4 := by simp only [dArg, h']; rfl
      rw [h4]
      exact main4 hp h4 di₂ r8₂ (by rw [k₂.2.1, k₁.2.1]) (by rw [k₂.2.2, k₁.2.2]) (by rw [m₂, m₁])
    · rw [sub_beq_zero32, decide_eq_false_iff_not] at h'
      have h10 : dArg s₀ .rsi = 10 := by
        rcases mem_compressWidths hd with e | e | e
        · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h
        · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h'
        · exact e
      rw [h10]
      exact main10 hp h10 di₂ r8₂ (by rw [k₂.2.1, k₁.2.1]) (by rw [k₂.2.2, k₁.2.2]) (by rw [m₂, m₁])

theorem correct (s : State) (hs : compressEncodeK.pre s) :
    ∃ t s', Exec isa compressEncodeAvx2 s t s' ∧ abiPreserved s s' ∧ compressEncodeK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := compressEncodeAvx2)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] (wp hs) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

end VG.Proof.MlKem.X86_64.CEY

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

theorem compressEncodeY_ct :
    ConstantTime isa compressEncodeK.pre compressEncodeK.pub compressEncodeAvx2 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

end VG.Proof.MlKem.X86_64
