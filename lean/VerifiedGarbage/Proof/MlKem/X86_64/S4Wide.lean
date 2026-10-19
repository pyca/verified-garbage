module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4Vec
public import VerifiedGarbage.Proof.Framework.X86_64.Words

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, sixteen candidates at once

The vector step of the sampling (`Sample4.vcand`, `Sample4.vput`) on the 24
bytes at `rsi`: of the 32 bytes it loads, `vpermq` puts bytes 0 to 15 in
the low lane and 8 to 23 in the high one (`perm_lanes`); `vpshufb`, `vpsrlw`,
`vpblendw` and `vpand` make candidate `8 l + i` of `SampleNTT` word `i` of
lane `l` (`cand_word`); `vpcmpgtw`, `vpacksswb` and `vpmovmskb` give the
masks `m₀`, `m₁` of the candidates less than `q` of each lane
(`mask_toNat`); the static's mask of each (`idxV`) moves its candidates to
the bottom of its lane (`pshufb_idxV`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64
open VG.Impl.MlKem.X86_64.Sample4 (idxV idxQ setBits)
open VG.Proof.Sha3.X86_64 (WP.cons Upd)

/-! ## The constants -/

/-- The `vpshufb` mask of lane `l` (`ymm8`). -/
def shufW (l : Nat) : BitVec 128 :=
  if l = 0 then 0x0b0a0a09080707060504040302010100#128 else 0x0f0e0e0d0c0b0b0a0908080706050504#128

/-- `0xfff` in each word (`ymm9`). -/
def fffW : BitVec 128 := 0x0fff0fff0fff0fff0fff0fff0fff0fff#128

/-- `q` in each word (`ymm10`). -/
def qW : BitVec 128 := 0x0d010d010d010d010d010d010d010d01#128

/-- The constants of the vector code in `ymm8` to `ymm10`. -/
structure VC (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = shufW l
  c9 : ∀ l < 2, s.lane .xmm9 l = fffW
  c10 : ∀ l < 2, s.lane .xmm10 l = qW

/-! ## The candidates -/

/-- Byte `k` of a 256-bit value. -/
abbrev byteY (X : BitVec 256) (k : Nat) : BitVec 8 := X.extractLsb' (8 * k) 8

/-- Lane `l` after `vpermq` with `0x94`: bytes `8 l` to `8 l + 15`. -/
abbrev laneP (X : BitVec 256) (l : Nat) : BitVec 128 := X.extractLsb' (64 * l) 128

theorem permQ94 (X : BitVec 256) :
    permQwords X 0x94 = qword256 X 2 ++ qword256 X 1 ++ qword256 X 1 ++ qword256 X 0 := rfl

theorem q4_bit (a b c d : BitVec 64) (j : Nat) : (a ++ b ++ c ++ d).getLsbD j =
    if j < 64 then d.getLsbD j else if j < 128 then c.getLsbD (j - 64)
    else if j < 192 then b.getLsbD (j - 128) else a.getLsbD (j - 192) := by
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases h1 : j < 64
  · rw [itT h1, itT h1]
  rw [itF h1, itF h1]
  by_cases h2 : j - 64 < 64
  · rw [itT h2, itT (show j < 128 by omega)]
  rw [itF h2, itF (show ¬ j < 128 by omega)]
  by_cases h3 : j - 64 - 64 < 64
  · rw [itT h3, itT (show j < 192 by omega), show j - 64 - 64 = j - 128 by omega]
  · rw [itF h3, itF (show ¬ j < 192 by omega), show j - 64 - 64 - 64 = j - 192 by omega]

theorem qword256_bit (X : BitVec 256) (i k : Nat) (hk : k < 64) :
    (qword256 X i).getLsbD k = X.getLsbD (64 * i + k) := by
  rw [qword256, BitVec.getLsbD_extractLsb', decide_eq_true hk, Bool.true_and]

theorem perm_lane (X : BitVec 256) {l : Nat} (hl : l < 2) :
    (permQwords X 0x94).extractLsb' (128 * l) 128 = laneP X l := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [permQ94, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and,
    Bool.true_and, q4_bit]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · by_cases a : j < 64
    · rw [itT (show 128 * 0 + j < 64 by omega), qword256_bit X 0 (128 * 0 + j) (by omega)]; congr 1; omega
    · rw [itF (show ¬ 128 * 0 + j < 64 by omega), itT (show 128 * 0 + j < 128 by omega),
        qword256_bit X 1 (128 * 0 + j - 64) (by omega)]; congr 1; omega
  · rw [show 128 * 1 + j = j + 128 by omega]
    by_cases a : j < 64
    · rw [itF (show ¬ j + 128 < 64 by omega), itF (show ¬ j + 128 < 128 by omega),
        itT (show j + 128 < 192 by omega), show j + 128 - 128 = j by omega, qword256_bit X 1 j a]
    · rw [itF (show ¬ j + 128 < 64 by omega), itF (show ¬ j + 128 < 128 by omega),
        itF (show ¬ j + 128 < 192 by omega), show j + 128 - 192 = j - 64 by omega,
        qword256_bit X 2 (j - 64) (by omega)]
      congr 1; omega

theorem byte_laneP (X : BitVec 256) {l j : Nat} (hj : j < 16) :
    byte (laneP X l) j = byteY X (8 * l + j) := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  simp only [byte, BitVec.getLsbD_extractLsb', hm, decide_true, Bool.true_and,
    show 8 * j + m < 128 by omega]
  congr 1; omega

theorem pshufb_shufW (a : BitVec 128) {l : Nat} (hl : l < 2) :
    XBinOp.eval .pshufb a (shufW l) = ofBytes fun j => byte a (cb (j / 2) + 4 * l + j % 2) := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
  · simp only [XBinOp.eval, ofBytes, shufW]
    rfl

theorem toNat_word_ofBytes (f : Nat → BitVec 8) {i : Nat} (hi : i < 8) :
    (word (ofBytes f) i).toNat = (f (2 * i)).toNat + 256 * (f (2 * i + 1)).toNat := by
  have e : word (ofBytes f) i = f (2 * i + 1) ++ f (2 * i) := by
    apply BitVec.eq_of_getLsbD_eq; intro m hm
    rw [getLsbD_word, decide_eq_true hm, Bool.true_and, show 16 * i + m = 8 * (2 * i + m / 8) + m % 8 by omega,
      getLsbD_ofBytes _ (by omega) (by omega), BitVec.getLsbD_append]
    by_cases a : m < 8
    · rw [itT a]; exact gb (by omega) (by omega)
    · rw [itF a]; exact gb (by omega) (by omega)
  rw [e, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (f (2 * i)).isLt, Nat.shiftLeft_eq]
  omega

/-- Lane `l` of the candidates, from the 32 bytes `X`. -/
def candW (X : BitVec 256) (l : Nat) : BitVec 128 :=
  let P := XBinOp.eval .pshufb (laneP X l) (shufW l)
  XBinOp.eval .pand (blendWords P (XShiftOp.eval .psrlw P 4) 0xAA) fffW

theorem cand_word (X : BitVec 256) {l i : Nat} (hl : l < 2) (hi : i < 8) :
    (word (candW X l) i).toNat = candN (fun k => (byteY X k).toNat) (8 * l + i) := by
  have hb : ∀ k, (byteY X k).toNat < 256 := fun k => (byteY X k).isLt
  have hP : (word (XBinOp.eval .pshufb (laneP X l) (shufW l)) i).toNat =
      (byteY X (cb (8 * l + i))).toNat + 256 * (byteY X (cb (8 * l + i) + 1)).toNat := by
    have e0 : 8 * l + (cb (2 * i / 2) + 4 * l + 2 * i % 2) = cb (8 * l + i) := by simp only [cb]; omega
    have e1 : 8 * l + (cb ((2 * i + 1) / 2) + 4 * l + (2 * i + 1) % 2) = cb (8 * l + i) + 1 := by
      simp only [cb]; omega
    rw [pshufb_shufW _ hl, toNat_word_ofBytes _ hi, byte_laneP _ (by simp only [cb]; omega),
      byte_laneP _ (by simp only [cb]; omega), e0, e1]
  simp only [candW]
  rw [word_pand, BitVec.toNat_and, show word fffW i = 0xfff#16 by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl,
    show (0xfff#16).toNat = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, blendWords, word_ofWords _ hi]
  have hcb : cb (8 * l + i) = 12 * l + cb i := by simp only [cb]; omega
  have b0 := hb (cb (8 * l + i)); have b1 := hb (cb (8 * l + i) + 1)
  by_cases h : (0xAA : BitVec 8).getLsbD i
  · have hodd : i % 2 = 1 := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    rw [itT h, XShiftOp.eval]
    dsimp only
    rw [itF (show ¬ 15 < (4 : BitVec 8).toNat by decide), word_ofWords _ hi, BitVec.toNat_ushiftRight, hP,
      Nat.shiftRight_eq_div_pow, candN, itF (show ¬ (8 * l + i) % 2 = 0 by omega),
      show (4 : BitVec 8).toNat = 4 from rfl, hcb]
    simp only [cb] at b0 b1 ⊢
    omega
  · have hev : i % 2 = 0 := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    rw [itF h, hP, candN, itT (show (8 * l + i) % 2 = 0 by omega), hcb]
    simp only [cb] at b0 b1 ⊢
    omega

/-! ## The mask -/

/-- Byte `i` of `ofBytes f`. -/
theorem byte_ofBytes' (f : Nat → BitVec 8) {i : Nat} (hi : i < 16) : byte (ofBytes f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [byte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
  exact getLsbD_ofBytes f hi hr

/-- The bytes of each lane after `vpcmpgtw` with `q` and `vpacksswb`. -/
def maskW (X : BitVec 256) (l : Nat) : BitVec 128 :=
  let K := XBinOp.eval .pcmpgtw qW (candW X l)
  XBinOp.eval .packsswb K K

/-- The mask of the candidates less than `q` of lane `l`. -/
def maskL (X : BitVec 256) (l : Nat) : Nat :=
  bsum (fun i => decide (candN (fun k => (byteY X k).toNat) (8 * l + i) < 3329)) 8

theorem candN_lt' (X : BitVec 256) (k : Nat) : candN (fun k => (byteY X k).toNat) k < 4096 :=
  candN_lt _ (fun i => (byteY X i).isLt) k

theorem packsswb_eval (a b : BitVec 128) : XBinOp.eval .packsswb a b =
    ofBytes fun i => if i < 8 then satSignedByte (word a i) else satSignedByte (word b (i - 8)) := rfl

theorem slt_q {x : BitVec 16} (h : x.toNat < 4096) : x.slt 0x0d01#16 = decide (x.toNat < 3329) := by
  have e : x.toInt = x.toNat := by rw [BitVec.toInt_eq_toNat_cond, ite_eq_left (by omega)]
  rw [BitVec.slt, e, show (0x0d01#16).toInt = 3329 from rfl]
  by_cases hq : x.toNat < 3329 <;> simp [hq] <;> omega

theorem maskW_bit (X : BitVec 256) {l j : Nat} (hl : l < 2) (hj : j < 16) :
    (maskW X l).getLsbD (8 * j + 7) =
      decide (candN (fun k => (byteY X k).toNat) (8 * l + j % 8) < 3329) := by
  have hw : ∀ i < 8, word (XBinOp.eval .pcmpgtw qW (candW X l)) i =
      if candN (fun k => (byteY X k).toNat) (8 * l + i) < 3329 then (0xFFFF : BitVec 16) else 0 := fun i hi => by
    have hc := cand_word X hl hi
    rw [XBinOp.eval, word_ofWords _ hi, show word qW i = 0x0d01#16 by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl,
      slt_q (by rw [hc]; exact candN_lt' X _), hc]
    simp only [decide_eq_true_eq]
  simp only [maskW]
  rw [packsswb_eval, getLsbD_ofBytes _ hj (by decide)]
  have hk : (if j < 8 then j else j - 8) = j % 8 := by split <;> omega
  have e : (if j < 8 then satSignedByte (word (XBinOp.eval .pcmpgtw qW (candW X l)) j)
      else satSignedByte (word (XBinOp.eval .pcmpgtw qW (candW X l)) (j - 8))) =
      satSignedByte (word (XBinOp.eval .pcmpgtw qW (candW X l)) (j % 8)) := by
    split <;> congr 2 <;> omega
  rw [e, hw _ (Nat.mod_lt _ (by decide))]
  by_cases h : candN (fun k => (byteY X k).toNat) (8 * l + j % 8) < 3329
  · rw [itT h, decide_eq_true h]; decide
  · rw [itF h, decide_eq_false h]; decide

theorem bsum_chunk (g : Nat → Bool) (n : Nat) :
    bsum g (n + 8) = bsum g n + 2 ^ n * bsum (fun i => g (n + i)) 8 := bsum_add g n 8

/-- `vpmovmskb` of the two lanes: `m₀` in bits 0 to 7 and 8 to 15, `m₁` in bits 16 to 23 and 24 to 31. -/
theorem mask_toNat (X : BitVec 256) :
    (byteMask (maskW X 1 ++ maskW X 0) 32).toNat =
      maskL X 0 + 256 * maskL X 0 + 65536 * maskL X 1 + 16777216 * maskL X 1 := by
  have hbit : ∀ j < 32, (maskW X 1 ++ maskW X 0).getLsbD (8 * j + 7) =
      decide (candN (fun k => (byteY X k).toNat) (8 * (j / 16) + j % 8) < 3329) := fun j hj => by
    rw [BitVec.getLsbD_append]
    by_cases h : j < 16
    · rw [itT (show 8 * j + 7 < 128 by omega), maskW_bit X (by decide) h, Nat.div_eq_of_lt h]
    · rw [itF (show ¬ 8 * j + 7 < 128 by omega), show 8 * j + 7 - 128 = 8 * (j - 16) + 7 by omega,
        maskW_bit X (by decide) (show j - 16 < 16 by omega), show j / 16 = 1 by omega,
        show (j - 16) % 8 = j % 8 by omega]
  have hl : ∀ l, maskL X l < 256 := fun l => bsum_lt _ 8
  rw [byteMask_eq _ (by decide), BitVec.toNat_ofNat]
  generalize hg : (fun i => (maskW X 1 ++ maskW X 0).getLsbD (8 * i + 7)) = g
  have hgj : ∀ j < 32, g j = decide (candN (fun k => (byteY X k).toNat) (8 * (j / 16) + j % 8) < 3329) :=
    fun j hj => by rw [← hg]; exact hbit j hj
  have B : ∀ n < 32, n % 8 = 0 → bsum (fun i => g (n + i)) 8 = maskL X (n / 16) := fun n hn h8 =>
    bsum_congr fun i hi => by rw [hgj _ (by omega), show (n + i) / 16 = n / 16 by omega, show (n + i) % 8 = i by omega]
  have b0 : bsum g 8 = maskL X 0 := by
    rw [← B 0 (by decide) rfl]; exact bsum_congr fun i _ => by rw [Nat.zero_add]
  rw [show (32 : Nat) = 24 + 8 from rfl, bsum_chunk, show (24 : Nat) = 16 + 8 from rfl, bsum_chunk,
    show (16 : Nat) = 8 + 8 from rfl, bsum_chunk, B 8 (by decide) rfl, B 16 (by decide) rfl, B 24 (by decide) rfl, b0]
  have := hl 0; have := hl 1
  simp only [Nat.reduceDiv, Nat.reducePow]
  omega

/-! ## The compaction -/

theorem word_bytes (x : BitVec 128) (i : Nat) : word x i = byte x (2 * i + 1) ++ byte x (2 * i) := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_word, decide_eq_true hm, Bool.true_and, BitVec.getLsbD_append]
  by_cases a : m < 8
  · rw [itT a, byte, BitVec.getLsbD_extractLsb', decide_eq_true a, Bool.true_and]; congr 1; omega
  · rw [itF a, byte, BitVec.getLsbD_extractLsb', decide_eq_true (show m - 8 < 8 by omega), Bool.true_and]
    congr 1; omega

theorem setBits_lt {m : Nat} {c : Nat} (hc : c < (setBits m).length) : (setBits m).getD c 0 < 8 := by
  have hmem : (setBits m).getD c 0 ∈ setBits m := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]; exact List.getElem_mem hc
  unfold setBits at hmem
  exact List.mem_range.mp (List.mem_filter.mp hmem).1

/-- The mask of `m` moves word `(setBits m)[c]` to word `c`. -/
theorem pshufb_idxV (a : BitVec 128) {m c : Nat} (hc : c < (setBits m).length) :
    word (XBinOp.eval .pshufb a (idxV m)) c = word a ((setBits m).getD c 0) := by
  have hs := setBits_lt hc
  have hc8 : c < 8 := Nat.lt_of_lt_of_le hc (by unfold setBits; exact Nat.le_trans (List.length_filter_le _ _) (by simp))
  have hb : ∀ e < 2, byte (XBinOp.eval .pshufb a (idxV m)) (2 * c + e) = byte a (2 * (setBits m).getD c 0 + e) :=
    fun e he => by
      have hi : byte (idxV m) (2 * c + e) = BitVec.ofNat 8 (2 * (setBits m).getD c 0 + e) := by
        rw [idxV, byte_ofBytes' _ (by omega), itT (show (2 * c + e) / 2 < (setBits m).length by omega),
          show (2 * c + e) / 2 = c by omega, show (2 * c + e) % 2 = e by omega]
      rw [XBinOp.eval, byte_ofBytes' _ (by omega)]
      dsimp only
      rw [hi, itF (by simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_true_eq]; omega)]
      congr 1
      simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
      omega
  have h0 := hb 0 (by decide)
  rw [Nat.add_zero, Nat.add_zero] at h0
  rw [word_bytes, word_bytes, hb 1 (by decide), h0]

/-! ## The static -/

open VG.Impl.MlKem.X86_64.Sample4 (tblWords consts) in
theorem tblWords_length : tblWords.length = 780 := by simp [tblWords, consts]

open VG.Impl.MlKem.X86_64.Sample4 (tblWords consts) in
theorem tblWords_idx {m h : Nat} (hm : m < 256) (hh : h < 2) : tblWords.getD (2 * m + h) 0 = idxQ m h := by
  rw [tblWords, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_left (by simp; omega)]
  simp only [List.getElem?_map, List.getElem?_range (show 2 * m + h < 512 by omega), Option.map_some,
    Option.getD_some, show (2 * m + h) / 2 = m by omega, show (2 * m + h) % 2 = h by omega]

open VG.Impl.MlKem.X86_64.Sample4 (tblWords consts) in
theorem tblWords_cst {i : Nat} (hi : i < 12) : tblWords.getD (512 + i) 0 = consts.getD i 0 := by
  rw [tblWords, List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by simp),
    List.getElem?_append_left (by simp [consts]; omega)]
  simp [List.getD_eq_getElem?_getD]

open VG.Impl.MlKem.X86_64.Sample4 (tblWords consts) in
theorem tblWords_cnt {m : Nat} (hm : m < 256) :
    tblWords.getD (524 + m) 0 = BitVec.ofNat 64 (setBits m).length := by
  rw [tblWords, List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by simp [consts]; omega)]
  simp only [List.length_map, List.length_range, consts, List.length_cons, List.length_nil, Nat.reduceAdd,
    show 524 + m - 512 - 12 = m by omega, List.getElem?_map, List.getElem?_range hm, Option.map_some,
    Option.getD_some]

open VG.Impl.MlKem.X86_64.Sample4 (tblWords consts) in
theorem tblWords_idx0 {m : Nat} (hm : m < 256) : tblWords.getD (2 * m) 0 = idxQ m 0 := by
  have := tblWords_idx hm (show 0 < 2 by decide); rwa [Nat.add_zero] at this

theorem idxQ_pair (m : Nat) : idxQ m 1 ++ idxQ m 0 = idxV m := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [idxQ, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 64
  · rw [itT h, decide_eq_true h, Bool.true_and, Nat.mul_zero, Nat.zero_add]
  · rw [itF h, decide_eq_true (show j - 64 < 64 by omega), Bool.true_and]; congr 1; omega

/-! ## The steps -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_vpermq {d a : XReg} {o : BitVec 8}
    (k : ∀ s', LUpd s s' d (fun l => (permQwords (s.ymm a) o).extractLsb' (128 * l) 128) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpermq d a o) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d ((permQwords (s.ymm a) o).extractLsb' 0 128)
      ((permQwords (s.ymm a) o).extractLsb' 128 128)) rfl (k _ (by
    have h := LUpd.setV256 s d ((permQwords (s.ymm a) o).extractLsb' 0 128)
      ((permQwords (s.ymm a) o).extractLsb' 128 128)
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩))

theorem wp_vshift {op : XShiftOp} {d a : XReg} {n : BitVec 8}
    (k : ∀ s', LUpd s s' d (fun l => op.eval (s.lane a l) n) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vshift op .l256 d a n) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (op.eval (s.lane a 0) n) (op.eval (s.lane a 1) n)) rfl (k _ (by
    have h := LUpd.setV256 s d (op.eval (s.lane a 0) n) (op.eval (s.lane a 1) n)
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩))

theorem wp_vpblendw {d a b : XReg} {n : BitVec 8}
    (k : ∀ s', LUpd s s' d (fun l => blendWords (s.lane a l) (s.lane b l) n) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpblendw .l256 d a b n) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (blendWords (s.lane a 0) (s.lane b 0) n) (blendWords (s.lane a 1) (s.lane b 1) n))
    rfl (k _ (by
    have h := LUpd.setV256 s d (blendWords (s.lane a 0) (s.lane b 0) n) (blendWords (s.lane a 1) (s.lane b 1) n)
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩))

theorem wp_vins1 {d a b : XReg}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then s.lane a 0 else s.xmm b) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vinserti128 d a b 1) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (s.lane a 0) (s.xmm b)) rfl (k _ (LUpd.setV256 _ _ _ _))

end

theorem VC.lupd {s s' : State} (h : VC s) {d : XReg} {v : Nat → BitVec 128} (hu : LUpd s s' d v)
    (hd : d = .xmm0 ∨ d = .xmm1 ∨ d = .xmm2 ∨ d = .xmm3) : VC s' := by
  have e : ∀ r, r = XReg.xmm8 ∨ r = .xmm9 ∨ r = .xmm10 → ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r hr l hl => hu.other r (by rcases hd with rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> decide) l hl
  exact ⟨fun l hl => by rw [e _ (by simp) l hl, h.c8 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c9 l hl],
    fun l hl => by rw [e _ (by simp) l hl, h.c10 l hl]⟩

theorem VC.gupd {s s' : State} (h : VC s) {d : Reg} {v : BitVec 64} (hu : GUpd s s' d v) : VC s' :=
  ⟨fun l hl => by rw [hu.lane, h.c8 l hl], fun l hl => by rw [hu.lane, h.c9 l hl],
    fun l hl => by rw [hu.lane, h.c10 l hl]⟩

theorem VC.same {s s' : State} (h : VC s) (hl : ∀ x l, s'.lane x l = s.lane x l) : VC s' :=
  ⟨fun l hl' => by rw [hl, h.c8 l hl'], fun l hl' => by rw [hl, h.c9 l hl'], fun l hl' => by rw [hl, h.c10 l hl']⟩

theorem halves256 (X : BitVec 256) : X.extractLsb' 128 128 ++ X.extractLsb' 0 128 = X := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_append]
  by_cases h : j < 128
  · rw [itT h, BitVec.getLsbD_extractLsb', decide_eq_true h, Bool.true_and, Nat.zero_add]
  · rw [itF h, BitVec.getLsbD_extractLsb', decide_eq_true (show j - 128 < 128 by omega), Bool.true_and]
    exact congrArg _ (by omega)

open VG.Impl.MlKem.X86_64.Sample4 (vcand) in
open VG.Proof.MlKem.X86_64 (ea_at add_ofNat_zero) in
/-- The candidates of the 24 bytes at `rsi` in `ymm0`, and their masks in `eax`. -/
theorem vcand_ok {s : State} (hc : VC s) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 32) :
    WP isa (.block vcand) s fun s' =>
      (s'.gpr .rax).toNat = maskL (s.mem.readW (s.gpr .rsi) 256) 0 + 256 * maskL (s.mem.readW (s.gpr .rsi) 256) 0 +
        65536 * maskL (s.mem.readW (s.gpr .rsi) 256) 1 + 16777216 * maskL (s.mem.readW (s.gpr .rsi) 256) 1 ∧
      (∀ l < 2, s'.lane .xmm0 l = candW (s.mem.readW (s.gpr .rsi) 256) l) ∧ VC s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  generalize hX : s.mem.readW (s.gpr .rsi) 256 = X
  refine wp_vld256 (a := s.gpr .rsi) (by rw [ea_at, add_ofNat_zero]) hin fun s1 u1 =>
    wp_vpermq fun s2 u2 => wp_vbin fun s3 u3 => wp_vshift fun s4 u4 => wp_vpblendw fun s5 u5 =>
    wp_vbin fun s6 u6 => wp_vbin fun s7 u7 => wp_vbin fun s8 u8 => wp_vpmovmskb fun s9 u9 => WP.block_nil ?_
  have c8 : VC s8 := (((((((hc.lupd u1 (.inl rfl)).lupd u2 (.inl rfl)).lupd u3 (.inl rfl)).lupd u4 (.inr (.inl rfl))).lupd
    u5 (.inl rfl)).lupd u6 (.inl rfl)).lupd u7 (.inr (.inl rfl))).lupd u8 (.inr (.inl rfl))
  have y1 : s1.ymm .xmm0 = X := by
    rw [State.ymm_eq, u1.val 1 (by decide), u1.val 0 (by decide), ← hX, Nat.mul_one, Nat.mul_zero, halves256]
  have l2 : ∀ l < 2, s2.lane .xmm0 l = laneP X l := fun l hl => by rw [u2.val l hl, y1, perm_lane X hl]
  have k3 : ∀ l < 2, s2.lane .xmm8 l = shufW l := fun l hl => by
    rw [u2.other _ (by decide) l hl, u1.other _ (by decide) l hl, hc.c8 l hl]
  have l3 : ∀ l < 2, s3.lane .xmm0 l = XBinOp.eval .pshufb (laneP X l) (shufW l) := fun l hl => by
    rw [u3.val l hl, l2 l hl, k3 l hl]; rfl
  have l4 : ∀ l < 2, s4.lane .xmm1 l = XShiftOp.eval .psrlw (XBinOp.eval .pshufb (laneP X l) (shufW l)) 4 :=
    fun l hl => by rw [u4.val l hl, l3 l hl]
  have l5 : ∀ l < 2, s5.lane .xmm0 l = blendWords (XBinOp.eval .pshufb (laneP X l) (shufW l))
      (XShiftOp.eval .psrlw (XBinOp.eval .pshufb (laneP X l) (shufW l)) 4) 0xAA := fun l hl => by
    rw [u5.val l hl, u4.other _ (by decide) l hl, l3 l hl, l4 l hl]
  have k6 : ∀ l < 2, s5.lane .xmm9 l = fffW := fun l hl => by
    rw [u5.other _ (by decide) l hl, u4.other _ (by decide) l hl, u3.other _ (by decide) l hl,
      u2.other _ (by decide) l hl, u1.other _ (by decide) l hl, hc.c9 l hl]
  have l6 : ∀ l < 2, s6.lane .xmm0 l = candW X l := fun l hl => by
    rw [u6.val l hl, l5 l hl, k6 l hl]; rfl
  have k7 : ∀ l < 2, s6.lane .xmm10 l = qW := fun l hl => by
    rw [u6.other _ (by decide) l hl, u5.other _ (by decide) l hl, u4.other _ (by decide) l hl,
      u3.other _ (by decide) l hl, u2.other _ (by decide) l hl, u1.other _ (by decide) l hl, hc.c10 l hl]
  have l7 : ∀ l < 2, s7.lane .xmm1 l = XBinOp.eval .pcmpgtw qW (candW X l) := fun l hl => by
    rw [u7.val l hl, k7 l hl, l6 l hl]; rfl
  have l8 : ∀ l < 2, s8.lane .xmm1 l = maskW X l := fun l hl => by
    rw [u8.val l hl, l7 l hl]; rfl
  have g8 : s8.gpr = s.gpr := by rw [u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  refine ⟨?_, fun l hl => ?_, c8.gupd u9, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [u9.gpr, State.ymm_eq, l8 1 (by decide), l8 0 (by decide), mask_toNat]
  · rw [u9.lane, u8.other _ (by decide) l hl, u7.other _ (by decide) l hl, l6 l hl]
  · rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  · rw [u9.syms, u8.syms, u7.syms, u6.syms, u5.syms, u4.syms, u3.syms, u2.syms, u1.syms]
  · rw [u9.other r hr, g8]

open VG.Proof.MlKem.X86_64 (WP.keep Keep) in
/-- `rdx := 2 (E mod 256)` and `rax := 2 (E >> 24)`, for `E` in `eax`. -/
theorem vidx_ok {s : State} {E : Nat} (hE : (s.gpr .rax).toNat = E) (hE32 : E < 2 ^ 32) :
    WP isa (.block [.mov32 .rdx (.reg .rax), .alu32 .and .rdx (.imm 0xff), .shift32 .shr .rax 24,
      .alu32 .add .rdx (.reg .rdx), .alu32 .add .rax (.reg .rax)]) s fun s' =>
      ((s'.gpr .rdx).toNat = 2 * (E % 256) ∧ (s'.gpr .rax).toNat = 2 * (E / 2 ^ 24) ∧ s'.mem = s.mem ∧
        (∀ x l, s'.lane x l = s.lane x l) ∧ s'.syms = s.syms) ∧ Keep [.rax, .rdx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun
  have h255 : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
  refine ⟨?_, ?_, fun _ _ => rfl, rfl⟩
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_and, hE, show (255 : BitVec 32).toNat = 255 from rfl,
      h255]
    omega
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ushiftRight, hE, Nat.shiftRight_eq_div_pow]
    omega

open VG.Impl.MlKem.X86_64.Sample4 (aJ16 idxE numE tblName tblWords oNum) in
theorem ea_aJ16 (s : State) : s.ea aJ16 = s.gpr .rbp + BitVec.ofNat 64 (2 * (s.gpr .rdi).toNat) := by
  simp only [State.ea, aJ16, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

open VG.Impl.MlKem.X86_64.Sample4 (aJ16 idxE numE tblName tblWords oNum) in
theorem ea_idxE {s : State} {r : Reg} {M : Nat} (h : (s.gpr r).toNat = 2 * M) (hM : M < 256)
    (ht : s.gpr .r11 = s.syms tblName) : (s.ea (idxE r) - s.syms tblName).toNat = 8 * (2 * M) := by
  simp only [State.ea, idxE, ht, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
    VG.Offset.add_sub_cancel_left, BitVec.toNat_mul, h, BitVec.toNat_ofNat]
  omega

open VG.Impl.MlKem.X86_64.Sample4 (aJ16 idxE numE tblName tblWords oNum) in
theorem ea_numE {s : State} {r : Reg} {M : Nat} (h : (s.gpr r).toNat = 2 * M) (hM : M < 256)
    (ht : s.gpr .r11 = s.syms tblName) : (s.ea (numE r) - s.syms tblName).toNat = 8 * (524 + M) := by
  simp only [State.ea, numE, ht, oNum, show BitVec.ofInt 64 ((4192 : Nat) : Int) = BitVec.ofNat 64 4192 from rfl,
    BitVec.add_assoc, VG.Offset.add_sub_cancel_left, BitVec.toNat_add, BitVec.toNat_mul, h, BitVec.toNat_ofNat]
  omega

/-- Lane `l` after the compaction: the candidates less than `q` at its bottom. -/
abbrev compW (X : BitVec 256) (l : Nat) : BitVec 128 := XBinOp.eval .pshufb (candW X l) (idxV (maskL X l))

/-- The number of candidates less than `q` of lane `l`. -/
abbrev cntL (X : BitVec 256) (l : Nat) : Nat := (setBits (maskL X l)).length

theorem cntL_le (X : BitVec 256) (l : Nat) : cntL X l ≤ 8 := by
  unfold cntL setBits; exact Nat.le_trans (List.length_filter_le _ _) (by simp)

section
open VG.Impl.MlKem.X86_64.Sample4 (vputA vputB tblName tblWords idxE numE aJ16)
open VG.Impl.Sha3.X86_64.X4 (vb)

/-- The state after `vputA` from `s`, with the candidates of `X`. -/
structure VPA (X : BitVec 256) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (2 * (s.gpr .rdi).toNat)) (compW X 0)
  rdi : (s'.gpr .rdi).toNat = (s.gpr .rdi).toNat + cntL X 0
  hi : s'.lane .xmm0 1 = compW X 1
  rax : (s'.gpr .rax).toNat = 2 * maskL X 1
  vc : VC s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rdi → s'.gpr r = s.gpr r

/-- The candidates less than `q` of the low lane to `a[j..]`, and `j` advanced by their number. -/
theorem vputA_ok {s : State} (hc : VC s) {X : BitVec 256} (h0 : ∀ l < 2, s.lane .xmm0 l = candW X l)
    (hrax : (s.gpr .rax).toNat = maskL X 0 + 256 * maskL X 0 + 65536 * maskL X 1 + 16777216 * maskL X 1)
    (ht : s.gpr .r11 = s.syms tblName) (hdi : (s.gpr .rdi).toNat < 2 ^ 32)
    (hout0 : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 (2 * (s.gpr .rdi).toNat)) 16) :
    WP isa (.block vputA) s (VPA X s) := by
  have hm0 : maskL X 0 < 256 := bsum_lt _ 8
  have hm1 : maskL X 1 < 256 := bsum_lt _ 8
  have c0 := cntL_le X 0
  rw [show vputA = [.mov32 .rdx (.reg .rax), .alu32 .and .rdx (.imm 0xff), .shift32 .shr .rax 24,
      .alu32 .add .rdx (.reg .rdx), .alu32 .add .rax (.reg .rax)] ++
      [.vmovdquTbl .xmm2 (idxE .rdx) tblName tblWords, .vmovdquTbl .xmm3 (idxE .rax) tblName tblWords,
        .vop (.vinserti128 .xmm2 .xmm2 .xmm3 1), vb .vpshufb .xmm0 .xmm0 .xmm2,
        .vmovdquStore .l128 aJ16 .xmm0, .aluTbl .add .rdi (numE .rdx) tblName tblWords] from rfl,
    WP.block_append_iff]
  refine WP.mono (vidx_ok hrax (by omega)) fun s1 ⟨⟨hdx, hax, hm, hln, hsy⟩, k1⟩ => ?_
  rw [show (maskL X 0 + 256 * maskL X 0 + 65536 * maskL X 1 + 16777216 * maskL X 1) % 256 = maskL X 0 by omega] at hdx
  rw [show (maskL X 0 + 256 * maskL X 0 + 65536 * maskL X 1 + 16777216 * maskL X 1) / 2 ^ 24 = maskL X 1 by omega]
    at hax
  have t1 : s1.gpr .r11 = s1.syms tblName := by rw [k1.gpr (by decide), hsy]; exact ht
  refine wp_vtbl (o := 2 * maskL X 0) t1 (ea_idxE hdx hm0 t1) (by rw [tblWords_length]; omega) fun s2 u2 => ?_
  have t2 : s2.gpr .r11 = s2.syms tblName := by rw [u2.gpr, u2.syms]; exact t1
  refine wp_vtbl (o := 2 * maskL X 1) t2 (ea_idxE (by rw [u2.gpr]; exact hax) hm1 t2) (by rw [tblWords_length]; omega)
    fun s3 u3 => wp_vins1 fun s4 u4 => wp_vbin fun s5 u5 => ?_
  have i0 : s4.lane .xmm2 0 = idxV (maskL X 0) := by
    rw [u4.val 0 (by decide), ite_eq_left rfl, u3.other _ (by decide) 0 (by decide), u2.val 0 (by decide),
      ite_eq_left rfl, tblWords_idx hm0 (by decide), tblWords_idx0 hm0, idxQ_pair]
  have i1 : s4.lane .xmm2 1 = idxV (maskL X 1) := by
    rw [u4.val 1 (by decide), ite_eq_right (by decide), show s3.xmm .xmm3 = s3.lane .xmm3 0 from rfl,
      u3.val 0 (by decide), ite_eq_left rfl, tblWords_idx hm1 (by decide), tblWords_idx0 hm1, idxQ_pair]
  have c5 : ∀ l < 2, s5.lane .xmm0 l = compW X l := fun l hl => by
    rw [u5.val l hl, u4.other _ (by decide) l hl, u3.other _ (by decide) l hl, u2.other _ (by decide) l hl, hln,
      h0 l hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [i0]; rfl
    · rw [i1]; rfl
  have v5 : VC s5 := (((hc.same hln).lupd u2 (.inr (.inr (.inl rfl)))).lupd u3 (.inr (.inr (.inr rfl)))).lupd u4
    (.inr (.inr (.inl rfl))) |>.lupd u5 (.inl rfl)
  have g5 : s5.gpr = s1.gpr := by rw [u5.gpr, u4.gpr, u3.gpr, u2.gpr]
  have y5 : s5.syms = s.syms := by rw [u5.syms, u4.syms, u3.syms, u2.syms, hsy]
  have bp : s5.gpr .rbp = s.gpr .rbp := by rw [g5, k1.gpr (by decide)]
  have di : s5.gpr .rdi = s.gpr .rdi := by rw [g5, k1.gpr (by decide)]
  refine wp_vst128s (a := s.gpr .rbp + BitVec.ofNat 64 (2 * (s.gpr .rdi).toNat)) (by rw [ea_aJ16, bp, di])
    (by rw [u5.wr, u4.wr, u3.wr, u2.wr, k1.2.2]; exact hout0) fun s6 g6 l6 m6 r6 w6 y6 => ?_
  have t6 : s6.gpr .r11 = s6.syms tblName := by rw [g6, y6, g5, y5, k1.gpr (by decide)]; exact ht
  refine wp_addTbl (o := 524 + maskL X 0) t6 (ea_numE (by rw [g6, g5]; exact hdx) hm0 t6)
    (by rw [tblWords_length]; omega) fun s7 u7 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ((v5.same l6).gupd u7), ?_, ?_, ?_, fun r h1 h2 h3 => ?_⟩
  · rw [u7.mem, m6, show s5.xmm .xmm0 = s5.lane .xmm0 0 from rfl, c5 0 (by decide), u5.mem, u4.mem, u3.mem, u2.mem,
      hm]
  · rw [u7.gpr, BitVec.toNat_add, tblWords_cnt hm0, g6, di, BitVec.toNat_ofNat]
    simp only [cntL] at c0 ⊢; omega
  · rw [u7.lane, l6, c5 1 (by decide)]
  · rw [u7.other _ (by decide), g6, g5]; exact hax
  · rw [u7.rd, r6, u5.rd, u4.rd, u3.rd, u2.rd, k1.2.1]
  · rw [u7.wr, w6, u5.wr, u4.wr, u3.wr, u2.wr, k1.2.2]
  · rw [u7.syms, y6, y5]
  · rw [u7.other r h3, g6, g5, k1.gpr (by simp [h1, h2])]

/-- The high lane's to `a[j..]`, `j` advanced by their number and `rsi` by 24. -/
theorem vputB_ok {s t : State} {X : BitVec 256} (hv : VPA X s t) (ht : s.gpr .r11 = s.syms tblName)
    (hdi : (s.gpr .rdi).toNat < 2 ^ 32)
    (hout1 : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 (2 * ((s.gpr .rdi).toNat + cntL X 0))) 16) :
    WP isa (.block vputB) t fun s' =>
      s'.mem = (s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (2 * (s.gpr .rdi).toNat)) (compW X 0)).writeW
        (s.gpr .rbp + BitVec.ofNat 64 (2 * ((s.gpr .rdi).toNat + cntL X 0))) (compW X 1) ∧
      (s'.gpr .rdi).toNat = (s.gpr .rdi).toNat + cntL X 0 + cntL X 1 ∧ s'.gpr .rsi = s.gpr .rsi + 24 ∧ VC s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi → s'.gpr r = s.gpr r := by
  have hm1 : maskL X 1 < 256 := bsum_lt _ 8
  have c0 := cntL_le X 0; have c1 := cntL_le X 1
  have tt : t.gpr .r11 = t.syms tblName := by
    rw [hv.gpr _ (by decide) (by decide) (by decide), hv.syms]; exact ht
  refine wp_vext128 fun s8 u8 => ?_
  refine wp_vst128s (a := s.gpr .rbp + BitVec.ofNat 64 (2 * ((s.gpr .rdi).toNat + cntL X 0)))
    (by rw [ea_aJ16, u8.gpr, hv.rdi, hv.gpr _ (by decide) (by decide) (by decide)])
    (by rw [u8.wr, hv.wr]; exact hout1) fun s9 g9 l9 m9 r9 w9 y9 => ?_
  have t9 : s9.gpr .r11 = s9.syms tblName := by rw [g9, y9, u8.syms, u8.gpr]; exact tt
  refine wp_addTbl (o := 524 + maskL X 1) t9 (ea_numE (by rw [g9, u8.gpr]; exact hv.rax) hm1 t9)
    (by rw [tblWords_length]; omega) fun s10 u10 => wp_addi' fun s11 u11 => WP.block_nil ?_
  have x8 : s8.xmm .xmm0 = compW X 1 := by
    rw [show s8.xmm .xmm0 = s8.lane .xmm0 0 from rfl, u8.val 0 (by decide), ite_eq_left rfl, hv.hi]
  refine ⟨?_, ?_, ?_, (((hv.vc.lupd u8 (.inl rfl)).same l9).gupd u10).gupd u11, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
  · rw [u11.mem, u10.mem, m9, u8.mem, x8, hv.mem]
  · rw [u11.other _ (by decide), u10.gpr, BitVec.toNat_add, tblWords_cnt hm1, g9, u8.gpr, hv.rdi, BitVec.toNat_ofNat]
    simp only [cntL] at c0 c1 ⊢; omega
  · rw [u11.gpr, u10.other _ (by decide), g9, u8.gpr, hv.gpr _ (by decide) (by decide) (by decide)]; rfl
  · rw [u11.rd, u10.rd, r9, u8.rd, hv.rd]
  · rw [u11.wr, u10.wr, w9, u8.wr, hv.wr]
  · rw [u11.syms, u10.syms, y9, u8.syms, hv.syms]
  · rw [u11.other r h4, u10.other r h3, g9, u8.gpr, hv.gpr r h1 h2 h3]

end

end VG.Proof.MlKem.X86_64.S4
