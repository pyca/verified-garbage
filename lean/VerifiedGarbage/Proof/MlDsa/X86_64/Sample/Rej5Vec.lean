module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4Wide
public import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt5
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: its bit-vector lemmas cost more to check than its imports and do not depend on the
-- segment proofs of `Rej5Parse`, which changing them would otherwise re-check

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, eight candidates at once

The vector step of the sampling (`Rej5.vcand`, `Rej5.vput`) on the 24 bytes
at `rsi`: of the 32 bytes it loads, `vpermq` puts bytes 0 to 15 in the low
lane and 8 to 23 in the high one (`perm_lane`); `vpshufb` and `vpand` make
candidate `4 l + i` of `RejNTTPoly` doubleword `i` of lane `l`
(`cand_dword`); `vpsubd` of `q`, whose sign bits are those of the candidates
less than `q`, `vpshufb` and `vpmovmskb` give their masks `m₀`, `m₁` of each
lane (`mask_toNat`); the static's mask of each (`idxD`) moves its
candidates to the bottom of its lane (`pshufb_idxD`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Vec

open VG VG.X86_64
open VG.Impl.MlDsa.X86_64.Sample.Rej5 (setBits4 idxD idxDQ consts tblWords tblName oNum)
open VG.Proof.MlKem.X86_64.S4 (byteY laneP perm_lane byte_laneP bsum bsum_lt bsum_congr bsum_add byteMask_eq
  itT itF byte_ofBytes' halves256 toNat_dword_ofBytes)
open VG.Proof.MlDsa.Sample (rnZ)

/-! ## The constants -/

/-- The `vpshufb` mask of lane `l` (`ymm8`): bytes `4 l + 3 i` to
`4 l + 3 i + 2` to doubleword `i`. -/
def shufD (l : Nat) : BitVec 128 :=
  if l = 0 then 0x800b0a09800807068005040380020100#128 else 0x800f0e0d800c0b0a8009080780060504#128

/-- `2²³ - 1` in each doubleword (`ymm9`). -/
def mskD : BitVec 128 := 0x007fffff007fffff007fffff007fffff#128

/-- `q` in each doubleword (`ymm10`). -/
def qD : BitVec 128 := 0x007fe001007fe001007fe001007fe001#128

/-- The `vpshufb` mask that moves byte `4 i + 3` to byte `i` (`ymm11`). -/
def sgnD : BitVec 128 := 0x8080808080808080808080800f0b0703#128

/-! ## The candidates -/

theorem pshufb_shufD (a : BitVec 128) {l : Nat} (hl : l < 2) :
    XBinOp.eval .pshufb a (shufD l) = ofBytes fun j => if j % 4 < 3 then byte a (4 * l + 3 * (j / 4) + j % 4) else 0 := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
  · simp only [XBinOp.eval, ofBytes, shufD]
    rfl

/-- Lane `l` of the candidates, from the 32 bytes `X`. -/
def candD (X : BitVec 256) (l : Nat) : BitVec 128 :=
  XBinOp.eval .pand (XBinOp.eval .pshufb (laneP X l) (shufD l)) mskD

/-- Candidate `k` of the 24 bytes of `X`: `RejNTTPoly`'s value of bytes `3 k` to `3 k + 2`. -/
abbrev candK (X : BitVec 256) (k : Nat) : Nat := rnZ (byteY X (3 * k)) (byteY X (3 * k + 1)) (byteY X (3 * k + 2))

theorem dword_mskD {i : Nat} (hi : i < 4) : dword mskD i = 0x7fffff#32 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl

theorem dword_qD {i : Nat} (hi : i < 4) : dword qD i = 0x7fe001#32 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl

theorem dword_pand' (a b : BitVec 128) (i : Nat) : dword (XBinOp.eval .pand a b) i = dword a i &&& dword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [XBinOp.eval, getLsbD_dword, BitVec.getLsbD_and]
  cases decide (j < 32) <;> simp

theorem cand_dword (X : BitVec 256) {l i : Nat} (hl : l < 2) (hi : i < 4) :
    (dword (candD X l) i).toNat = candK X (4 * l + i) := by
  rw [candD, dword_pand', dword_mskD hi, BitVec.toNat_and, show (0x7fffff#32).toNat = 2 ^ 23 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, pshufb_shufD _ hl, toNat_dword_ofBytes _ hi]
  simp only [show (4 * i) % 4 < 3 by omega, show (4 * i + 1) % 4 < 3 by omega, show (4 * i + 2) % 4 < 3 by omega,
    show ¬ (4 * i + 3) % 4 < 3 by omega, ↓reduceIte, show (0 : BitVec 8).toNat = 0 from rfl,
    byte_laneP _ (show 4 * l + 3 * (4 * i / 4) + 4 * i % 4 < 16 by omega),
    byte_laneP _ (show 4 * l + 3 * ((4 * i + 1) / 4) + (4 * i + 1) % 4 < 16 by omega),
    byte_laneP _ (show 4 * l + 3 * ((4 * i + 2) / 4) + (4 * i + 2) % 4 < 16 by omega)]
  rw [show 8 * l + (4 * l + 3 * (4 * i / 4) + 4 * i % 4) = 3 * (4 * l + i) by omega,
    show 8 * l + (4 * l + 3 * ((4 * i + 1) / 4) + (4 * i + 1) % 4) = 3 * (4 * l + i) + 1 by omega,
    show 8 * l + (4 * l + 3 * ((4 * i + 2) / 4) + (4 * i + 2) % 4) = 3 * (4 * l + i) + 2 by omega]
  have b0 := (byteY X (3 * (4 * l + i))).isLt
  have b1 := (byteY X (3 * (4 * l + i) + 1)).isLt
  have b2 := (byteY X (3 * (4 * l + i) + 2)).isLt
  simp only [candK, rnZ]
  omega

theorem candK_lt (X : BitVec 256) (k : Nat) : candK X k < 2 ^ 23 := by
  have b0 := (byteY X (3 * k)).isLt
  have b1 := (byteY X (3 * k + 1)).isLt
  have := Nat.mod_lt (byteY X (3 * k + 2)).toNat (show 128 > 0 by decide)
  simp only [candK, rnZ]
  omega

/-! ## The mask -/

/-- The sign bytes of lane `l` after `vpsubd` of `q` and `vpshufb`. -/
def sgnL (X : BitVec 256) (l : Nat) : BitVec 128 := XBinOp.eval .pshufb (XBinOp.eval .psubd (candD X l) qD) sgnD

/-- The mask of the candidates less than `q` of lane `l`. -/
def maskL (X : BitVec 256) (l : Nat) : Nat := bsum (fun i => decide (candK X (4 * l + i) < Spec.MlDsa.q)) 4

theorem dword_psubd (a b : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .psubd a b) i = dword a i - dword b i := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XBinOp.eval]

/-- The sign of `x - q`, for `x < 2²³`. -/
theorem msb_sub_q {x : BitVec 32} (hx : x.toNat < 2 ^ 23) :
    (x - 0x7fe001#32).getLsbD 31 = decide (x.toNat < Spec.MlDsa.q) := by
  rw [show (x - 0x7fe001#32).getLsbD 31 = (x - 0x7fe001#32).msb from (BitVec.msb_eq_getLsbD_last _).symm,
    BitVec.msb_eq_decide, BitVec.toNat_sub, show (0x7fe001#32).toNat = 8380417 from rfl]
  simp only [Spec.MlDsa.q]
  by_cases h : x.toNat < 8380417 <;> simp [h] <;> omega

/-- Byte `i < 4` of `sgnL X l` is byte 3 of doubleword `i`, the others zero. -/
theorem sgnL_bit (X : BitVec 256) {l j : Nat} (hl : l < 2) (hj : j < 16) :
    (sgnL X l).getLsbD (8 * j + 7) = (decide (j < 4) && decide (candK X (4 * l + j) < Spec.MlDsa.q)) := by
  have hs : sgnL X l = ofBytes fun j => if j < 4 then byte (XBinOp.eval .psubd (candD X l) qD) (4 * j + 3) else 0 := by
    simp only [sgnL, XBinOp.eval, ofBytes, sgnD]
    rfl
  rw [hs, getLsbD_ofBytes _ hj (by decide)]
  by_cases h4 : j < 4
  · rw [itT h4]
    have e : (byte (XBinOp.eval .psubd (candD X l) qD) (4 * j + 3)).getLsbD 7 =
        (dword (XBinOp.eval .psubd (candD X l) qD) j).getLsbD 31 := by
      simp only [byte, getLsbD_dword, BitVec.getLsbD_extractLsb', show 7 < 8 from by decide, show 31 < 32 from by decide,
        decide_true, Bool.true_and]
      exact congrArg _ (by omega)
    rw [e, dword_psubd _ _ h4, dword_qD h4, msb_sub_q (by rw [cand_dword X hl h4]; exact candK_lt X _),
      cand_dword X hl h4, decide_eq_true h4, Bool.true_and]
  · rw [itF h4, decide_eq_false h4, Bool.false_and]; rfl

/-- `vpmovmskb` of the two lanes: `m₀` in bits 0 to 3, `m₁` in bits 16 to 19. -/
theorem mask_toNat (X : BitVec 256) :
    (byteMask (sgnL X 1 ++ sgnL X 0) 32).toNat = maskL X 0 + 65536 * maskL X 1 := by
  have hbit : ∀ j < 32, (sgnL X 1 ++ sgnL X 0).getLsbD (8 * j + 7) =
      (decide (j % 16 < 4) && decide (candK X (4 * (j / 16) + j % 16) < Spec.MlDsa.q)) := fun j hj => by
    rw [BitVec.getLsbD_append]
    by_cases h : j < 16
    · rw [itT (show 8 * j + 7 < 128 by omega), sgnL_bit X (by decide) h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    · rw [itF (show ¬ 8 * j + 7 < 128 by omega), show 8 * j + 7 - 128 = 8 * (j - 16) + 7 by omega,
        sgnL_bit X (by decide) (show j - 16 < 16 by omega), show j / 16 = 1 by omega, show j % 16 = j - 16 by omega]
  rw [byteMask_eq _ (by decide), BitVec.toNat_ofNat]
  generalize hg : (fun i => (sgnL X 1 ++ sgnL X 0).getLsbD (8 * i + 7)) = g
  have hgj : ∀ j < 32, g j = (decide (j % 16 < 4) && decide (candK X (4 * (j / 16) + j % 16) < Spec.MlDsa.q)) :=
    fun j hj => by rw [← hg]; exact hbit j hj
  have hz : ∀ n, n % 16 = 4 → n + 12 ≤ 32 → bsum (fun i => g (n + i)) 12 = 0 := fun n hn hn' => by
    rw [bsum_congr (g := fun _ => false) fun i hi => by
      rw [hgj _ (by omega), decide_eq_false (show ¬ (n + i) % 16 < 4 by omega), Bool.false_and]]
    clear hgj hg hn hn'
    induction (12 : Nat) with
    | zero => rfl
    | succ k ih => rw [bsum, ih]; simp
  have hm : ∀ n, n % 16 = 0 → n < 32 → bsum (fun i => g (n + i)) 4 = maskL X (n / 16) := fun n hn hn' =>
    bsum_congr fun i hi => by
      rw [hgj _ (by omega), decide_eq_true (show (n + i) % 16 < 4 by omega), Bool.true_and,
        show (n + i) / 16 = n / 16 by omega, show (n + i) % 16 = i by omega]
  have b0 : bsum g 4 = maskL X 0 := by
    rw [← hm 0 (by decide) (by decide)]; exact bsum_congr fun i _ => by rw [Nat.zero_add]
  have e1 := bsum_add g 4 12
  have e2 := bsum_add g 16 4
  have e3 := bsum_add g 20 12
  rw [show (4 : Nat) + 12 = 16 from rfl, b0, hz 4 (by decide) (by decide)] at e1
  rw [show (16 : Nat) + 4 = 20 from rfl, e1, hm 16 (by decide) (by decide)] at e2
  rw [show (20 : Nat) + 12 = 32 from rfl, e2, hz 20 (by decide) (by decide)] at e3
  have l0 : maskL X 0 < 16 := bsum_lt _ 4
  have l1 : maskL X 1 < 16 := bsum_lt _ 4
  simp only [Nat.reduceDiv] at e3
  rw [e3, Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## The compaction -/

theorem setBits4_lt {m c : Nat} (hc : c < (setBits4 m).length) : (setBits4 m).getD c 0 < 4 := by
  have hmem : (setBits4 m).getD c 0 ∈ setBits4 m := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]; exact List.getElem_mem hc
  unfold setBits4 at hmem
  exact List.mem_range.mp (List.mem_filter.mp hmem).1

theorem setBits4_length_le (m : Nat) : (setBits4 m).length ≤ 4 := by
  unfold setBits4; exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- The mask of `m` moves doubleword `(setBits4 m)[c]` to doubleword `c`. -/
theorem pshufb_idxD (a : BitVec 128) {m c : Nat} (hc : c < (setBits4 m).length) :
    dword (XBinOp.eval .pshufb a (idxD m)) c = dword a ((setBits4 m).getD c 0) := by
  have hs := setBits4_lt hc
  have hc4 : c < 4 := Nat.lt_of_lt_of_le hc (setBits4_length_le m)
  have hb : ∀ e < 4, byte (XBinOp.eval .pshufb a (idxD m)) (4 * c + e) = byte a (4 * (setBits4 m).getD c 0 + e) :=
    fun e he => by
      have hi : byte (idxD m) (4 * c + e) = BitVec.ofNat 8 (4 * (setBits4 m).getD c 0 + e) := by
        rw [idxD, byte_ofBytes' _ (by omega), itT (show (4 * c + e) / 4 < (setBits4 m).length by omega),
          show (4 * c + e) / 4 = c by omega, show (4 * c + e) % 4 = e by omega]
      rw [XBinOp.eval, byte_ofBytes' _ (by omega)]
      dsimp only
      rw [hi, itF (by simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_true_eq]; omega)]
      congr 1
      simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
      omega
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_dword, getLsbD_dword, decide_eq_true hj, Bool.true_and, Bool.true_and]
  have e1 : 32 * c + j = 8 * (4 * c + j / 8) + j % 8 := by omega
  have e2 : 32 * (setBits4 m).getD c 0 + j = 8 * (4 * (setBits4 m).getD c 0 + j / 8) + j % 8 := by omega
  have g1 : ∀ x : BitVec 128, ∀ k, k < 16 → x.getLsbD (8 * k + j % 8) = (byte x k).getLsbD (j % 8) := fun x k hk => by
    simp only [byte, BitVec.getLsbD_extractLsb', show j % 8 < 8 by omega, decide_true, Bool.true_and]
  rw [e1, e2, g1 _ _ (by omega), g1 _ _ (by omega), hb _ (by omega)]

/-! ## The static -/

theorem tblWords_length : tblWords.length = 64 := by simp [tblWords, consts]

theorem tblWords_idx {m h : Nat} (hm : m < 16) (hh : h < 2) : tblWords.getD (2 * m + h) 0 = idxDQ m h := by
  rw [tblWords, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_left (by simp; omega)]
  simp only [List.getElem?_map, List.getElem?_range (show 2 * m + h < 32 by omega), Option.map_some,
    Option.getD_some, show (2 * m + h) / 2 = m by omega, show (2 * m + h) % 2 = h by omega]

theorem tblWords_idx0 {m : Nat} (hm : m < 16) : tblWords.getD (2 * m) 0 = idxDQ m 0 := by
  have := tblWords_idx hm (show 0 < 2 by decide); rwa [Nat.add_zero] at this

theorem tblWords_cst {i : Nat} (hi : i < 16) : tblWords.getD (32 + i) 0 = consts.getD i 0 := by
  rw [tblWords, List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by simp),
    List.getElem?_append_left (by simp [consts]; omega)]
  simp [List.getD_eq_getElem?_getD]

theorem tblWords_cnt {m : Nat} (hm : m < 16) :
    tblWords.getD (48 + m) 0 = BitVec.ofNat 64 (setBits4 m).length := by
  rw [tblWords, List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by simp [consts]; omega)]
  simp only [List.length_map, List.length_range, consts, List.length_cons, List.length_nil, Nat.reduceAdd,
    show 48 + m - 32 - 16 = m by omega, List.getElem?_map, List.getElem?_range hm, Option.map_some,
    Option.getD_some]

theorem tblWords_cst' {n : Nat} (h1 : 32 ≤ n) (h2 : n < 48) : tblWords.getD n 0 = consts.getD (n - 32) 0 := by
  have := tblWords_cst (i := n - 32) (by omega); rwa [show 32 + (n - 32) = n by omega] at this

theorem idxDQ_pair (m : Nat) : idxDQ m 1 ++ idxDQ m 0 = idxD m := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [idxDQ, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 64
  · rw [itT h, decide_eq_true h, Bool.true_and, Nat.mul_zero, Nat.zero_add]
  · rw [itF h, decide_eq_true (show j - 64 < 64 by omega), Bool.true_and]; congr 1; omega

/-- The constants of the static, as the lanes of `ymm8` to `ymm11`. -/
theorem cst_vals :
    (consts.getD 1 0 ++ consts.getD 0 0 = shufD 0 ∧ consts.getD 3 0 ++ consts.getD 2 0 = shufD 1) ∧
    (consts.getD 5 0 ++ consts.getD 4 0 = mskD ∧ consts.getD 7 0 ++ consts.getD 6 0 = mskD) ∧
    (consts.getD 9 0 ++ consts.getD 8 0 = qD ∧ consts.getD 11 0 ++ consts.getD 10 0 = qD) ∧
    (consts.getD 13 0 ++ consts.getD 12 0 = sgnD ∧ consts.getD 15 0 ++ consts.getD 14 0 = sgnD) := by
  decide

/-! ## The steps -/

open VG.Proof.MlKem.X86_64.S4 (LUpd GUpd wp_vbin wp_vld256 wp_vpermq wp_vpmovmskb wp_vtbl wp_addTbl wp_vins1
  wp_vext128 wp_vst128s wp_addi')
open VG.Impl.Sha3.X86_64.X4 (vb)

/-- The constants of the vector code in `ymm8` to `ymm11`. -/
structure VC (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = shufD l
  c9 : ∀ l < 2, s.lane .xmm9 l = mskD
  c10 : ∀ l < 2, s.lane .xmm10 l = qD
  c11 : ∀ l < 2, s.lane .xmm11 l = sgnD

theorem VC.lupd {s s' : State} (h : VC s) {d : XReg} {v : Nat → BitVec 128} (hu : LUpd s s' d v)
    (hd : d = .xmm0 ∨ d = .xmm1 ∨ d = .xmm2 ∨ d = .xmm3) : VC s' := by
  have e : ∀ r, r = XReg.xmm8 ∨ r = .xmm9 ∨ r = .xmm10 ∨ r = .xmm11 → ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r hr l hl => hu.other r (by rcases hd with rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl <;> decide) l hl
  exact ⟨fun l hl => by rw [e _ (by simp) l hl, h.c8 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c9 l hl],
    fun l hl => by rw [e _ (by simp) l hl, h.c10 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c11 l hl]⟩

theorem VC.gupd {s s' : State} (h : VC s) {d : Reg} {v : BitVec 64} (hu : GUpd s s' d v) : VC s' :=
  ⟨fun l hl => by rw [hu.lane, h.c8 l hl], fun l hl => by rw [hu.lane, h.c9 l hl],
    fun l hl => by rw [hu.lane, h.c10 l hl], fun l hl => by rw [hu.lane, h.c11 l hl]⟩

theorem VC.same {s s' : State} (h : VC s) (hl : ∀ x l, s'.lane x l = s.lane x l) : VC s' :=
  ⟨fun l hl' => by rw [hl, h.c8 l hl'], fun l hl' => by rw [hl, h.c9 l hl'], fun l hl' => by rw [hl, h.c10 l hl'],
    fun l hl' => by rw [hl, h.c11 l hl']⟩

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (vcand) in
open VG.Proof.MlKem.X86_64 (ea_at add_ofNat_zero) in
/-- The candidates of the 24 bytes at `rsi` in `ymm0`, and their masks in `eax`. -/
theorem vcand_ok {s : State} (hc : VC s) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 32) :
    WP isa (.block vcand) s fun s' =>
      (s'.gpr .rax).toNat = maskL (s.mem.readW (s.gpr .rsi) 256) 0 + 65536 * maskL (s.mem.readW (s.gpr .rsi) 256) 1 ∧
      (∀ l < 2, s'.lane .xmm0 l = candD (s.mem.readW (s.gpr .rsi) 256) l) ∧ VC s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  generalize hX : s.mem.readW (s.gpr .rsi) 256 = X
  refine wp_vld256 (a := s.gpr .rsi) (by rw [ea_at, add_ofNat_zero]) hin fun s1 u1 =>
    wp_vpermq fun s2 u2 => wp_vbin fun s3 u3 => wp_vbin fun s4 u4 => wp_vbin fun s5 u5 =>
    wp_vbin fun s6 u6 => wp_vpmovmskb fun s7 u7 => WP.block_nil ?_
  have c2 : VC s2 := (hc.lupd u1 (.inl rfl)).lupd u2 (.inl rfl)
  have c3 : VC s3 := c2.lupd u3 (.inl rfl)
  have c4 : VC s4 := c3.lupd u4 (.inl rfl)
  have c5 : VC s5 := c4.lupd u5 (.inr (.inl rfl))
  have c6 : VC s6 := c5.lupd u6 (.inr (.inl rfl))
  have y1 : s1.ymm .xmm0 = X := by
    rw [State.ymm_eq, u1.val 1 (by decide), u1.val 0 (by decide), ← hX, Nat.mul_one, Nat.mul_zero, halves256]
  have l2 : ∀ l < 2, s2.lane .xmm0 l = laneP X l := fun l hl => by rw [u2.val l hl, y1, perm_lane X hl]
  have l4 : ∀ l < 2, s4.lane .xmm0 l = candD X l := fun l hl => by
    rw [u4.val l hl, u3.val l hl, l2 l hl, c2.c8 l hl, c3.c9 l hl]
    rfl
  have l6 : ∀ l < 2, s6.lane .xmm1 l = sgnL X l := fun l hl => by
    rw [u6.val l hl, u5.val l hl, l4 l hl, c4.c10 l hl, c5.c11 l hl]
    rfl
  have g6 : s6.gpr = s.gpr := by rw [u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  refine ⟨?_, fun l hl => ?_, c6.gupd u7, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [u7.gpr, State.ymm_eq, l6 1 (by decide), l6 0 (by decide), mask_toNat]
  · rw [u7.lane, u6.other _ (by decide) l hl, u5.other _ (by decide) l hl, l4 l hl]
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  · rw [u7.syms, u6.syms, u5.syms, u4.syms, u3.syms, u2.syms, u1.syms]
  · rw [u7.other r hr, g6]

open VG.Proof.MlKem.X86_64 (WP.keep Keep) in
/-- `rdx := 2 (E mod 16)` and `rax := 2 (E >> 16)`, for `E` in `eax`. -/
theorem vidx_ok {s : State} {E : Nat} (hE : (s.gpr .rax).toNat = E) (hE32 : E < 2 ^ 32) :
    WP isa (.block [.mov32 .rdx (.reg .rax), .alu32 .and .rdx (.imm 0xf), .shift32 .shr .rax 16,
      .alu32 .add .rdx (.reg .rdx), .alu32 .add .rax (.reg .rax)]) s fun s' =>
      ((s'.gpr .rdx).toNat = 2 * (E % 16) ∧ (s'.gpr .rax).toNat = 2 * (E / 2 ^ 16) ∧ s'.mem = s.mem ∧
        (∀ x l, s'.lane x l = s.lane x l) ∧ s'.syms = s.syms) ∧ Keep [.rax, .rdx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun
  have h15 : ∀ x : Nat, x &&& 15 = x % 16 := fun x => Nat.and_two_pow_sub_one_eq_mod x 4
  refine ⟨?_, ?_, fun _ _ => rfl, rfl⟩
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_and, hE, show (15 : BitVec 32).toNat = 15 from rfl,
      h15]
    omega
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ushiftRight, hE, Nat.shiftRight_eq_div_pow]
    omega

open VG.Impl.MlKem.X86_64.Sample4 (idxE) in
theorem ea_idxE {s : State} {r : Reg} {M : Nat} (h : (s.gpr r).toNat = 2 * M) (hM : M < 16)
    (ht : s.gpr .r11 = s.syms tblName) : (s.ea (idxE r) - s.syms tblName).toNat = 8 * (2 * M) := by
  simp only [State.ea, idxE, ht, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
    VG.Offset.add_sub_cancel_left, BitVec.toNat_mul, h, BitVec.toNat_ofNat]
  omega

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (numE) in
theorem ea_numE {s : State} {r : Reg} {M : Nat} (h : (s.gpr r).toNat = 2 * M) (hM : M < 16)
    (ht : s.gpr .r11 = s.syms tblName) : (s.ea (numE r) - s.syms tblName).toNat = 8 * (48 + M) := by
  simp only [State.ea, numE, ht, oNum, show BitVec.ofInt 64 ((384 : Nat) : Int) = BitVec.ofNat 64 384 from rfl,
    BitVec.add_assoc, VG.Offset.add_sub_cancel_left, BitVec.toNat_add, BitVec.toNat_mul, h, BitVec.toNat_ofNat]
  omega

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (aJ) in
theorem ea_aJ (s : State) : s.ea aJ = s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat) := by
  simp only [State.ea, aJ, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- Lane `l` after the compaction: the candidates less than `q` at its bottom. -/
abbrev compD (X : BitVec 256) (l : Nat) : BitVec 128 := XBinOp.eval .pshufb (candD X l) (idxD (maskL X l))

/-- The number of candidates less than `q` of lane `l`. -/
abbrev cntL (X : BitVec 256) (l : Nat) : Nat := (setBits4 (maskL X l)).length

theorem cntL_le (X : BitVec 256) (l : Nat) : cntL X l ≤ 4 := setBits4_length_le _

section
open VG.Impl.MlDsa.X86_64.Sample.Rej5 (vput vputA vputB numE aJ)
open VG.Impl.MlKem.X86_64.Sample4 (idxE)

/-- The state after `vputA` from `s`, with the candidates of `X`. -/
structure VPA (X : BitVec 256) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) (compD X 0)
  rdi : (s'.gpr .rdi).toNat = (s.gpr .rdi).toNat + cntL X 0
  hi : s'.lane .xmm0 1 = compD X 1
  rax : (s'.gpr .rax).toNat = 2 * maskL X 1
  vc : VC s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rdi → s'.gpr r = s.gpr r

/-- The candidates less than `q` of the low lane to `a[j..]`, and `j` advanced by their number. -/
theorem vputA_ok {s : State} (hc : VC s) {X : BitVec 256} (h0 : ∀ l < 2, s.lane .xmm0 l = candD X l)
    (hrax : (s.gpr .rax).toNat = maskL X 0 + 65536 * maskL X 1)
    (ht : s.gpr .r11 = s.syms tblName) (hdi : (s.gpr .rdi).toNat < 2 ^ 32)
    (hout0 : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) 16) :
    WP isa (.block vputA) s (VPA X s) := by
  have hm0 : maskL X 0 < 16 := bsum_lt _ 4
  have hm1 : maskL X 1 < 16 := bsum_lt _ 4
  have c0 := cntL_le X 0
  rw [show vputA = [.mov32 .rdx (.reg .rax), .alu32 .and .rdx (.imm 0xf), .shift32 .shr .rax 16,
      .alu32 .add .rdx (.reg .rdx), .alu32 .add .rax (.reg .rax)] ++
      [.vmovdquTbl .xmm2 (idxE .rdx) tblName tblWords, .vmovdquTbl .xmm3 (idxE .rax) tblName tblWords,
        .vop (.vinserti128 .xmm2 .xmm2 .xmm3 1), vb .vpshufb .xmm0 .xmm0 .xmm2,
        .vmovdquStore .l128 aJ .xmm0, .aluTbl .add .rdi (numE .rdx) tblName tblWords] from rfl,
    WP.block_append_iff]
  refine WP.mono (vidx_ok hrax (by omega)) fun s1 ⟨⟨hdx, hax, hm, hln, hsy⟩, k1⟩ => ?_
  rw [show (maskL X 0 + 65536 * maskL X 1) % 16 = maskL X 0 by omega] at hdx
  rw [show (maskL X 0 + 65536 * maskL X 1) / 2 ^ 16 = maskL X 1 by omega] at hax
  have t1 : s1.gpr .r11 = s1.syms tblName := by rw [k1.gpr (by decide), hsy]; exact ht
  refine wp_vtbl (o := 2 * maskL X 0) t1 (ea_idxE hdx hm0 t1) (by rw [tblWords_length]; omega) fun s2 u2 => ?_
  have t2 : s2.gpr .r11 = s2.syms tblName := by rw [u2.gpr, u2.syms]; exact t1
  refine wp_vtbl (o := 2 * maskL X 1) t2 (ea_idxE (by rw [u2.gpr]; exact hax) hm1 t2) (by rw [tblWords_length]; omega)
    fun s3 u3 => wp_vins1 fun s4 u4 => wp_vbin fun s5 u5 => ?_
  have i0 : s4.lane .xmm2 0 = idxD (maskL X 0) := by
    rw [u4.val 0 (by decide), ite_eq_left rfl, u3.other _ (by decide) 0 (by decide), u2.val 0 (by decide),
      ite_eq_left rfl, tblWords_idx hm0 (by decide), tblWords_idx0 hm0, idxDQ_pair]
  have i1 : s4.lane .xmm2 1 = idxD (maskL X 1) := by
    rw [u4.val 1 (by decide), ite_eq_right (by decide), show s3.xmm .xmm3 = s3.lane .xmm3 0 from rfl,
      u3.val 0 (by decide), ite_eq_left rfl, tblWords_idx hm1 (by decide), tblWords_idx0 hm1, idxDQ_pair]
  have c5 : ∀ l < 2, s5.lane .xmm0 l = compD X l := fun l hl => by
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
  refine wp_vst128s (a := s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) (by rw [ea_aJ, bp, di])
    (by rw [u5.wr, u4.wr, u3.wr, u2.wr, k1.2.2]; exact hout0) fun s6 g6 l6 m6 r6 w6 y6 => ?_
  have t6 : s6.gpr .r11 = s6.syms tblName := by rw [g6, y6, g5, y5, k1.gpr (by decide)]; exact ht
  refine wp_addTbl (o := 48 + maskL X 0) t6 (ea_numE (by rw [g6, g5]; exact hdx) hm0 t6)
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
    (hout1 : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 (4 * ((s.gpr .rdi).toNat + cntL X 0))) 16) :
    WP isa (.block vputB) t fun s' =>
      s'.mem = (s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) (compD X 0)).writeW
        (s.gpr .rbp + BitVec.ofNat 64 (4 * ((s.gpr .rdi).toNat + cntL X 0))) (compD X 1) ∧
      (s'.gpr .rdi).toNat = (s.gpr .rdi).toNat + cntL X 0 + cntL X 1 ∧ s'.gpr .rsi = s.gpr .rsi + 24 ∧ VC s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi → s'.gpr r = s.gpr r := by
  have hm1 : maskL X 1 < 16 := bsum_lt _ 4
  have c0 := cntL_le X 0; have c1 := cntL_le X 1
  have tt : t.gpr .r11 = t.syms tblName := by
    rw [hv.gpr _ (by decide) (by decide) (by decide), hv.syms]; exact ht
  refine wp_vext128 fun s8 u8 => ?_
  refine wp_vst128s (a := s.gpr .rbp + BitVec.ofNat 64 (4 * ((s.gpr .rdi).toNat + cntL X 0)))
    (by rw [ea_aJ, u8.gpr, hv.rdi, hv.gpr _ (by decide) (by decide) (by decide)])
    (by rw [u8.wr, hv.wr]; exact hout1) fun s9 g9 l9 m9 r9 w9 y9 => ?_
  have t9 : s9.gpr .r11 = s9.syms tblName := by rw [g9, y9, u8.syms, u8.gpr]; exact tt
  have hax : (s9.gpr .rax).toNat = 2 * maskL X 1 := by rw [g9, u8.gpr]; exact hv.rax
  refine wp_addTbl (o := 48 + maskL X 1) t9 (ea_numE hax hm1 t9)
    (by rw [tblWords_length]; omega) fun s10 u10 => wp_addi' fun s11 u11 => WP.block_nil ?_
  have x8 : s8.xmm .xmm0 = compD X 1 := by
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

/-- The candidates less than `q` of each lane to `a[j..]` in turn, `j` advanced by their number and `rsi` by 24. -/
theorem vput_ok {s : State} (hc : VC s) {X : BitVec 256} (h0 : ∀ l < 2, s.lane .xmm0 l = candD X l)
    (hrax : (s.gpr .rax).toNat = maskL X 0 + 65536 * maskL X 1)
    (ht : s.gpr .r11 = s.syms tblName) (hdi : (s.gpr .rdi).toNat < 2 ^ 32)
    (hout0 : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) 16)
    (hout1 : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 (4 * ((s.gpr .rdi).toNat + cntL X 0))) 16) :
    WP isa (.block vput) s fun s' =>
      s'.mem = (s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) (compD X 0)).writeW
        (s.gpr .rbp + BitVec.ofNat 64 (4 * ((s.gpr .rdi).toNat + cntL X 0))) (compD X 1) ∧
      (s'.gpr .rdi).toNat = (s.gpr .rdi).toNat + cntL X 0 + cntL X 1 ∧ s'.gpr .rsi = s.gpr .rsi + 24 ∧ VC s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi → s'.gpr r = s.gpr r := by
  rw [show vput = vputA ++ vputB from rfl, WP.block_append_iff]
  exact WP.mono (vputA_ok hc h0 hrax ht hdi hout0) fun t hv => vputB_ok hv ht hdi hout1

end

/-! ## The coefficients -/

section
open VG.Proof.MlDsa.Sample (rnStep Stored coeffAt_eq coeffAddr zw zw_toNat)
open VG.Spec.MlDsa (Zq)

/-- The value of candidate `k` of the bytes `g`. -/
abbrev candG (g : Nat → Byte) (k : Nat) : Nat := rnZ (g (3 * k)) (g (3 * k + 1)) (g (3 * k + 2))

/-- The coefficients that candidates `4 l` to `4 l + 3` of the bytes `g` add. -/
def accG (g : Nat → Byte) (l : Nat) : List Zq :=
  ((List.range 4).filter fun i => decide (candG g (4 * l + i) < Spec.MlDsa.q)).map
    fun i => Fin.ofNat Spec.MlDsa.q (candG g (4 * l + i))

/-- What one iteration adds, with room for it. -/
abbrev addG (g : Nat → Byte) (k : Nat) : List Zq :=
  if candG g k < Spec.MlDsa.q then [Fin.ofNat Spec.MlDsa.q (candG g k)] else []

theorem rnStep_room {a : List Zq} (h : a.length < Spec.MlDsa.n) (g : Nat → Byte) (k : Nat) :
    rnStep a (g (3 * k)) (g (3 * k + 1)) (g (3 * k + 2)) = a ++ addG g k := by
  unfold rnStep addG; rw [itT h]; split <;> simp

theorem addG_length (g : Nat → Byte) (k : Nat) : (addG g k).length ≤ 1 := by
  unfold addG; split <;> simp

/-- `k` iterations on the bytes `g`, from `a`. -/
def stepsG (a : List Zq) (g : Nat → Byte) : Nat → List Zq
  | 0 => a
  | k + 1 => rnStep (stepsG a g k) (g (3 * k)) (g (3 * k + 1)) (g (3 * k + 2))

theorem filter_map4 (p : Nat → Bool) (f : Nat → Zq) :
    ((List.range 4).filter p).map f = (if p 0 then [f 0] else []) ++ (if p 1 then [f 1] else []) ++
      (if p 2 then [f 2] else []) ++ (if p 3 then [f 3] else []) := by
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.filter_cons, List.filter_nil]
  cases p 0 <;> cases p 1 <;> cases p 2 <;> cases p 3 <;> rfl

theorem accG_eq (g : Nat → Byte) (l : Nat) :
    accG g l = addG g (4 * l) ++ addG g (4 * l + 1) ++ addG g (4 * l + 2) ++ addG g (4 * l + 3) := by
  rw [accG, filter_map4]
  simp only [addG, decide_eq_true_eq, Nat.add_zero]

/-- Eight iterations with room for eight coefficients add the candidates
less than `q` of each half. -/
theorem stepsG_eight {a : List Zq} (h : a.length + 8 ≤ Spec.MlDsa.n) (g : Nat → Byte) :
    stepsG a g 8 = a ++ accG g 0 ++ accG g 1 := by
  have hk : ∀ k ≤ 8, stepsG a g k = a ++ (List.range k).flatMap (addG g) ∧
      (stepsG a g k).length ≤ a.length + k := by
    intro k
    induction k with
    | zero => intro _; simp [stepsG]
    | succ k ih =>
      intro hk8
      obtain ⟨e, l⟩ := ih (by omega)
      rw [stepsG, rnStep_room (by omega), e, List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.append_assoc]
      refine ⟨rfl, ?_⟩
      rw [List.length_append, List.length_append]
      have := addG_length g k
      rw [e, List.length_append] at l
      omega
  rw [(hk 8 (by decide)).1, accG_eq, accG_eq]
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Nat.mul_zero, Nat.zero_add, Nat.mul_one, List.append_assoc]

theorem setBits4_bsum (f : Nat → Bool) : setBits4 (bsum f 4) = (List.range 4).filter f := by
  unfold setBits4
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;> cases h3 : f 3 <;>
    simp [bsum, h0, h1, h2, h3]

/-- The coefficients `L ++ A` are stored after a write of four coefficients
`V` at `a[|L|]`, whose first `|A|` are `A`. -/
theorem stored_write4 {m : Mem} {p : Addr} {L A : List Zq} (h : Stored m p L)
    (hl : L.length + 4 ≤ 256) (hA : A.length ≤ 4) (V : BitVec 128)
    (hV : ∀ i < A.length, (dword V i).toNat = (A.getD i 0).val) :
    Stored (m.writeW (coeffAddr p L.length) V) p (L ++ A) := by
  intro k hk
  rw [List.length_append] at hk
  rw [coeffAt_eq]
  by_cases hkL : k < L.length
  · have := readW_writeW_off m p V (d := 4 * k) (e := 4 * L.length) (n := 4) (by omega) (by omega) (by omega)
    rw [this, show (L ++ A).getD k 0 = L.getD k 0 by simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hkL]]
    exact h k hkL
  · have e := readW_writeW_inside m (coeffAddr p L.length) V (k := 4 * (k - L.length)) (n := 4) (by omega) (by decide)
    rw [coeffAddr, Offset.add_add, show 4 * L.length + 4 * (k - L.length) = 4 * k by omega] at e
    rw [e, show (L ++ A).getD k 0 = A.getD (k - L.length) 0 by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show L.length ≤ k by omega)]]
    apply BitVec.eq_of_toNat_eq
    rw [zw_toNat, show 8 * (4 * (k - L.length)) = 32 * (k - L.length) by omega, ← dword_eq, hV _ (by omega)]

/-- The candidates of lane `l` of `X` are those of the bytes `g`. -/
abbrev CandOf (X : BitVec 256) (g : Nat → Byte) (l : Nat) : Prop := ∀ i < 4, candK X (4 * l + i) = candG g (4 * l + i)

theorem cntL_eq {X : BitVec 256} {g : Nat → Byte} {l : Nat} (hc : CandOf X g l) : cntL X l = (accG g l).length := by
  rw [cntL, maskL, setBits4_bsum, accG, List.length_map]
  congr 1
  apply List.filter_congr
  intro i hi
  rw [hc i (List.mem_range.mp hi)]

/-- The doublewords of a lane after the compaction are its coefficients. -/
theorem comp_dwords {X : BitVec 256} {g : Nat → Byte} {l : Nat} (hl : l < 2) (hc : CandOf X g l) :
    ∀ i < (accG g l).length, (dword (compD X l) i).toNat = ((accG g l).getD i 0).val := by
  intro i hi
  have hi' : i < (setBits4 (maskL X l)).length := by rw [← cntL, cntL_eq hc]; exact hi
  have hs := setBits4_lt hi'
  have hmem : (setBits4 (maskL X l)).getD i 0 ∈ setBits4 (maskL X l) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; exact List.getElem_mem hi'
  have hf : (setBits4 (maskL X l)) = (List.range 4).filter fun i => decide (candG g (4 * l + i) < Spec.MlDsa.q) := by
    rw [maskL, setBits4_bsum]
    apply List.filter_congr
    intro j hj
    rw [hc j (List.mem_range.mp hj)]
  have hq : candG g (4 * l + (setBits4 (maskL X l)).getD i 0) < Spec.MlDsa.q := by
    have hm' := hmem
    generalize (setBits4 (maskL X l)).getD i 0 = x at hm' ⊢
    rw [hf, List.mem_filter, decide_eq_true_eq] at hm'
    exact hm'.2
  rw [compD, pshufb_idxD _ hi', cand_dword X hl hs, hc _ hs]
  simp only [accG]
  rw [← hf]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi', Option.map_some,
    Option.getD_some, Fin.val_ofNat]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some] at hq
  exact (Nat.mod_eq_of_lt hq).symm

end

end VG.Proof.MlDsa.X86_64.Rej4.Vec
