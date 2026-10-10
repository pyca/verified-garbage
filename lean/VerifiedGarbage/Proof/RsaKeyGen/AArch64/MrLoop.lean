import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
import VerifiedGarbage.Proof.RsaKeyGen.Bits

/-!
# A candidate on AArch64: Miller–Rabin's exponentiation loops

`BitInv`: after `t` bits of word `k − 1` of `c` (the words from the top),
`y R mod c` and the flag for the `64 (w − k) + t` bits from the top
(`mrPow`, `mrPre`), the word shifted left by `t` in `kV`. `mrBits_ok`: the
inner loop over the word's bits, 64 but 63 of the last; `mrExpLoop_ok`: the
words.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- What the exponentiation changes. -/
def expRanges (w : Nat) : List (Nat × Nat) := bitRanges w ++ [(8 * kWords, 8)]

theorem expRanges_mut (w : Nat) : ∀ r ∈ expRanges w, KMut r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact bitRanges_mut w r hr
  · rw [List.mem_singleton.mp hr]; exact KMut.hdr (by decide)

/-- Disjointness of a range from each of the ranges of the exponentiation. -/
macro "ex_disj" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, expRanges, bitRanges,
    List.cons_append, List.nil_append, slot, hdrBytes, aN, aAcc, aTmp, aY, aXm, aB, aR1, aRm1, kG, kFlag, kPlen,
    kV, kT0, sCnt, kBits, kT2, kWords, kT1, sFn, sMinv]
  and_intros <;> omega_arith))

/-- `MrCtx` across changes within `expRanges`. -/
theorem MrCtx.of_exp {s t : State} {B : Addr} {Z w c bm : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w c bm) (hf : Frm B rs s.mem t.mem) (hs : ∀ r ∈ rs, r ∈ expRanges w)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : MrCtx t B Z w c bm :=
  hc.of_frm (hf.mono hs) (expRanges_mut w) k hr (by ex_disj) (by ex_disj) (by ex_disj) (by ex_disj) (by ex_disj)

theorem expRanges_hdr (w : Nat) {i : Nat} (hi : i = kWords ∨ i = kV ∨ i = kBits ∨ i = kFlag) :
    (8 * i, 8) ∈ expRanges w := by
  rcases hi with rfl | rfl | rfl | rfl <;> simp [expRanges, bitRanges]

theorem shl_succ (x : BitVec 64) (t : Nat) : x <<< t + x <<< t = x <<< (t + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    ← Nat.two_mul, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_succ]
  congr 1
  rw [Nat.mul_left_comm, Nat.pow_succ, Nat.mul_comm (2 ^ t) 2]

theorem toNat_ofNat_ne {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat ≠ 0 ↔ n ≠ 0 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_shl3 {x : Nat} (hx : x < 2 ^ 60) : BitVec.ofNat 64 x <<< 3 = BitVec.ofNat 64 (8 * x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega_arith), Nat.mul_comm]

/-- The number of bits of word `k − 1`: 63 for the last. -/
theorem bits_sel {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 63) :
    (if decide (2 ^ 64 ≤ (BitVec.ofNat 64 (k - 1)).toNat + (~~~BitVec.setWidth 64 1#16).toNat + true.toNat) = true
      then BitVec.setWidth 64 64#16 else BitVec.setWidth 64 63#16) = BitVec.ofNat 64 (if k = 1 then 63 else 64) := by
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k - 1 < 2 ^ 64 by omega_arith),
    show (BitVec.setWidth 64 1#16 : BitVec 64).toNat = 1 from rfl, show true.toNat = 1 from rfl]
  split <;> split <;> rename_i h1 h2 <;> simp only [decide_eq_true_eq] at h1 <;> first | rfl | (exfalso; omega_arith)

/-- The start of a word: `kWords := k − 1`, its word into `kV`, its number
of bits into `kBits`. -/
theorem wordHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {k : Nat} (hk : 1 ≤ k) (hkw : k ≤ w) (hK : word s.mem B (8 * kWords) = BitVec.ofNat 64 k) :
    WP isa (.block [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords, ldh .x4 (sArr aN), .lsl .x .x5 .x3 3,
      .add .x .x4 .x4 .x5, ld .x5 .x4, sth .x5 kV, movi .x6 64, movi .x7 63, movi .x4 1, .subs .x .x8 .x3 .x4,
      .csel .x .x6 .x6 .x7, sth .x6 kBits]) s fun t =>
      t.mem = ((s.mem.writeW (off B (8 * kWords)) (BitVec.ofNat 64 (k - 1))).writeW (off B (8 * kV))
        (word s.mem B (slot w aN + 8 * (k - 1)))).writeW (off B (8 * kBits))
        (BitVec.ofNat 64 (if k = 1 then 63 else 64)) := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  have sN := h.sl (show aN < 16 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
  have hst : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi => hs.st (by omega_arith)
  brun [h.x0, hdr_enc (show kWords < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
    hdr_enc (show kV < 32 by decide), hdr_enc (show kBits < 32 by decide), hl kWords (by decide),
    hl (sArr aN) (by decide), hst kWords (by decide), hst kV (by decide), hst kBits (by decide), hK,
    ofNat64_pred hk (by omega_arith), ofNat_shl3 (show k - 1 < 2 ^ 60 by omega_arith), off_add,
    hs.ld (d := slot w aN + 8 * (k - 1)) (by omega_arith),
    fun X => (writeW_outside s.mem B X (d := 8 * kWords) (by decide)).word (d := slot w aN + 8 * (k - 1))
      (Or.inr (by have := hdr_lt_slot w aN (show kWords < 32 by decide); omega_arith)) (by omega_arith),
    fun X => (hdrStore_hdr s.mem B X (show kWords < 32 by decide) (show sArr aN < 32 by decide) (by decide)).trans
      (h.harr aN (by decide)), bits_sel hk (show k < 2 ^ 63 by omega_arith)]

/-- After `t` bits of word `k − 1`, `W`, of `c`. -/
structure BitInv (B : Addr) (Z w : Nat) (c b k nb : Nat) (W : BitVec 64) (s₀ : State) (t : Nat)
    (s : State) : Prop where
  ctx : MrCtx s B Z w c (b * 2 ^ (64 * w) % c)
  y : wv s.mem B (slot w aY) w = mrPow c b (64 * w) (64 * (w - k) + t) * 2 ^ (64 * w) % c
  flag : word s.mem B (8 * kFlag) = mask (mrPre c b (64 * w) (64 * (w - k) + t) false)
  v : word s.mem B (8 * kV) = W <<< t
  bits : word s.mem B (8 * kBits) = BitVec.ofNat 64 (nb - t)
  words : word s.mem B (8 * kWords) = BitVec.ofNat 64 (k - 1)
  frm : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- One bit of word `k − 1`. -/
theorem mrBitStep_ok (M : Mont) {B : Addr} {Z w c b k nb : Nat} {W : BitVec 64} {s₀ s : State}
    (hw4 : 4 ≤ w) (hw64 : w ≤ 64) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k) (hkw : k ≤ w)
    (hnb : nb = if k = 1 then 63 else 64)
    (hWc : ∀ u < 64, W.toNat.testBit u = c.testBit (64 * (k - 1) + u)) {j : Nat} (hj : j < nb)
    (hI : BitInv B Z w c b k nb W s₀ j s) :
    WP isa (seqs (mrExpBit M.mm)) s fun t =>
      BitInv B Z w c b k nb W s₀ (j + 1) t ∧ ((t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ nb) := by
  have hjT : 64 * (w - k) + j < 64 * w := by split at hnb <;> omega_arith
  have hp : 1 ≤ 64 * w - 1 - (64 * (w - k) + j) := by split at hnb <;> omega_arith
  have hbt := shl_shr63 W (t := j) (by split at hnb <;> omega_arith)
  have hcond : ((c - 1) / 2 ^ (64 * w - 1 - (64 * (w - k) + j)) % 2 = 1) ↔
      (W.toNat.testBit (63 - j)) = true := by
    rw [odd_sub_one_div hodd hp, div_bit_iff, hWc (63 - j) (by omega_arith)]
    rw [show 64 * w - 1 - (64 * (w - k) + j) = 64 * (k - 1) + (63 - j) by split at hnb <;> omega_arith]
  obtain ⟨hpow, hpre⟩ := mr_step (c := c) (b := b) (T := 64 * w) (j := 64 * (w - k) + j) false hjT hcond
  refine WP.mono (mrExpBit_ok M hI.ctx hw4 hw64 hodd hc1 hI.y hI.v hbt hI.flag hI.bits (by omega_arith)
    (by split at hnb <;> omega_arith)) fun t ⟨hct, hyt, hft, hvt, hbt', h3, hfr, kt⟩ => ⟨?_, ?_⟩
  · refine ⟨hct, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hyt, ← hpow, show 64 * (w - k) + (j + 1) = 64 * (w - k) + j + 1 by omega_arith]
    · rw [hft, show 64 * (w - k) + (j + 1) = 64 * (w - k) + j + 1 by omega_arith, hpre, ← hpow]
    · rw [hvt, shl_succ]
    · rw [hbt', show nb - j - 1 = nb - (j + 1) by omega_arith]
    · rw [hfr.word_eq (d := 8 * kWords) (by ex_disj) (by decide)]; exact hI.words
    · exact hI.frm.trans (hfr.mono fun r hr => List.mem_append_left _ hr)
    · exact (hI.keep.trans kt).mono (by decide)
  · rw [h3, toNat_ofNat_ne (by split at hnb <;> omega_arith)]; omega_arith

/-- The inner loop: the `nb` bits of word `k − 1`. -/
theorem mrBits_ok (M : Mont) {B : Addr} {Z w c b k nb : Nat} {W : BitVec 64} {s₀ s : State}
    (hw4 : 4 ≤ w) (hw64 : w ≤ 64) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k) (hkw : k ≤ w)
    (hnb : nb = if k = 1 then 63 else 64)
    (hWc : ∀ u < 64, W.toNat.testBit u = c.testBit (64 * (k - 1) + u))
    (h0 : BitInv B Z w c b k nb W s₀ 0 s) :
    WP isa (.loop (seqs (mrExpBit M.mm)) (.nonzero .x .x3)) s (BitInv B Z w c b k nb W s₀ nb) :=
  count_loop (cr := .x3) (n := nb) (by split at hnb <;> omega_arith) (BitInv B Z w c b k nb W s₀)
    (fun _ hj _ hI => mrBitStep_ok M hw4 hw64 hodd hc1 hk hkw hnb hWc hj hI) h0

/-- After `j` of the `w` words. -/
structure WordInv (B : Addr) (Z w : Nat) (c b : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  ctx : MrCtx s B Z w c (b * 2 ^ (64 * w) % c)
  y : wv s.mem B (slot w aY) w = mrPow c b (64 * w) (min (64 * j) (64 * w - 1)) * 2 ^ (64 * w) % c
  flag : word s.mem B (8 * kFlag) = mask (mrPre c b (64 * w) (min (64 * j) (64 * w - 1)) false)
  words : word s.mem B (8 * kWords) = BitVec.ofNat 64 (w - j)
  frm : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- The bits of a word: the word, as `BitInv` reads it. -/
abbrev wordW (m : Mem) (B : Addr) (w j : Nat) : BitVec 64 := word m B (slot w aN + 8 * (w - j - 1))

/-- The start of word `w − 1 − j`. -/
theorem wordStart_ok {B : Addr} {Z w c b : Nat} {s₀ s : State} {j : Nat} (hj : j < w)
    (hI : WordInv B Z w c b s₀ j s) :
    WP isa (.block [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords, ldh .x4 (sArr aN), .lsl .x .x5 .x3 3,
        .add .x .x4 .x4 .x5, ld .x5 .x4, sth .x5 kV, movi .x6 64, movi .x7 63, movi .x4 1, .subs .x .x8 .x3 .x4,
        .csel .x .x6 .x6 .x7, sth .x6 kBits]) s
      fun s₁ => BitInv B Z w c b (w - j) (if w - j = 1 then 63 else 64) (wordW s.mem B w j) s₀ 0 s₁ ∧
        ∀ u < 64, (wordW s.mem B w j).toNat.testBit u = c.testBit (64 * (w - j - 1) + u) := by
  have h := hI.ctx.ws
  have hZ8 := hI.ctx.good.2
  have hn := h.scr.nowrap
  have h256 := h.h256
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x7, .x8] (Q := fun t => t.mem = ((s.mem.writeW (off B (8 * kWords))
      (BitVec.ofNat 64 (w - j - 1))).writeW (off B (8 * kV)) (word s.mem B (slot w aN + 8 * (w - j - 1)))).writeW
      (off B (8 * kBits)) (BitVec.ofNat 64 (if w - j = 1 then 63 else 64)))
    (wordHead_ok h (k := w - j) (by omega_arith) (by omega_arith) hI.words) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hf₁ : Frm B (expRanges w) s.mem s₁.mem := by
    rw [hm₁]
    exact ((Frm.of_outside (writeW_outside _ B _ (d := 8 * kWords) (by decide))
      (expRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV)
        (by decide)) (expRanges_hdr w (Or.inr (Or.inl rfl))))).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits) (by decide))
        (expRanges_hdr w (Or.inr (Or.inr (Or.inl rfl)))))
  have hnw : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  refine ⟨⟨hI.ctx.of_exp hf₁ (fun _ h => h) k₁ (by decide), ?_, ?_, ?_, ?_, ?_, hI.frm.trans hf₁,
    (hI.keep.trans k₁).mono (by decide)⟩, fun u hu => ?_⟩
  · rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) hnw, hdrStore_wv _ _ _ (by decide) (by decide) hnw,
      hdrStore_wv _ _ _ (by decide) (by decide) hnw, hI.y,
      show min (64 * j) (64 * w - 1) = 64 * (w - (w - j)) + 0 by omega_arith]
  · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hI.flag,
      show min (64 * j) (64 * w - 1) = 64 * (w - (w - j)) + 0 by omega_arith]
  · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, BitVec.shiftLeft_zero]
  · rw [hm₁, word_writeW_self, Nat.sub_zero]
  · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [← hI.ctx.n, testBit_wv s.mem B (slot w aN) w _ (by omega_arith), show (64 * (w - j - 1) + u) / 64 = w - j - 1 by omega_arith,
      show (64 * (w - j - 1) + u) % 64 = u by omega_arith]

/-- The end of word `w − 1 − j`: `x3 := kWords`. -/
theorem wordEnd_ok {B : Addr} {Z w c b : Nat} {W : BitVec 64} {s₀ s : State} {j : Nat} (hj : j < w)
    (hB : BitInv B Z w c b (w - j) (if w - j = 1 then 63 else 64) W s₀ (if w - j = 1 then 63 else 64) s) :
    WP isa (.block [ldh .x3 kWords]) s fun t =>
      WordInv B Z w c b s₀ (j + 1) t ∧ ((t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ w) := by
  have h := hB.ctx.ws
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (w - j - 1) ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kWords < 32 by decide), h.scr.ld (d := 8 * kWords) (by simp only [kWords, kT1, sFn]; omega_arith), hB.words])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ⟨?_, ?_⟩
  · have e : 64 * (w - (w - j)) + (if w - j = 1 then 63 else 64) = min (64 * (j + 1)) (64 * w - 1) := by
      split <;> omega_arith
    refine ⟨hB.ctx.of_exp (rs := []) (fun x _ => by rw [hm]) (by simp) k (by decide), ?_, ?_, ?_,
      by rw [hm]; exact hB.frm, (hB.keep.trans k).mono (by decide)⟩
    · rw [hm, hB.y, e]
    · rw [hm, hB.flag, e]
    · rw [hm, hB.words, show w - j - 1 = w - (j + 1) by omega_arith]
  · rw [h3, toNat_ofNat_ne (by omega_arith)]; omega_arith

/-- One word of the exponentiation. -/
theorem mrWord_ok (M : Mont) {B : Addr} {Z w c b : Nat} {s₀ s : State} (hw4 : 4 ≤ w) (hw64 : w ≤ 64)
    (hodd : c % 2 = 1) (hc1 : 1 < c) {j : Nat} (hj : j < w) (hI : WordInv B Z w c b s₀ j s) :
    WP isa (seqs [
      .block [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords, ldh .x4 (sArr aN), .lsl .x .x5 .x3 3,
        .add .x .x4 .x4 .x5, ld .x5 .x4, sth .x5 kV, movi .x6 64, movi .x7 63, movi .x4 1, .subs .x .x8 .x3 .x4,
        .csel .x .x6 .x6 .x7, sth .x6 kBits],
      .loop (seqs (mrExpBit M.mm)) (.nonzero .x .x3),
      .block [ldh .x3 kWords]]) s fun t =>
      WordInv B Z w c b s₀ (j + 1) t ∧ ((t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ w) := by
  simp only [seqs]
  refine WP.seq (WP.mono (wordStart_ok hj hI) fun s₁ ⟨hB0, hWc⟩ => ?_)
  exact WP.seq (WP.mono (mrBits_ok M hw4 hw64 hodd hc1 (by omega_arith) (by omega_arith) rfl hWc hB0)
    fun s₂ hB => wordEnd_ok hj hB)

theorem setWidth_zero_mask : BitVec.setWidth 64 (0#16) = mask false := rfl

/-- The start of the exponentiation: `kWords := w`, the flag clear. -/
theorem expStart_ok {B : Addr} {Z w c b : Nat} {s : State} (hc : MrCtx s B Z w c (b * 2 ^ (64 * w) % c))
    (hc1 : 1 < c) (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (.block [ldh .x3 sW, sth .x3 kWords, movi .x3 0, sth .x3 kFlag]) s (WordInv B Z w c b s 0) := by
  have h := hc.ws
  have hZ8 := hc.good.2
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hcT : c - 1 < 2 ^ (64 * w) := by rw [← hc.n]; have := wv_lt s.mem B (slot w aN) w; omega_arith
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => h.scr.ld (by omega_arith)
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi => h.scr.st (by omega_arith)
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * kWords))
      (BitVec.ofNat 64 w)).writeW (off B (8 * kFlag)) (mask false)) (by
    brun [h.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show kWords < 32 by decide),
      hdr_enc (show kFlag < 32 by decide), hl sW (by decide), hs kWords (by decide), hs kFlag (by decide), h.hw,
      setWidth_zero_mask]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hf₁ : Frm B (expRanges w) s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kWords) (by decide))
      (expRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag)
        (by decide)) (expRanges_hdr w (Or.inr (Or.inr (Or.inr rfl)))))
  have hnw : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  refine ⟨hc.of_exp hf₁ (fun _ h => h) k₁ (by decide), ?_, ?_, ?_, hf₁, k₁.mono (by decide)⟩
  · rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) hnw, hdrStore_wv _ _ _ (by decide) (by decide) hnw,
      hY, show min (64 * 0) (64 * w - 1) = 0 by omega_arith, mrPow_zero hcT hc1, Nat.one_mul]
  · rw [hm₁, word_writeW_self, show min (64 * 0) (64 * w - 1) = 0 by omega_arith]; rfl
  · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.sub_zero]

/-- The exponentiation: from `y = 1` (`R mod c` in `aY`), `y` and the flag
after the top `64 w − 1` bits of `c − 1`. -/
theorem mrExpLoop_ok (M : Mont) {B : Addr} {Z w c b : Nat} {s : State}
    (hc : MrCtx s B Z w c (b * 2 ^ (64 * w) % c)) (hw4 : 4 ≤ w) (hw64 : w ≤ 64) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (seqs (mrExpLoop M.mm)) s fun t => MrCtx t B Z w c (b * 2 ^ (64 * w) % c) ∧
      wv t.mem B (slot w aY) w = mrPow c b (64 * w) (64 * w - 1) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (mrPre c b (64 * w) (64 * w - 1) false) ∧
      Frm B (expRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold mrExpLoop
  simp only [seqs]
  refine WP.seq (WP.mono (expStart_ok hc hc1 hY) fun s₁ hI0 => ?_)
  refine WP.mono (count_loop (cr := .x3) (n := w) (by omega_arith) (WordInv B Z w c b s)
    (fun j hj t hI => mrWord_ok M hw4 hw64 hodd hc1 hj hI) hI0) fun t hI => ?_
  have e : min (64 * w) (64 * w - 1) = 64 * w - 1 := by omega_arith
  exact ⟨hI.ctx, by rw [hI.y, e], by rw [hI.flag, e], hI.frm, hI.keep⟩

end VG.Proof.RsaKeyGen.AArch64
