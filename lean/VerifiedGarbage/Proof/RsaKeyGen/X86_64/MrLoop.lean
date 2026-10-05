import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrBitAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Bits

/-!
# A candidate on x86-64: Miller–Rabin's exponentiation loops

`BitInv`: after `t` bits of word `k − 1` of `c` (the words from the top),
`y R mod c` and the flag for the `64 (w − k) + t` bits from the top
(`mrPow`, `mrPre`), the word shifted left by `t` in `kV`. `mrBits_ok`: the
inner loop over the word's bits, 64 but 63 of the last.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What the exponentiation changes. -/
def expRanges (w : Nat) : List (Nat × Nat) := bitRanges w ++ [(8 * kWords, 8)]

/-- After `t` bits of word `k − 1`, `W`, of `c`. -/
structure BitInv (B : Addr) (Z w : Nat) (mi : BitVec 64) (c b k nb : Nat) (W : BitVec 64) (s₀ : State) (t : Nat)
    (s : State) : Prop where
  ctx : MrCtx s B Z w mi c (b * 2 ^ (64 * w) % c)
  y : wv s.mem B (slot w aY) w = mrPow c b (64 * w) (64 * (w - k) + t) * 2 ^ (64 * w) % c
  flag : word s.mem B (8 * kFlag) = mask (mrPre c b (64 * w) (64 * (w - k) + t) false)
  v : word s.mem B (8 * kV) = W <<< t
  bits : word s.mem B (8 * kBits) = BitVec.ofNat 64 (nb - t)
  words : word s.mem B (8 * kWords) = BitVec.ofNat 64 (k - 1)
  frm : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

theorem shl_succ (x : BitVec 64) (t : Nat) : x <<< t + x <<< t = x <<< (t + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    ← Nat.two_mul, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_succ]
  congr 1
  rw [Nat.mul_left_comm, Nat.pow_succ, Nat.mul_comm (2 ^ t) 2]

/-- One bit of word `k − 1`. -/
theorem mrBitStep_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c b k nb : Nat} {W : BitVec 64}
    {s₀ s : State} (hd : MrDims B Z w) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k) (hkw : k ≤ w)
    (hnb : nb = if k = 1 then 63 else 64)
    (hWc : ∀ u < 64, W.toNat.testBit u = c.testBit (64 * (k - 1) + u)) {j : Nat} (hj : j < nb)
    (hI : BitInv B Z w mi c b k nb W s₀ j s) :
    WP isa (seqs (mrExpBit M.mm)) s fun t =>
      t.zf = some (decide (j + 1 = nb)) ∧ BitInv B Z w mi c b k nb W s₀ (j + 1) t := by
  have hjT : 64 * (w - k) + j < 64 * w := by split at hnb <;> omega
  have hp : 1 ≤ 64 * w - 1 - (64 * (w - k) + j) := by split at hnb <;> omega
  have hbt := shl_shr63 W (t := j) (by split at hnb <;> omega)
  have hcond : ((c - 1) / 2 ^ (64 * w - 1 - (64 * (w - k) + j)) % 2 = 1) ↔
      (W.toNat.testBit (63 - j)) = true := by
    rw [odd_sub_one_div hodd hp, div_bit_iff, hWc (63 - j) (by omega)]
    rw [show 64 * w - 1 - (64 * (w - k) + j) = 64 * (k - 1) + (63 - j) by split at hnb <;> omega]
  obtain ⟨hpow, hpre⟩ := mr_step (c := c) (b := b) (T := 64 * w) (j := 64 * (w - k) + j) false hjT hcond
  refine WP.mono (mrExpBit_ok M hd hI.ctx hodd hc1 hI.y hI.v hbt hI.flag hI.bits (by omega) (by split at hnb <;> omega))
    fun t ⟨hct, hyt, hft, hvt, hbt', hz, hfr, kt⟩ => ⟨by rw [hz, decide_eq_decide.mpr (show nb - j - 1 = 0 ↔ j + 1 = nb by omega)], ?_⟩
  refine ⟨hct, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hyt, ← hpow, show 64 * (w - k) + (j + 1) = 64 * (w - k) + j + 1 by omega]
  · rw [hft, show 64 * (w - k) + (j + 1) = 64 * (w - k) + j + 1 by omega, hpre, ← hpow]
  · rw [hvt, shl_succ]
  · rw [hbt', show nb - j - 1 = nb - (j + 1) by omega]
  · rw [hfr.word_eq (d := 8 * kWords) (by simp only [bitRanges]; rng_disj)
    (by unfold kWords kT1 sFn; omega)]; exact hI.words
  · exact hI.frm.trans (hfr.mono fun r hr => List.mem_append_left _ hr)
  · exact (hI.keep.trans kt).mono (by decide)

/-- The inner loop: the `nb` bits of word `k − 1`. -/
theorem mrBits_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c b k nb : Nat} {W : BitVec 64}
    {s₀ s : State} (hd : MrDims B Z w) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k) (hkw : k ≤ w)
    (hnb : nb = if k = 1 then 63 else 64)
    (hWc : ∀ u < 64, W.toNat.testBit u = c.testBit (64 * (k - 1) + u))
    (h0 : BitInv B Z w mi c b k nb W s₀ 0 s) :
    WP isa (.loop (seqs (mrExpBit M.mm)) .ne) s (BitInv B Z w mi c b k nb W s₀ nb) := by
  have hnb1 : 1 ≤ nb := by split at hnb <;> omega
  exact wp_upto (a := 0) (N := nb) (by omega) (BitInv B Z w mi c b k nb W s₀)
    (fun j _ hj s hI => mrBitStep_ok M hd hodd hc1 hk hkw hnb hWc hj hI) (fun _ h => h) h0

/-- The start of a word: `kWords := k − 1`, its word into `kV`, its number
of bits into `kBits`. -/
theorem wordHead_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    {k : Nat} (hk : 1 ≤ k) (hkw : k ≤ w) (hw : w < 2 ^ 31) (hK : word s.mem B (8 * kWords) = BitVec.ofNat 64 k) :
    WP isa (.block [.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax,
      .mov .rdx (.mem (hdr (sArr aN))), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
      .mov32 .rcx (.imm 64), .alu .cmp .rax (.imm 1), .alu .sbb .rcx (.imm 0), .store (hdr kBits) .rcx]) s fun t =>
      t.mem = ((s.mem.writeW (off B (8 * kWords)) (BitVec.ofNat 64 (k - 1))).writeW (off B (8 * kV))
        (word s.mem B (slot w aN + 8 * (k - 1)))).writeW (off B (8 * kBits))
        (BitVec.ofNat 64 (if k = 1 then 63 else 64)) ∧ Keep [.rax, .rcx, .rdx] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hg.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t => t.mem = ((s.mem.writeW (off B (8 * kWords))
      (BitVec.ofNat 64 (k - 1))).writeW (off B (8 * kV)) (word s.mem B (slot w aN + 8 * (k - 1)))).writeW
      (off B (8 * kBits)) (BitVec.ofNat 64 (if k = 1 then 63 else 64))) (by
    xrun [State.ea, hdr, ix, hg.rdi, hdrOff, hl kWords (by decide), hl (sArr aN) (by decide), hs kWords (by decide),
      hs kV (by decide), hs kBits (by decide), hK, ofNat64_pred hk (by omega),
      fun X => (hdrStore_hdr s.mem B X (show kWords < 32 by decide) (show sArr aN < 32 by decide) (by decide)).trans
        (hg.hdr.harr aN (by decide)),
      addr0 rfl rfl, hg.scr.ld (d := slot w aN + 8 * (k - 1)) (by omega),
      fun X => (writeW_outside s.mem B X (d := 8 * kWords) (by unfold kWords kT1 sFn; omega)).word
        (d := slot w aN + 8 * (k - 1)) (Or.inr (by unfold slot kWords kT1 sFn aN hdrBytes; omega)) (by omega)]
    congr 1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
    by_cases h1 : k = 1
    · simp only [h1, Nat.sub_self, Nat.zero_lt_one, decide_true, ↓reduceIte]; decide
    · simp only [h1, show ¬ (k - 1 < 1) by omega, decide_false, ↓reduceIte]; decide) rfl)
    fun t ⟨hm, k⟩ => ⟨hm, k⟩

/-- After `j` of the `w` words. -/
structure WordInv (B : Addr) (Z w : Nat) (mi : BitVec 64) (c b : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  ctx : MrCtx s B Z w mi c (b * 2 ^ (64 * w) % c)
  y : wv s.mem B (slot w aY) w = mrPow c b (64 * w) (min (64 * j) (64 * w - 1)) * 2 ^ (64 * w) % c
  flag : word s.mem B (8 * kFlag) = mask (mrPre c b (64 * w) (min (64 * j) (64 * w - 1)) false)
  words : word s.mem B (8 * kWords) = BitVec.ofNat 64 (w - j)
  frm : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

theorem expRanges_hdr (w : Nat) {i : Nat} (hi : i = kWords ∨ i = kV ∨ i = kBits ∨ i = kFlag) :
    (8 * i, 8) ∈ expRanges w := by
  rcases hi with rfl | rfl | rfl | rfl <;> simp [expRanges, bitRanges]

/-- The bits of a word: the word, as `BitInv` reads it. -/
abbrev wordW (m : Mem) (B : Addr) (w j : Nat) : BitVec 64 := word m B (slot w aN + 8 * (w - j - 1))

/-- The start of word `w − 1 − j`. -/
theorem wordStart_ok {B : Addr} {Z w : Nat} {mi : BitVec 64} {c b : Nat} {s₀ s : State}
    (hd : MrDims B Z w) {j : Nat} (hj : j < w) (hI : WordInv B Z w mi c b s₀ j s) :
    WP isa (.block [.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax,
        .mov .rdx (.mem (hdr (sArr aN))), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
        .mov32 .rcx (.imm 64), .alu .cmp .rax (.imm 1), .alu .sbb .rcx (.imm 0), .store (hdr kBits) .rcx]) s
      fun s₁ => BitInv B Z w mi c b (w - j) (if w - j = 1 then 63 else 64) (wordW s.mem B w j) s₀ 0 s₁ ∧
        ∀ u < 64, (wordW s.mem B w j).toNat.testBit u = c.testBit (64 * (w - j - 1) + u) := by
  have hg := hI.ctx.good
  have hZ := hd.z
  have hw4 := hd.w4
  have hw' : w < 2 ^ 31 := by have := hd.w64; omega
  have hn := hg.scr.nowrap
  refine WP.mono (wordHead_ok hg hZ (k := w - j) (by omega) (by omega) hw' hI.words) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hf₁ : Frm B (expRanges w) s.mem s₁.mem := by
    rw [hm₁]
    exact ((Frm.of_outside (writeW_outside _ B _ (d := 8 * kWords) (by unfold kWords kT1 sFn; omega))
      (expRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV)
        (by unfold kV kT0 sFn; omega)) (expRanges_hdr w (Or.inr (Or.inl rfl))))).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits) (by unfold kBits kT2 sFn; omega))
        (expRanges_hdr w (Or.inr (Or.inr (Or.inl rfl)))))
  have hs₁ := hg.scr.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  have hc₁ := hI.ctx.of_frm hd hf₁ hs₁ hdi₁ (by simp only [expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj)
  refine ⟨⟨hc₁, ?_, ?_, ?_, ?_, ?_, hI.frm.trans hf₁, (hI.keep.trans k₁).mono (by decide)⟩, fun u hu => ?_⟩
  · rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) (by omega), hdrStore_wv _ _ _ (by decide) (by decide) (by omega),
      hdrStore_wv _ _ _ (by decide) (by decide) (by omega), hI.y,
      show min (64 * j) (64 * w - 1) = 64 * (w - (w - j)) + 0 by omega]
  · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hI.flag,
      show min (64 * j) (64 * w - 1) = 64 * (w - (w - j)) + 0 by omega]
  · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, BitVec.shiftLeft_zero]
  · rw [hm₁, word_writeW_self, Nat.sub_zero]
  · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [← hI.ctx.n, testBit_wv s.mem B (slot w aN) w _ (by omega), show (64 * (w - j - 1) + u) / 64 = w - j - 1 by omega,
      show (64 * (w - j - 1) + u) % 64 = u by omega]

/-- The end of word `w − 1 − j`: ZF set after the last. -/
theorem wordEnd_ok {B : Addr} {Z w : Nat} {mi : BitVec 64} {c b : Nat} {W : BitVec 64} {s₀ s : State}
    (hd : MrDims B Z w) {j : Nat} (hj : j < w)
    (hB : BitInv B Z w mi c b (w - j) (if w - j = 1 then 63 else 64) W s₀ (if w - j = 1 then 63 else 64) s) :
    WP isa (.block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (decide (j + 1 = w)) ∧ WordInv B Z w mi c b s₀ (j + 1) t := by
  have hg₂ := hB.ctx.good
  have hn := hg₂.scr.nowrap
  have hZ := hd.z
  have hw' : w < 2 ^ 31 := by have := hd.w64; omega
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kWords)) 8 :=
    hg₂.scr.ld (by have := hdr_lt_slot w 8 (show kWords < 32 by decide); omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (j + 1 = w)) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg₂.rdi, hdrOff, hl, hB.words, BitVec.and_self, ofNat64_beq_zero (show w - j - 1 < 2 ^ 64 by omega)]
    exact decide_eq_decide.mpr (by omega)) rfl) fun t ⟨⟨hz, hm⟩, k⟩ => ⟨hz, ?_⟩
  have e : 64 * (w - (w - j)) + (if w - j = 1 then 63 else 64) = min (64 * (j + 1)) (64 * w - 1) := by
    split <;> omega
  refine ⟨?_, ?_, ?_, ?_, by rw [hm]; exact hB.frm, (hB.keep.trans k).mono (by decide)⟩
  · exact hB.ctx.of_frm hd (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (hg₂.scr.congr k.2.2)
      ((k.gpr (by decide)).trans hg₂.rdi) (by simp) (by simp) (by simp) (by simp) (by simp)
  · rw [hm, hB.y, e]
  · rw [hm, hB.flag, e]
  · rw [hm, hB.words, show w - j - 1 = w - (j + 1) by omega]

/-- One word of the exponentiation. -/
theorem mrWord_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c b : Nat} {s₀ s : State}
    (hd : MrDims B Z w) (hodd : c % 2 = 1) (hc1 : 1 < c) {j : Nat} (hj : j < w) (hI : WordInv B Z w mi c b s₀ j s) :
    WP isa (seqs [
      .block [.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax,
        .mov .rdx (.mem (hdr (sArr aN))), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
        .mov32 .rcx (.imm 64), .alu .cmp .rax (.imm 1), .alu .sbb .rcx (.imm 0), .store (hdr kBits) .rcx],
      .loop (seqs (mrExpBit M.mm)) .ne,
      .block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]]) s fun t =>
      t.zf = some (decide (j + 1 = w)) ∧ WordInv B Z w mi c b s₀ (j + 1) t := by
  simp only [seqs]
  refine WP.seq (WP.mono (wordStart_ok hd hj hI) fun s₁ ⟨hB0, hWc⟩ => ?_)
  exact WP.seq (WP.mono (mrBits_ok M hd hodd hc1 (by omega) (by omega) rfl hWc hB0) fun s₂ hB => wordEnd_ok hd hj hB)

/-- The start of the exponentiation: `kWords := w`, the flag clear. -/
theorem expStart_ok {B : Addr} {Z w : Nat} {mi : BitVec 64} {c b : Nat} {s : State}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c (b * 2 ^ (64 * w) % c)) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (.block [.mov .rax (.mem (hdr sW)), .store (hdr kWords) .rax, .mov32 .rax (.imm 0), .store (hdr kFlag) .rax])
      s (WordInv B Z w mi c b s 0) := by
  have hg := hc.good
  have hZ := hd.z
  have hw4 := hd.w4
  have hn := hg.scr.nowrap
  have hcT : c - 1 < 2 ^ (64 * w) := by rw [← hc.n]; have := wv_lt s.mem B (slot w aN) w; omega
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hg.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * kWords))
      (BitVec.ofNat 64 w)).writeW (off B (8 * kFlag)) (mask false)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hs kWords (by decide), hs kFlag (by decide), hg.hdr.hw]
    rfl) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hf₁ : Frm B (expRanges w) s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kWords) (by unfold kWords kT1 sFn; omega))
      (expRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag)
        (by unfold kFlag kPlen sFn; omega)) (expRanges_hdr w (Or.inr (Or.inr (Or.inr rfl)))))
  have hs₁ := hg.scr.congr k₁.2.2
  refine ⟨hc.of_frm hd hf₁ hs₁ ((k₁.gpr (by decide)).trans hg.rdi)
    (by simp only [expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj), ?_, ?_, ?_, hf₁,
    k₁.mono (by decide)⟩
  · rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) (by omega), hdrStore_wv _ _ _ (by decide) (by decide) (by omega),
      hY, show min (64 * 0) (64 * w - 1) = 0 by omega, mrPow_zero hcT hc1, Nat.one_mul]
  · rw [hm₁, word_writeW_self, show min (64 * 0) (64 * w - 1) = 0 by omega]; rfl
  · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.sub_zero]

/-- The exponentiation: from `y = 1` (`R mod c` in `aY`), `y` and the flag
after the top `64 w − 1` bits of `c − 1`. -/
theorem mrExpLoop_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c b : Nat} {s : State}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c (b * 2 ^ (64 * w) % c)) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (seqs (mrExpLoop M.mm)) s fun t => MrCtx t B Z w mi c (b * 2 ^ (64 * w) % c) ∧
      wv t.mem B (slot w aY) w = mrPow c b (64 * w) (64 * w - 1) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (mrPre c b (64 * w) (64 * w - 1) false) ∧
      Frm B (expRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw4 := hd.w4
  unfold mrExpLoop
  simp only [seqs]
  refine WP.seq (WP.mono (expStart_ok hd hc hc1 hY) fun s₁ hI0 => ?_)
  refine wp_upto (a := 0) (N := w) (by omega) (WordInv B Z w mi c b s) (fun j _ hj t hI => mrWord_ok M hd hodd hc1 hj hI)
    (fun t hI => ?_) hI0
  have e : min (64 * w) (64 * w - 1) = 64 * w - 1 := by omega
  exact ⟨hI.ctx, by rw [hI.y, e], by rw [hI.flag, e], hI.frm, hI.keep⟩

end VG.Proof.RsaKeyGen.X86_64
