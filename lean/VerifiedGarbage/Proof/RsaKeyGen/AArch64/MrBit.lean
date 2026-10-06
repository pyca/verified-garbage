import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrCtx
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.RsaKeyGen.MrMont

/-!
# A candidate on AArch64: one bit of Miller–Rabin's exponentiation

`mrExpBit_ok`: from `y R mod c` in `aY` and the top bit `bt` of `kV`,
`y' = y² b^bt mod c` (as `y' R mod c`), the flag updated with `y' = 1` and
`y' = c − 1` (`eqMask_ok`), `kV` doubled and `x3 := kBits := kBits − 1`.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- `eqMask j`: `x15 :=` the mask of `[aY] = [j]`. -/
theorem eqMask_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (seqs (eqMask j)) s fun t =>
      t.gpr .x15 = mask (decide (wv s.mem B (slot w aY) w = wv s.mem B (slot w j) w)) ∧ t.mem = s.mem ∧
      Keep mmRegs s t := by
  unfold eqMask
  refine wp_seqs_append (by simp [eqA]) (by simp) ?_
  refine WP.mono (eqA_ok h (a := aY) (b := j) (by decide) hj) fun s₁ ⟨hz, m₁, _, _, k₁⟩ => ?_
  have e : (!decide (2 ^ 64 ≤ (s₁.gpr .x9).toNat + (~~~(BitVec.setWidth 64 1#16 : BitVec 64)).toNat + 1)) =
      decide (wv s.mem B (slot w aY) w = wv s.mem B (slot w j) w) := (lt_one_flag _).trans (decide_eq_decide.mpr hz)
  simp only [seqs]
  refine WP.mono (WP.keep [.x3, .x4, .x7, .x15] (Q := fun t => t.gpr .x15 =
      mask (decide (wv s.mem B (slot w aY) w = wv s.mem B (slot w j) w)) ∧ t.mem = s₁.mem) (by
    brun [borrowMask, Bool.toNat_true, csel_mask', e]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h15, mt⟩, k⟩ => ⟨h15, mt.trans m₁, (k₁.trans k).mono (by decide)⟩


theorem neg_bit (b : Bool) : BitVec.setWidth 64 0#16 - BitVec.ofNat 64 b.toNat = mask b := by
  cases b <;> decide

/-- The flag's update. -/
theorem flag_mask (P m e bt : Bool) :
    (mask P ||| mask m) &&& (mask bt ^^^ BitVec.setWidth 64 0#16 - 1#64) ||| (mask e ||| mask m) &&& mask bt =
      mask (if bt then e || m else P || m) := by
  cases P <;> cases m <;> cases e <;> cases bt <;> decide

theorem shl_one (x : BitVec 64) : x <<< 1 = x + x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_two]

theorem ofNat64_pred {n : Nat} (h : 1 ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show n - 1 < 2 ^ 64 by omega)]
  omega

theorem bitTail_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {V : BitVec 64} {bt m e P : Bool} {n : Nat} (hV : word s.mem B (8 * kV) = V)
    (hbt : V >>> 63 = BitVec.ofNat 64 bt.toNat) (hG : word s.mem B (8 * kG) = mask m) (h15 : s.gpr .x15 = mask e)
    (hP : word s.mem B (8 * kFlag) = mask P) (hnb : word s.mem B (8 * kBits) = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn' : n < 2 ^ 64) :
    WP isa (.block [mov .x9 .x15, ldh .x3 kV, .lsr .x .x3 .x3 63, movi .x7 0, .sub .x .x6 .x7 .x3, ldh .x5 kG,
      .logic .orr .x .x9 .x9 .x5, .logic .and .x .x9 .x9 .x6, ldh .x4 kFlag, .logic .orr .x .x4 .x4 .x5,
      .subImm .x .x8 .x7 1, .logic .eor .x .x6 .x6 .x8, .logic .and .x .x4 .x4 .x6, .logic .orr .x .x4 .x4 .x9,
      sth .x4 kFlag, ldh .x3 kV, .lsl .x .x3 .x3 1, sth .x3 kV, ldh .x3 kBits, .subImm .x .x3 .x3 1, sth .x3 kBits])
      s fun t =>
      (t.mem = ((s.mem.writeW (off B (8 * kFlag)) (mask (if bt then e || m else P || m))).writeW (off B (8 * kV))
        (V + V)).writeW (off B (8 * kBits)) (BitVec.ofNat 64 (n - 1)) ∧ t.gpr .x3 = BitVec.ofNat 64 (n - 1)) ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x8, .x9] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have hst : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi => hs.st (by omega)
  refine WP.keep [.x3, .x4, .x5, .x6, .x7, .x8, .x9] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h.x0, hdr_enc (show kV < 32 by decide), hdr_enc (show kG < 32 by decide), hdr_enc (show kFlag < 32 by decide),
    hdr_enc (show kBits < 32 by decide), hl kV (by decide), hl kG (by decide), hl kFlag (by decide),
    hl kBits (by decide), hst kV (by decide), hst kFlag (by decide), hst kBits (by decide), hV, hG, hP, h15, hbt,
    neg_bit, flag_mask, shl_one,
    fun X => (hdrStore_hdr s.mem B X (show kFlag < 32 by decide) (show kV < 32 by decide) (by decide)).trans hV,
    fun X Y => (hdrStore_hdr _ B Y (show kV < 32 by decide) (show kBits < 32 by decide) (by decide)).trans
      ((hdrStore_hdr s.mem B X (show kFlag < 32 by decide) (show kBits < 32 by decide) (by decide)).trans hnb),
    ofNat64_pred hn1 hn']

/-- The selection's head: `x15 :=` the mask of the top bit of `kV`, `x14 := w`,
`x16` at `aB` and `x17` at `aXm`. -/
theorem bitSel_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {V : BitVec 64} {bt : Bool}
    (hV : word s.mem B (8 * kV) = V) (hbt : V >>> 63 = BitVec.ofNat 64 bt.toNat) :
    WP isa (.block (bitMask ++ ws ++ base aB .x16 ++ base aXm .x17 ++ [mov .x14 .x12])) s fun t =>
      (t.gpr .x15 = mask bt ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x16 = off B (slot w aB) ∧
        t.gpr .x17 = off B (slot w aXm) ∧ t.mem = s.mem) ∧
      Keep [.x3, .x7, .x15, .x11, .x12, .x16, .x17, .x14] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  rw [List.append_assoc (bitMask ++ ws) (base aB .x16) (base aXm .x17)]
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr ?_)
  refine WP.mono (WP.keep [.x3, .x7, .x15, .x11, .x12] (Q := fun t => t.gpr .x15 = mask bt ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem) (by
    brun [bitMask, ws, h.x0, hdr_enc (show kV < 32 by decide), hdr_enc (show sW < 32 by decide),
      hdr_enc (show sStride < 32 by decide), hl kV (by decide), hl sW (by decide), hl sStride (by decide), hV, hbt,
      neg_bit, h.hw, h.hS]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h15, h12, h11, m₁⟩, k₁⟩ => ?_
  refine WP.mono (base2_ok aB aXm .x16 .x17 ((k₁.gpr .x0 (by decide)).trans h.x0) h11)
    fun s₂ ⟨⟨h16, h17, m₂, _⟩, k₂⟩ => ?_
  have h12₂ : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  refine WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = s₂.mem) (by
    brun [h12₂]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h14, m₃⟩, k₃⟩ => ?_
  have k23 := k₂.trans k₃
  exact ⟨⟨(k23.gpr .x15 (by decide)).trans h15, h14, (k₃.gpr .x16 (by decide)).trans h16,
    (k₃.gpr .x17 (by decide)).trans h17, by rw [m₃, m₂, m₁]⟩, (k₁.trans k23).mono (by decide)⟩

/-- What `mrExpBit` changes. -/
def bitRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)),
    (8 * kG, 8), (8 * kFlag, 8), (8 * kV, 8), (8 * kBits, 8)]

/-- What its multiplications and selection change: arrays only. -/
def mulRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]

theorem mulRanges_sub (w : Nat) : ∀ r ∈ mulRanges w, r ∈ bitRanges w := by
  intro r hr
  simp only [mulRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp [bitRanges]

theorem bitRanges_mut (w : Nat) : ∀ r ∈ bitRanges w, KMut r := by
  simp only [bitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    first | exact KMut.ofSlot w _ _ | exact KMut.hdr (by decide)

/-- Disjointness of a range from each of a list of literal ranges of the
working space. -/
macro "mr_disj" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, bitRanges, slot,
    hdrBytes, aN, aAcc, aTmp, aY, aXm, aB, aR1, aRm1, kG, kFlag, kPlen, kV, kT0, sCnt, kBits, kT2, sFn, sMinv]
  and_intros <;> omega))

/-- `MrCtx` across changes within `bitRanges`. -/
theorem MrCtx.of_bit {s t : State} {B : Addr} {Z w c bm : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w c bm) (hf : Frm B rs s.mem t.mem) (hs : ∀ r ∈ rs, r ∈ bitRanges w)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : MrCtx t B Z w c bm :=
  hc.of_frm (hf.mono hs) (bitRanges_mut w) k hr (by mr_disj) (by mr_disj) (by mr_disj) (by mr_disj) (by mr_disj)

/-- The multiplications of `mrExpBit`: `y := y²`, `[aXm] := bit ? [aB] : [aR1]`,
`y := y [aXm]`. -/
theorem mrMul_ok (M : Mont) {s : State} {B : Addr} {Z w c b y : Nat}
    (hc : MrCtx s B Z w c (b * 2 ^ (64 * w) % c)) (hw64 : w ≤ 64) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % c)
    {V : BitVec 64} {bt : Bool} (hV : word s.mem B (8 * kV) = V) (hbt : V >>> 63 = BitVec.ofNat 64 bt.toNat) :
    WP isa (seqs [M.mm aY aY aY, copyA aXm aR1, .block (bitMask ++ ws ++ base aB .x16 ++ base aXm .x17 ++
        [mov .x14 .x12]), Crt.selLoop, M.mm aY aY aXm]) s fun t =>
      MrCtx t B Z w c (b * 2 ^ (64 * w) % c) ∧
      wv t.mem B (slot w aY) w = (y * y % c * (if bt then b else 1) % c) * 2 ^ (64 * w) % c ∧
      Frm B (mulRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega
  have hw' : w < 2 ^ 31 := by omega
  have hw2 := hc.ws.w1
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have sXm := hc.ws.sl (show aXm < 16 by decide)
  have sB := hc.ws.sl (show aB < 16 by decide)
  have sY := hc.ws.sl (show aY < 16 by decide)
  have hg := hc.good
  simp only [seqs]
  -- `y := y²`.
  refine WP.seq (WP.mono (M.mm_ok hg.1 hg.2 hw2 hw' (o := aY) (a := aY) (b := aY) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hY, hc.n]; exact Nat.mod_lt _ hc0)) fun s₁ ⟨_, hlt₁, hy₁, ha₁, k₁⟩ => ?_)
  rw [hc.n] at hlt₁ hy₁
  rw [hY] at hy₁
  have hY₁ : wv s₁.mem B (slot w aY) w = y * y % c * 2 ^ (64 * w) % c := mont_val hR hlt₁ hy₁ rfl rfl
  have f₁ : Frm B (mulRanges w) s.mem s₁.mem := Frm.of_arrays ha₁ (by simp [mulRanges])
  have hc₁ := hc.of_bit f₁ (mulRanges_sub w) k₁ (by decide)
  have hV₁ : word s₁.mem B (8 * kV) = V := by rw [ha₁.hslot (by decide)]; exact hV
  -- `[aXm] := [aR1]`.
  refine WP.seq (WP.mono (copyA_ok hc₁.ws (o := aXm) (a := aR1) (by decide) (by decide) (by decide))
    fun s₂ ⟨hv₂, o₂, _, _, k₂⟩ => ?_)
  rw [hc₁.r1] at hv₂
  have o₂' : Outside B (slot w aXm) (8 * (w + 2)) s₁.mem s₂.mem := o₂.mono (Nat.le_refl _) (by omega)
  have f₂ : Frm B (mulRanges w) s₁.mem s₂.mem := Frm.of_outside o₂' (by simp [mulRanges])
  have hc₂ := hc₁.of_bit f₂ (mulRanges_sub w) k₂ (by decide)
  have hV₂ : word s₂.mem B (8 * kV) = V := by
    have := hdr_lt_slot w aXm (show kV < 32 by decide)
    rw [o₂'.word (Or.inl this) (by omega)]; exact hV₁
  have hY₂ : wv s₂.mem B (slot w aY) w = y * y % c * 2 ^ (64 * w) % c := by
    rw [o₂'.wv (by simp only [slot, aXm, aY]; omega) (by omega)]; exact hY₁
  -- The selection.
  refine WP.seq (WP.mono (bitSel_ok hc₂.ws hV₂ hbt) fun s₃ ⟨⟨h15, h14, h16, h17, m₃⟩, k₃⟩ => ?_)
  refine WP.seq (WP.mono (selLoop_ok (hc₂.ws.scr.congr k₃.wr) h16 h17 h14 h15 (by omega) hw' (by omega) (by omega)
    (Or.inl (by simp only [slot, aXm, aB]; omega))) fun s₄ ⟨hv₄, o₄, k₄⟩ => ?_)
  rw [m₃, hc₂.b, hv₂] at hv₄
  rw [m₃] at o₄
  have o₄' : Outside B (slot w aXm) (8 * (w + 2)) s₂.mem s₄.mem := o₄.mono (Nat.le_refl _) (by omega)
  have f₄ : Frm B (mulRanges w) s₂.mem s₄.mem := Frm.of_outside o₄' (by simp [mulRanges])
  have k₃₄ := k₃.trans k₄
  have hc₄ := hc₂.of_bit f₄ (mulRanges_sub w) k₃₄ (by decide)
  have hX₄ : wv s₄.mem B (slot w aXm) w = (if bt then b else 1) * 2 ^ (64 * w) % c := by
    rw [hv₄]; cases bt <;> simp
  have hY₄ : wv s₄.mem B (slot w aY) w = y * y % c * 2 ^ (64 * w) % c := by
    rw [o₄'.wv (by simp only [slot, aXm, aY]; omega) (by omega)]; exact hY₂
  -- `y := y [aXm]`.
  have hg₄ := hc₄.good
  refine WP.mono (M.mm_ok hg₄.1 hg₄.2 hw2 hw' (o := aY) (a := aY) (b := aXm) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc₄.inv
    (by rw [hX₄, hc₄.n]; exact Nat.mod_lt _ hc0)) fun t ⟨_, hlt, hy, ha, k⟩ => ?_
  rw [hc₄.n] at hlt hy
  rw [hY₄, hX₄] at hy
  have f : Frm B (mulRanges w) s₄.mem t.mem := Frm.of_arrays ha (by simp [mulRanges])
  exact ⟨hc₄.of_bit f (mulRanges_sub w) k (by decide), mont_val hR hlt hy rfl rfl,
    ((f₁.trans f₂).trans f₄).trans f, (((k₁.trans k₂).trans k₃₄).trans k).mono (by decide)⟩

theorem mrExpBit_eq (mul : Nat → Nat → Nat → Prog isa) : mrExpBit mul =
    [mul aY aY aY, copyA aXm aR1, .block (bitMask ++ ws ++ base aB .x16 ++ base aXm .x17 ++ [mov .x14 .x12]),
      Crt.selLoop, mul aY aY aXm] ++ (eqMask aRm1 ++ (([.block [sth .x15 kG]] : List (Prog isa)) ++
      (eqMask aR1 ++ ([.block [mov .x9 .x15, ldh .x3 kV, .lsr .x .x3 .x3 63, movi .x7 0, .sub .x .x6 .x7 .x3,
        ldh .x5 kG, .logic .orr .x .x9 .x9 .x5, .logic .and .x .x9 .x9 .x6, ldh .x4 kFlag,
        .logic .orr .x .x4 .x4 .x5, .subImm .x .x8 .x7 1, .logic .eor .x .x6 .x6 .x8, .logic .and .x .x4 .x4 .x6,
        .logic .orr .x .x4 .x4 .x9, sth .x4 kFlag, ldh .x3 kV, .lsl .x .x3 .x3 1, sth .x3 kV, ldh .x3 kBits,
        .subImm .x .x3 .x3 1, sth .x3 kBits]] : List (Prog isa))))) := rfl

/-- `mrExpBit`: `y := y² b^bt`, the flag, `kV := 2 kV` and `x3 := kBits := kBits − 1`. -/
theorem mrExpBit_ok (M : Mont) {s : State} {B : Addr} {Z w c b y : Nat}
    (hc : MrCtx s B Z w c (b * 2 ^ (64 * w) % c)) (_hw4 : 4 ≤ w) (hw64 : w ≤ 64) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % c)
    {V : BitVec 64} {bt P : Bool} {n : Nat} (hV : word s.mem B (8 * kV) = V)
    (hbt : V >>> 63 = BitVec.ofNat 64 bt.toNat) (hP : word s.mem B (8 * kFlag) = mask P)
    (hnb : word s.mem B (8 * kBits) = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hn' : n < 2 ^ 64) :
    WP isa (seqs (mrExpBit M.mm)) s fun t =>
      MrCtx t B Z w c (b * 2 ^ (64 * w) % c) ∧
      wv t.mem B (slot w aY) w = (y * y % c * (if bt then b else 1) % c) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (if bt then
          decide (y * y % c * (if bt then b else 1) % c = 1) || decide (y * y % c * (if bt then b else 1) % c = c - 1)
        else P || decide (y * y % c * (if bt then b else 1) % c = c - 1)) ∧
      word t.mem B (8 * kV) = V + V ∧ word t.mem B (8 * kBits) = BitVec.ofNat 64 (n - 1) ∧
      t.gpr .x3 = BitVec.ofNat 64 (n - 1) ∧ Frm B (bitRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have hZ8 := hc.good.2
  rw [mrExpBit_eq]
  refine wp_seqs_append (by simp) (by simp [eqMask, eqA]) ?_
  refine WP.mono (mrMul_ok M hc hw64 hodd hc1 hY hV hbt) fun s₄ ⟨hc₄, hY₄, f₄, k₄⟩ => ?_
  generalize hz : y * y % c * (if bt then b else 1) % c = z at hY₄ ⊢
  have hlt : z < c := hz ▸ Nat.mod_lt _ hc0
  have hhd₄ : ∀ i < 32, word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    f₄.word_eq (fun r hr => by
      simp only [mulRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Or.inl (hdr_lt_slot w _ hi)) (by omega)
  -- `y = c − 1`, into `kG`.
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) ?_
  refine WP.mono (eqMask_ok hc₄.ws (j := aRm1) (by decide)) fun s₅ ⟨h15₅, hm₅, k₅⟩ => ?_
  rw [hY₄, hc₄.rm1, decide_eq_decide.mpr (mont_eq_m1 hR hc1 hlt)] at h15₅
  refine wp_seqs_append (by simp) (by simp [eqMask, eqA]) ?_
  have h0₅ : s₅.gpr .x0 = B := (k₅.gpr .x0 (by decide)).trans hc₄.ws.x0
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₅.mem.writeW (off B (8 * kG)) (s₅.gpr .x15)) (by
    brun [h0₅, hdr_enc (show kG < 32 by decide), (hc₄.ws.scr.congr k₅.wr).st (d := 8 * kG)
      (by have := hdr_lt_slot w 8 (show kG < 32 by decide); omega)]) (by decide) (by decide) (by decide +kernel))
    fun s₆ ⟨hm₆, k₆⟩ => ?_
  rw [h15₅, hm₅] at hm₆
  have f₆ : Frm B (bitRanges w) s₄.mem s₆.mem := by
    rw [hm₆]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kG) (by decide)) (by simp [bitRanges])
  have hc₆ := hc₄.of_bit f₆ (fun _ h => h) (k₅.trans k₆) (by decide)
  have hY₆ : wv s₆.mem B (slot w aY) w = z * 2 ^ (64 * w) % c := by
    rw [hm₆, hdrStore_wv _ _ _ (by decide) (by decide) (by omega)]; exact hY₄
  -- `y = 1`, then the flag.
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) ?_
  refine WP.mono (eqMask_ok hc₆.ws (j := aR1) (by decide)) fun s₇ ⟨h15₇, hm₇, k₇⟩ => ?_
  rw [hY₆, hc₆.r1, decide_eq_decide.mpr (mont_eq_one hR hc1 hlt)] at h15₇
  have hc₇ := hc₆.of_bit (rs := []) (fun x _ => by rw [hm₇]) (by simp) k₇ (by decide)
  have hhd₇ : ∀ i < 32, i ≠ kG → word s₇.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hne => by
    rw [hm₇, hm₆, hdrStore_hdr _ _ _ (by decide) hi (Ne.symm hne), hhd₄ i hi]
  have hG₇ : word s₇.mem B (8 * kG) = mask (decide (z = c - 1)) := by rw [hm₇, hm₆, word_writeW_self]
  simp only [seqs]
  refine WP.mono (bitTail_ok hc₇.ws (V := V) (bt := bt) (m := decide (z = c - 1)) (e := decide (z = 1)) (P := P) (n := n)
    (by rw [hhd₇ kV (by decide) (by decide)]; exact hV) hbt hG₇ h15₇
    (by rw [hhd₇ kFlag (by decide) (by decide)]; exact hP) (by rw [hhd₇ kBits (by decide) (by decide)]; exact hnb)
    hn1 hn') fun t ⟨⟨hm, h3⟩, k⟩ => ?_
  have ft : Frm B (bitRanges w) s₇.mem t.mem := by
    rw [hm]
    exact ((Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag) (by decide)) (by simp [bitRanges])).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV) (by decide)) (by simp [bitRanges]))).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits) (by decide)) (by simp [bitRanges]))
  refine ⟨hc₇.of_bit ft (fun _ h => h) k (by decide), ?_, ?_, ?_, ?_, h3, ?_,
    ((((k₄.trans k₅).trans k₆).trans k₇).trans k).mono (by decide)⟩
  · rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega), hdrStore_wv _ _ _ (by decide) (by decide) (by omega),
      hdrStore_wv _ _ _ (by decide) (by decide) (by omega), hm₇]
    exact hY₆
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm, word_writeW_self]
  · have f₇ : Frm B (bitRanges w) s₆.mem s₇.mem := fun x _ => by rw [hm₇]
    exact (((f₄.mono (mulRanges_sub w)).trans f₆).trans f₇).trans ft

end VG.Proof.RsaKeyGen.AArch64
