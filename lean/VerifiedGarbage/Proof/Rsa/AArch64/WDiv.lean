module

public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.R2dStep
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.WordDiv
import VerifiedGarbage.Proof.Rsa.WordFactors
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-!
# RSA private keys on AArch64: division by words

`wdiv x m r t` (`wdiv_ok`): `[r] := [x] mod m'` for `m'` the `w_m` words of
`[m]` with the top bit of its top word set (in place), which is `[m]` itself
when that bit is set: `v` for its top word into `[t]` (`recip`), `[r]`
from the top `w_m - 1` words of `[x]`, then for each lower word `u` of `[x]`,
`r := (r 2^64 + u) mod m'` (`R2Div.stepU`, `r2dStepU_ok`), whose values
`WordStep.wordDiv_step` folds.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Setting the top bit makes a word at least `2^63`. -/
theorem or_top (x : BitVec 64) : 2 ^ 63 ≤ (x ||| BitVec.ofNat 64 (2 ^ 63)).toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  exact Nat.right_le_or

/-- A word whose top bit is set is unchanged by setting it. -/
theorem or_top_self (x : BitVec 64) (h : 2 ^ 63 ≤ x.toNat) : x ||| BitVec.ofNat 64 (2 ^ 63) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hi : 63 = i
  · subst i
    have ht := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h x.isLt
    simp only [ht, decide_true, Bool.or_true]
  · simp only [hi, decide_false, Bool.or_false]

/-- `w_m` into `x12` from `w` (`wm`). -/
def WmOk (wmI : List Instr) (w wm : Nat) : Prop :=
  ∀ t : State, t.gpr .x12 = BitVec.ofNat 64 w → WP isa (.block wmI) t fun t' =>
    (t'.gpr .x12 = BitVec.ofNat 64 wm ∧ t'.mem = t.mem) ∧ Keep [.x12] t t'

/-- `L` into `x13` from `w` in `x12` (`lenL`). -/
def LenOk (lenL : List Instr) (w L : Nat) : Prop :=
  ∀ t : State, t.gpr .x12 = BitVec.ofNat 64 w → WP isa (.block lenL) t fun t' =>
    (t'.gpr .x13 = BitVec.ofNat 64 L ∧ t'.mem = t.mem) ∧ Keep [.x13] t t'

/-- The address of `[x]`'s word `-1` into `x16` (`xb`), from `[r]`'s base in
`x11` and `w_m` in `x12`. -/
def XbOk (xb : List Instr) (B : Addr) (eR eX wm : Nat) : Prop :=
  ∀ t : State, t.gpr .x11 = off B eR → t.gpr .x12 = BitVec.ofNat 64 wm → WP isa (.block xb) t fun t' =>
    (t'.gpr .x16 = off B (eX - 8) ∧ t'.mem = t.mem) ∧ Keep [.x16] t t'

/-- `wdivSet`: the top bit of `m'`'s word `w_m - 1` set. -/
theorem wdivSet_ok {s : State} {B : Addr} {Z eM wm : Nat} (hs : Scr s B Z) (h9 : s.gpr .x9 = off B eM)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 wm) (hw : 1 ≤ wm) (hw' : wm < 2 ^ 31) (hM : eM + 8 * wm ≤ Z) :
    WP isa (.block wdivSet) s fun t =>
      (t.mem = s.mem.writeW (off B (eM + 8 * (wm - 1)))
        (word s.mem B (eM + 8 * (wm - 1)) ||| BitVec.ofNat 64 (2 ^ 63))) ∧ Keep [.x3, .x4, .x13] s t := by
  have hn := hs.nowrap
  have ea : BitVec.ofNat 64 (8 * (wm - 1)) + off B eM = off B (eM + 8 * (wm - 1)) := by
    rw [BitVec.add_comm, off_add]
  refine WP.keep [.x3, .x4, .x13] ?_ (by decide) (by decide) (by decide +kernel)
  brun [wdivSet, h9, h12, shl3_sub8 hw (show wm < 2 ^ 61 by omega_arith), ea,
    hs.ld (show eM + 8 * (wm - 1) + 8 ≤ Z by omega_arith), hs.st (show eM + 8 * (wm - 1) + 8 ≤ Z by omega_arith)]
  rfl

theorem bv_sub_ofNat {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- `wdiv`'s first block, after `zeroA`: the bases of `[m]` (`x16`) and `[t]`
(`x6`), `x9 = x17 :=` the temporary's word 1, `w_m`, and `x8 := L - w_m + 1`,
the number of steps. -/
theorem wdivA_ok {s : State} {B : Addr} {w : Nat} (h0 : s.gpr .x0 = B)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    {iM iT : Nat} {wmI lenL : List Instr} {wm L : Nat} (hwm : WmOk wmI w wm) (hL : LenOk lenL w L)
    (hmL : wm ≤ L) (hL' : L < 2 ^ 31) :
    WP isa (.block (base iM .x16 ++ base iT .x6 ++ lenL ++ wmI ++
        ([.sub .x .x8 .x13 .x12, .addImm .x .x8 .x8 1, movi .x7 0, .addImm .x .x9 .x6 8, mov .x17 .x9] : List Instr)))
      s fun t =>
      (t.gpr .x16 = off B (slot w iM) ∧ t.gpr .x6 = off B (slot w iT) ∧ t.gpr .x9 = off B (slot w iT + 8) ∧
        t.gpr .x17 = off B (slot w iT + 8) ∧ t.gpr .x12 = BitVec.ofNat 64 wm ∧
        t.gpr .x8 = BitVec.ofNat 64 (L - wm + 1) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧
      Keep [.x6, .x7, .x8, .x9, .x12, .x13, .x16, .x17] s t := by
  simp only [List.append_assoc]
  rw [← List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (base2_ok iM iT .x16 .x6 h0 h11) fun s₁ ⟨⟨h16, h6, m₁, _⟩, k₁⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (hL s₁ ((k₁.gpr .x12 (by decide)).trans h12)) fun s₂ ⟨⟨h13, m₂⟩, k₂⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (hwm s₂ ((k₂.gpr .x12 (by decide)).trans ((k₁.gpr .x12 (by decide)).trans h12)))
    fun s₃ ⟨⟨h12₃, m₃⟩, k₃⟩ => ?_)
  have e1 : BitVec.ofNat 64 L - BitVec.ofNat 64 wm + BitVec.ofNat 64 1 = BitVec.ofNat 64 (L - wm + 1) := by
    rw [bv_sub_ofNat hmL (by omega_arith), BitVec.ofNat_add]
  have k13 := (k₂.trans k₃)
  refine WP.mono (WP.keep [.x7, .x8, .x9, .x17] (Q := fun t => t.gpr .x8 = BitVec.ofNat 64 (L - wm + 1) ∧
      t.gpr .x7 = 0 ∧ t.gpr .x9 = off B (slot w iT + 8) ∧ t.gpr .x17 = off B (slot w iT + 8) ∧ t.mem = s₃.mem)
    (by brun [(k₃.gpr .x13 (by decide)).trans h13, h12₃, e1, (k13.gpr .x6 (by decide)).trans h6, off_add])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h8, h7, h9, h17, mt⟩, k₄⟩ => ?_
  exact ⟨⟨(k₄.gpr .x16 (by decide)).trans ((k13.gpr .x16 (by decide)).trans h16),
    (k₄.gpr .x6 (by decide)).trans ((k13.gpr .x6 (by decide)).trans h6), h9, h17,
    (k₄.gpr .x12 (by decide)).trans h12₃, h8, h7, by rw [mt, m₃, m₂, m₁]⟩, ((k₁.trans k13).trans k₄).mono (by decide)⟩

/-- `wdiv`'s copy setup: `x16 :=` the address of `[x]`'s word `S`, `x17 :=`
`[r]`'s base and `x12 := w_m - 1`. -/
theorem wdivB_ok {s : State} {B : Addr} {w : Nat} (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) {iX iR S wm : Nat} (h8 : s.gpr .x8 = BitVec.ofNat 64 S)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 wm) (hS : S < 2 ^ 31) (hw : 1 ≤ wm) (hw' : wm < 2 ^ 31) :
    WP isa (.block (base iX .x16 ++ ([.lsl .x .x3 .x8 3, .add .x .x16 .x16 .x3] : List Instr) ++ base iR .x17 ++
        ([.subImm .x .x12 .x12 1] : List Instr))) s fun t =>
      (t.gpr .x16 = off B (slot w iX + 8 * S) ∧ t.gpr .x17 = off B (slot w iR) ∧
        t.gpr .x12 = BitVec.ofNat 64 (wm - 1) ∧ t.mem = s.mem) ∧ Keep [.x3, .x12, .x16, .x17] s t := by
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (base_ok iX .x16 h0 h11) fun s₁ ⟨⟨h16, m₁, _⟩, k₁⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x16] (Q := fun t => t.gpr .x16 = off B (slot w iX + 8 * S) ∧
      t.mem = s₁.mem) (by brun [h16, (k₁.gpr .x8 (by decide)).trans h8, r2d_ofNat_shl3 (show S < 2 ^ 61 by omega_arith),
        off_add]) (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨h16₂, m₂⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (base_ok iR .x17 ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h17, m₃, _⟩, k₃⟩ => ?_)
  refine WP.mono (WP.keep [.x12] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 (wm - 1) ∧ t.mem = s₃.mem)
    (by brun [((k12.trans k₃).gpr .x12 (by decide)).trans h12, bv_sub_ofNat hw (by omega_arith)]) (by decide)
    (by decide) (by decide +kernel)) fun t ⟨⟨h12', mt⟩, k₄⟩ => ?_
  exact ⟨⟨(k₄.gpr .x16 (by decide)).trans ((k₃.gpr .x16 (by decide)).trans h16₂), (k₄.gpr .x17 (by decide)).trans h17,
    h12', by rw [mt, m₃, m₂, m₁]⟩, ((k12.trans k₃).trans k₄).mono (by decide)⟩

/-- `wdiv`'s step registers: `x11 :=` `[r]`'s base, `x12 := w_m`. -/
theorem wdivC_ok {s : State} {B : Addr} {w : Nat} (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) {iR wm : Nat} (h12 : s.gpr .x12 = BitVec.ofNat 64 (wm - 1))
    (hw : 1 ≤ wm) :
    WP isa (.block (base iR .x16 ++ ([mov .x11 .x16, .addImm .x .x12 .x12 1] : List Instr))) s fun t =>
      (t.gpr .x11 = off B (slot w iR) ∧ t.gpr .x12 = BitVec.ofNat 64 wm ∧ t.mem = s.mem) ∧
      Keep [.x11, .x12, .x16] s t := by
  refine WP.block_append_iff.mpr (WP.mono (base_ok iR .x16 h0 h11) fun s₁ ⟨⟨h16, m₁, _⟩, k₁⟩ => ?_)
  have e : BitVec.ofNat 64 (wm - 1) + 1#64 = BitVec.ofNat 64 wm := by
    rw [show (1#64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add, Nat.sub_add_cancel hw]
  refine WP.mono (WP.keep [.x11, .x12] (Q := fun t => t.gpr .x11 = off B (slot w iR) ∧
      t.gpr .x12 = BitVec.ofNat 64 wm ∧ t.mem = s₁.mem)
    (by brun [h16, (k₁.gpr .x12 (by decide)).trans h12, e]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h11', h12', mt⟩, k₂⟩ => ⟨⟨h11', h12', by rw [mt, m₁]⟩, (k₁.trans k₂).mono (by decide)⟩

/-- The registers `wdiv` writes. -/
abbrev wdRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- After `j` of `wdiv`'s steps, from `s₀` (`wdiv`'s start), for `[x]` of
`L` words with value `X` and `m'` (`w_m` words, normalized) with value `M`:
`r = ⌊X / 2^(64 (S - j))⌋ mod M` over `w_m + 1` words, for
`S = L - w_m + 1` steps, and the words of `[r]` above them zero. -/
structure WdInv (s₀ : State) (B : Addr) (Z w iX iR iT wm L X M : Nat) (j : Nat) (t : State) : Prop where
  ws : Ws t B Z w
  x9 : t.gpr .x9 = off B (slot w iT + 8)
  x11 : t.gpr .x11 = off B (slot w iR)
  x6 : t.gpr .x6 = off B (slot w iT)
  x12 : t.gpr .x12 = BitVec.ofNat 64 wm
  x7 : t.gpr .x7 = 0
  frm : Frm B [ar w iR, ar w iT] s₀.mem t.mem
  keep : Keep wdRegs s₀ t
  m : wv t.mem B (slot w iT + 8) wm = M
  top : 2 ^ 63 ≤ (word t.mem B (slot w iT + 8 + 8 * (wm - 1))).toNat
  v : (word t.mem B (slot w iT)).toNat = (2 ^ 128 - 1) / (word t.mem B (slot w iT + 8 + 8 * (wm - 1))).toNat - 2 ^ 64
  x : wv t.mem B (slot w iX) L = X
  hi : ∀ i, wm + 1 ≤ i → i < w + 2 → word t.mem B (slot w iR + 8 * i) = 0
  val : wv t.mem B (slot w iR) (wm + 1) = X / 2 ^ (64 * (L - wm + 1 - j)) % M

/-- A step of `wdiv`'s loop. -/
theorem wdivBody_ok {s₀ t : State} {B : Addr} {Z w iX iR iT wm L X M j : Nat}
    (hI : WdInv s₀ B Z w iX iR iT wm L X M j t) (hj : j < L - wm + 1)
    (h8 : t.gpr .x8 = BitVec.ofNat 64 (L - wm + 1 - j)) {xb : List Instr}
    (hxb : XbOk xb B (slot w iR) (slot w iX) wm)
    (hX : iX < 16) (hR : iR < 16) (hT : iT < 16) (dXR : iX ≠ iR) (dRT : iR ≠ iT)
    (h3 : 3 ≤ wm) (hwm' : wm + 1 ≤ w + 1) (hLw : L ≤ w + 2) (hmL : wm ≤ L) :
    WP isa (seqs [.block (xb ++ ([.lsl .x .x3 .x8 3, .add .x .x16 .x16 .x3, ld .x10 .x16] : List Instr)),
        R2Div.stepU, .block [.subImm .x .x8 .x8 1]]) t fun t' =>
      WdInv s₀ B Z w iX iR iT wm L X M (j + 1) t' ∧ t'.gpr .x8 = t.gpr .x8 - BitVec.ofNat 64 1 := by
  have h := hI.ws
  have hn := h.scr.nowrap
  have w2 := h.w2
  have sX := h.sl hX
  have sR := h.sl hR
  have sT := h.sl hT
  have pXR := slot_sep (w := w) dXR
  have pRT := slot_sep (w := w) dRT
  have h8X : 8 ≤ slot w iX := by have := hdr_lt_slot w iX (show 0 < 32 by decide); omega_arith
  have h8M : 8 ≤ slot w iT + 8 := by omega_arith
  have h8R : 8 ≤ slot w iR := by have := hdr_lt_slot w iR (show 0 < 32 by decide); omega_arith
  have hM0 : 0 < M := by
    rw [← hI.m, wv_split1 _ _ _ (by omega_arith : 1 ≤ wm)]
    have := Nat.le_mul_of_pos_right (word t.mem B (slot w iT + 8 + 8 * (wm - 1))).toNat
      (Nat.two_pow_pos (64 * (wm - 1)))
    have := hI.top
    omega_arith
  generalize hk : L - wm + 1 - j - 1 = k
  have hk1 : L - wm + 1 - j = k + 1 := by omega_arith
  rw [hk1] at h8
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (hxb t hI.x11 hI.x12) fun t₀ ⟨⟨h16, m₀⟩, k₀⟩ => ?_))
  have e : off B (slot w iX - 8) + BitVec.ofNat 64 (8 * (k + 1)) = off B (slot w iX + 8 * k) := by
    rw [off_add]; congr 1; omega_arith
  refine WP.mono (WP.keep [.x3, .x10, .x16] (Q := fun t₁ => t₁.gpr .x10 = word t.mem B (slot w iX + 8 * k) ∧
      t₁.mem = t.mem) (by
        brun [h16, (k₀.gpr .x8 (by decide)).trans h8, r2d_ofNat_shl3 (show k + 1 < 2 ^ 61 by omega_arith), e,
          (h.scr.congr k₀.wr).ld (show slot w iX + 8 * k + 8 ≤ Z by omega_arith), m₀])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h10, m₁⟩, k₁'⟩ => ?_
  have k₁ := k₀.trans k₁'
  -- `r` below `M` over `w_m` words.
  have hRlt : wv t.mem B (slot w iR) (wm + 1) < M := by rw [hI.val]; exact Nat.mod_lt _ hM0
  have hRw : wv t.mem B (slot w iR) wm = wv t.mem B (slot w iR) (wm + 1) := by
    refine wv_low_top _ _ _ _ (Nat.lt_of_lt_of_le hRlt ?_)
    rw [← hI.m]; exact Nat.le_of_lt (wv_lt _ _ _ _)
  have hs₁ := h.scr.congr k₁.wr
  refine WP.seq (WP.mono (r2dStepU_ok (eX := slot w iR) (eM := slot w iT + 8) (eV := slot w iT) hs₁
    ((k₁.gpr .x11 (by decide)).trans hI.x11) ((k₁.gpr .x9 (by decide)).trans hI.x9)
    ((k₁.gpr .x12 (by decide)).trans hI.x12) ((k₁.gpr .x6 (by decide)).trans hI.x6)
    ((k₁.gpr .x7 (by decide)).trans hI.x7) h3 (by omega_arith) h8R h8M (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by rw [m₁]; exact hI.top) (by rw [m₁]; exact hI.v)
    (by rw [m₁, hRw, hI.m]; exact hRlt)) fun t₂ ⟨hv₂, o₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  rw [m₁] at o₂ hv₂
  refine WP.mono (dec_ok t₂ .x8) fun t' ⟨⟨h8', m', _⟩, k'⟩ => ⟨?_, by rw [h8', k12.gpr .x8 (by decide)]⟩
  have k13 := k12.trans k'
  have oR : ∀ {d : Nat}, d + 8 ≤ slot w iR ∨ slot w iR + 8 * (w + 2) ≤ d → d + 8 ≤ 2 ^ 64 →
      word t'.mem B d = word t.mem B d := fun hd hd' => by rw [m']; exact o₂.word (by omega_arith) hd'
  have oRv : ∀ {d n : Nat}, d + 8 * n ≤ slot w iR ∨ slot w iR + 8 * (w + 2) ≤ d → d + 8 * n ≤ 2 ^ 64 →
      wv t'.mem B d n = wv t.mem B d n := fun hd hd' => by rw [m']; exact o₂.wv (by omega_arith) hd'
  have f₂ : Frm B [ar w iR, ar w iT] t.mem t'.mem := by
    rw [m']
    exact Frm.of_outside (o₂.mono (o' := slot w iR) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp [ar])
  refine ⟨h.congr f₂ (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Mut.ofSlot _ _ _) k13 (by decide),
    (k13.gpr .x9 (by decide)).trans hI.x9, (k13.gpr .x11 (by decide)).trans hI.x11,
    (k13.gpr .x6 (by decide)).trans hI.x6, (k13.gpr .x12 (by decide)).trans hI.x12,
    (k13.gpr .x7 (by decide)).trans hI.x7, hI.frm.trans f₂, (hI.keep.trans k13).mono (by decide),
    by rw [oRv (by omega_arith) (by omega_arith), hI.m],
    by rw [oR (by omega_arith) (by omega_arith)]; exact hI.top,
    by rw [oR (by omega_arith) (by omega_arith), oR (by omega_arith) (by omega_arith)]; exact hI.v,
    by rw [oRv (by omega_arith) (by omega_arith)]; exact hI.x,
    fun i hi hi' => by rw [m', o₂.word (by omega_arith) (by omega_arith)]; exact hI.hi i hi hi', ?_⟩
  -- The value.
  have hu : (word t.mem B (slot w iX + 8 * k)).toNat = X / 2 ^ (64 * k) % 2 ^ 64 := by
    rw [word_of_wv t.mem B (slot w iX) L (show k < L by omega_arith), hI.x]
  rw [m', hv₂, h10, hu, hRw, hI.m, hI.val, hk1]
  rw [show L - wm + 1 - (j + 1) = k by omega_arith]
  exact WordStep.wordDiv_step X M 64 k

/-- The top `n` words of `L = S + n` words. -/
theorem wv_hi_div (m : Mem) (B : Addr) (e S n : Nat) :
    wv m B (e + 8 * S) n = wv m B e (S + n) / 2 ^ (64 * S) := by
  rw [wv_add, Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (wv_lt _ _ _ _),
    Nat.zero_add]

/-- `wdiv`: `[r] := [x] mod m'` over `w + 2` words, for `[x]` of `L` words
(`lenL`) and `m'` the `w_m` words of `[m]` (`wmI`) with the top bit of its
top word set, in the temporary `[t]`: `[x] mod [m]` when that bit is set. -/
theorem wdiv_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {iX iM iR iT : Nat}
    (hX : iX < 16) (hM : iM < 16) (hR : iR < 16) (hT : iT < 16) (dXR : iX ≠ iR) (dXT : iX ≠ iT)
    (dMR : iM ≠ iR) (dMT : iM ≠ iT) (dRT : iR ≠ iT)
    {wmI lenL xb : List Instr} {wm L : Nat} (hwm : WmOk wmI w wm) (hL : LenOk lenL w L)
    (hxb : XbOk xb B (slot w iR) (slot w iX) wm) (h3 : 3 ≤ wm) (hww : wm ≤ w) (hLw : L ≤ w + 2) (hmL : wm ≤ L) :
    WP isa (wdiv iX iM iR iT wmI lenL xb) s fun t =>
      t.gpr .x0 = B ∧ Frm B [ar w iR, ar w iT] s.mem t.mem ∧ Keep wdRegs s t ∧
      (2 ^ 63 ≤ (word s.mem B (slot w iM + 8 * (wm - 1))).toNat →
        wv t.mem B (slot w iR) (w + 2) = wv s.mem B (slot w iX) L % wv s.mem B (slot w iM) wm) := by
  have hn := h.scr.nowrap
  have w2 := h.w2
  have sX := h.sl hX
  have sM := h.sl hM
  have sR := h.sl hR
  have sT := h.sl hT
  have pXR := slot_sep (w := w) dXR
  have pXT := slot_sep (w := w) dXT
  have pMR := slot_sep (w := w) dMR
  have pMT := slot_sep (w := w) dMT
  have pRT := slot_sep (w := w) dRT
  have h8X : 8 ≤ slot w iX := by have := hdr_lt_slot w iX (show 0 < 32 by decide); omega_arith
  have mutA : ∀ r ∈ [ar w iR, ar w iT], Mut r := fun r hr => by
    simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Mut.ofSlot _ _ _
  have frmOf : ∀ {m m' : Mem} {o n j : Nat}, j = iR ∨ j = iT → Outside B o n m m' → slot w j ≤ o →
      o + n ≤ slot w j + 8 * (w + 2) → Frm B [ar w iR, ar w iT] m m' := fun {m m' o n j} hj ho h1 h2 =>
    Frm.of_outside (ho.mono (o' := slot w j) (n' := 8 * (w + 2)) h1 h2) (by
      rcases hj with rfl | rfl <;> simp [ar])
  have eT : slot w iT + 8 + 8 * (wm - 1) = slot w iT + 8 * wm := by omega_arith
  unfold wdiv
  simp only [seqs]
  -- `[r] := 0`.
  refine WP.seq (WP.mono (zeroA_ok h hR) fun s₁ ⟨hz₁, o₁, h12₁, h11₁, _, k₁⟩ => ?_)
  have f₁ := frmOf (.inl rfl) o₁ (Nat.le_refl _) (Nat.le_refl _)
  have g₁ := h.congr f₁ mutA k₁ (by decide)
  -- The bases, `w_m` and the count.
  refine WP.seq (WP.mono (wdivA_ok (iM := iM) (iT := iT) g₁.x0 h12₁ h11₁ hwm hL hmL (by omega_arith))
    fun s₂ ⟨⟨h16₂, h6₂, h9₂, h17₂, h12₂, h8₂, h7₂, m₂⟩, k₂⟩ => ?_)
  have g₂ := g₁.congr (rs := []) (by rw [m₂]; exact Frm.refl _ _ _) (by simp) k₂ (by decide)
  -- `m` to the temporary's words 1 to `w_m`.
  refine WP.seq (WP.mono (copyWords_ok h16₂ h17₂ h12₂ (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi => g₂.scr.ld (by omega_arith)) (fun i hi => g₂.scr.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun s₃ ⟨hc₃, _, o₃, _, _, k₃⟩ => ?_)
  have f₃ := frmOf (.inr rfl) o₃ (by omega_arith) (by omega_arith)
  have g₃ := g₂.congr f₃ mutA k₃ (by decide)
  have k23 := k₂.trans k₃
  -- Its top bit set.
  refine WP.seq (WP.mono (wdivSet_ok g₃.scr ((k₃.gpr .x9 (by decide)).trans h9₂) ((k₃.gpr .x12 (by decide)).trans h12₂)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₄ ⟨m₄, k₄⟩ => ?_)
  have o₄ : Outside B (slot w iT + 8 + 8 * (wm - 1)) 8 s₃.mem s₄.mem := by
    rw [m₄]; exact writeW_outside _ _ _ (by omega_arith)
  have f₄ := frmOf (.inr rfl) o₄ (by omega_arith) (by omega_arith)
  have g₄ := g₃.congr f₄ mutA k₄ (by decide)
  have top₄ : word s₄.mem B (slot w iT + 8 + 8 * (wm - 1)) =
      (word s₃.mem B (slot w iT + 8 + 8 * (wm - 1)) ||| BitVec.ofNat 64 (2 ^ 63)) := by
    rw [m₄, word_writeW_self]
  have k24 := k23.trans k₄
  have j4 := k₃.trans k₄
  -- `v`.
  refine WP.seq (WP.mono (r2dRecip_ok (eM := slot w iT + 8) (eV := slot w iT) g₄.scr ((j4.gpr .x9 (by decide)).trans h9₂)
    ((j4.gpr .x12 (by decide)).trans h12₂) ((j4.gpr .x6 (by decide)).trans h6₂) ((j4.gpr .x7 (by decide)).trans h7₂)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [top₄]; exact or_top _))
    fun s₅ ⟨hv₅, o₅, k₅⟩ => ?_)
  have f₅ := frmOf (.inr rfl) o₅ (Nat.le_refl _) (by omega_arith)
  have g₅ := g₄.congr f₅ mutA k₅ (by decide)
  have k25 := k24.trans k₅
  have j5 := j4.trans k₅
  -- The top `w_m - 1` words of `[x]` to `[r]`.
  refine WP.seq (WP.mono (wdivB_ok (iX := iX) (iR := iR) g₅.x0 ((k25.gpr .x11 (by decide)).trans h11₁)
    ((j5.gpr .x8 (by decide)).trans h8₂) ((j5.gpr .x12 (by decide)).trans h12₂) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₆ ⟨⟨h16₆, h17₆, h12₆, m₆⟩, k₆⟩ => ?_)
  have g₆ := g₅.congr (rs := []) (by rw [m₆]; exact Frm.refl _ _ _) (by simp) k₆ (by decide)
  refine WP.seq (WP.mono (copyWords_ok h16₆ h17₆ h12₆ (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi => g₆.scr.ld (by omega_arith)) (fun i hi => g₆.scr.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun s₇ ⟨hc₇, _, o₇, _, _, k₇⟩ => ?_)
  have f₇ := frmOf (.inl rfl) o₇ (Nat.le_refl _) (by omega_arith)
  have g₇ := g₆.congr f₇ mutA k₇ (by decide)
  have k27 := (k25.trans k₆).trans k₇
  -- The step's registers.
  refine WP.seq (WP.mono (wdivC_ok (iR := iR) g₇.x0 ((k27.gpr .x11 (by decide)).trans h11₁)
    ((k₇.gpr .x12 (by decide)).trans h12₆) (by omega_arith)) fun s₈ ⟨⟨h11₈, h12₈, m₈⟩, k₈⟩ => ?_)
  have g₈ := g₇.congr (rs := []) (by rw [m₈]; exact Frm.refl _ _ _) (by simp) k₈ (by decide)
  have k28 := k27.trans k₈
  have mm86 : s₈.mem = s₇.mem := m₈
  have f₁₈ : Frm B [ar w iR, ar w iT] s.mem s₈.mem := by
    rw [m₈]
    exact (((((f₁.trans (by rw [m₂]; exact Frm.refl _ _ _)).trans f₃).trans f₄).trans f₅).trans
      (by rw [m₆]; exact Frm.refl _ _ _)).trans f₇
  -- What the setup leaves.
  have eX₈ : wv s₈.mem B (slot w iX) L = wv s.mem B (slot w iX) L :=
    f₁₈.wv_eq (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  have tw : ∀ i < wm, word s₈.mem B (slot w iT + 8 + 8 * i) =
      if i = wm - 1 then word s.mem B (slot w iM + 8 * i) ||| BitVec.ofNat 64 (2 ^ 63)
      else word s.mem B (slot w iM + 8 * i) := by
    intro i hi
    have e3 : word s₃.mem B (slot w iT + 8 + 8 * i) = word s.mem B (slot w iM + 8 * i) := by
      rw [show slot w iT + 8 + 8 * i = slot w iT + 8 + 8 * i from rfl]
      have := ‹∀ i < wm, word s₃.mem B (slot w iT + 8 + 8 * i) = word s₂.mem B (slot w iM + 8 * i)› i hi
      rw [this, m₂, o₁.word (by omega_arith) (by omega_arith)]
    rw [m₈, o₇.word (by omega_arith) (by omega_arith), m₆, o₅.word (by omega_arith) (by omega_arith)]
    split
    · rename_i he; subst he; rw [top₄, e3]
    · rw [o₄.word (by omega_arith) (by omega_arith), e3]
  have j8 := ((j5.trans k₆).trans k₇).trans k₈
  have top₈ : 2 ^ 63 ≤ (word s₈.mem B (slot w iT + 8 + 8 * (wm - 1))).toNat := by
    rw [tw (wm - 1) (by omega_arith), ite_eq_left rfl]; exact or_top _
  have v₈ : (word s₈.mem B (slot w iT)).toNat =
      (2 ^ 128 - 1) / (word s₈.mem B (slot w iT + 8 + 8 * (wm - 1))).toNat - 2 ^ 64 := by
    have e1 : word s₈.mem B (slot w iT) = word s₅.mem B (slot w iT) := by
      rw [m₈, o₇.word (by omega_arith) (by omega_arith), m₆]
    have e2 : word s₈.mem B (slot w iT + 8 + 8 * (wm - 1)) = word s₄.mem B (slot w iT + 8 + 8 * (wm - 1)) := by
      rw [m₈, o₇.word (by omega_arith) (by omega_arith), m₆, o₅.word (by omega_arith) (by omega_arith)]
    rw [e1, hv₅, e2]
  -- `[r]`: the top `w_m - 1` words of `X`, then zeros.
  have z₁ := (wv_eq_zero_iff s₁.mem B (slot w iR) (w + 2)).mp hz₁
  have hi₈ : ∀ i, wm - 1 ≤ i → i < w + 2 → word s₈.mem B (slot w iR + 8 * i) = 0 := fun i hi hi' => by
    rw [m₈, o₇.word (by omega_arith) (by omega_arith), m₆, o₅.word (by omega_arith) (by omega_arith),
      o₄.word (by omega_arith) (by omega_arith), o₃.word (by omega_arith) (by omega_arith), m₂]
    exact z₁ i hi'
  have eX₆ : wv s₆.mem B (slot w iX + 8 * (L - wm + 1)) (wm - 1) = wv s.mem B (slot w iX) L / 2 ^ (64 * (L - wm + 1)) := by
    rw [wv_hi_div, show L - wm + 1 + (wm - 1) = L by omega_arith]
    exact congrArg (· / _) ((((((f₁.trans (by rw [m₂]; exact Frm.refl _ _ _)).trans f₃).trans f₄).trans f₅).trans
      (by rw [m₆]; exact Frm.refl _ _ _)).wv_eq (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith))
  generalize hMv : wv s₈.mem B (slot w iT + 8) wm = M
  generalize hXv : wv s.mem B (slot w iX) L = X at eX₆ eX₈
  have hMlo : 2 ^ (64 * (wm - 1)) ≤ M := by
    rw [← hMv, wv_split1 _ _ _ (by omega_arith : 1 ≤ wm)]
    have := Nat.le_mul_of_pos_left (2 ^ (64 * (wm - 1))) (Nat.lt_of_lt_of_le (by decide) top₈)
    omega_arith
  have val₈ : wv s₈.mem B (slot w iR) (wm + 1) = X / 2 ^ (64 * (L - wm + 1 - 0)) % M := by
    have e := wv_add s₈.mem B (slot w iR) (wm - 1) 2
    have z : wv s₈.mem B (slot w iR + 8 * (wm - 1)) 2 = 0 := wv_zero fun k hk => by
      rw [show slot w iR + 8 * (wm - 1) + 8 * k = slot w iR + 8 * (wm - 1 + k) by omega_arith]
      exact hi₈ _ (by omega_arith) (by omega_arith)
    rw [show wm - 1 + 2 = wm + 1 by omega_arith, z, Nat.mul_zero, Nat.add_zero] at e
    have hlt : X / 2 ^ (64 * (L - wm + 1)) < 2 ^ (64 * (wm - 1)) := by rw [← eX₆]; exact wv_lt _ _ _ _
    rw [e, m₈, hc₇, eX₆, Nat.sub_zero, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hMlo), Nat.add_zero]
  have I₀ : WdInv s B Z w iX iR iT wm L X M 0 s₈ :=
    ⟨g₈, (j8.gpr .x9 (by decide)).trans h9₂, h11₈, (j8.gpr .x6 (by decide)).trans h6₂, h12₈,
      (j8.gpr .x7 (by decide)).trans h7₂, f₁₈, (k₁.trans k28).mono (by decide), hMv, top₈, v₈, eX₈,
      fun i hi hi' => hi₈ i (by omega_arith) hi', val₈⟩
  have h8₈ : s₈.gpr .x8 = BitVec.ofNat 64 (L - wm + 1) := ((((j5.trans k₆).trans k₇).trans k₈).gpr .x8 (by decide)).trans h8₂
  -- The steps.
  refine WP.mono (wp_countdown (N := L - wm + 1) (by omega_arith) (by omega_arith)
    (WdInv s B Z w iX iR iT wm L X M)
    (fun j hj t hI hc => wdivBody_ok hI hj hc hxb hX hR hT dXR dRT h3 (by omega_arith) hLw hmL) I₀ h8₈)
    fun t hI => ⟨hI.ws.x0, hI.frm, hI.keep, fun htop => ?_⟩
  have hM : M = wv s.mem B (slot w iM) wm := by
    rw [← hMv]
    refine wv_congr2 fun i hi => ?_
    rw [tw i hi]
    split
    · rename_i he; subst he; exact or_top_self _ htop
    · rfl
  have e := wv_add t.mem B (slot w iR) (wm + 1) (w + 2 - (wm + 1))
  have z : wv t.mem B (slot w iR + 8 * (wm + 1)) (w + 2 - (wm + 1)) = 0 := wv_zero fun k hk => by
    rw [show slot w iR + 8 * (wm + 1) + 8 * k = slot w iR + 8 * (wm + 1 + k) by omega_arith]
    exact hI.hi _ (by omega_arith) (by omega_arith)
  rw [show wm + 1 + (w + 2 - (wm + 1)) = w + 2 by omega_arith, z, Nat.mul_zero, Nat.add_zero] at e
  rw [e, hI.val, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one, ← hXv, ← hM, Nat.add_zero]

/-- `x <<< 5`. -/
theorem shl5_ofNat {x : Nat} (hx : x < 2 ^ 58) : BitVec.ofNat 64 x <<< 5 = BitVec.ofNat 64 (32 * x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega_arith : x < 2 ^ 64), Nat.mod_eq_of_lt (by omega_arith : x * 2 ^ 5 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega_arith : 32 * x < 2 ^ 64)]
  omega_arith

/-! ## The guard -/

/-- A byte read as a one-byte value. -/
theorem read_one (m : Mem) (p : Addr) : (m.read p 1).toNat = (m p).toNat := by
  simp only [Mem.read, BitVec.toNat_append]; simp

/-- What `wordGuard` leaves in `x9`, zero exactly when its checks pass. -/
def guardVal (k pl ql : Nat) (b : BitVec (8 * 1)) : BitVec 64 :=
  BitVec.ofNat 64 k &&& BitVec.setWidth 64 15#16 ||| BitVec.ofNat 64 pl + BitVec.ofNat 64 pl ^^^ BitVec.ofNat 64 k |||
    BitVec.ofNat 64 pl ^^^ BitVec.ofNat 64 ql |||
    BitVec.setWidth 64 (BitVec.setWidth 32 b) >>> 7 ^^^ BitVec.setWidth 64 1#16

/-- `wordGuard`, from the lengths `k`, `p_len`, `q_len` in the header and
`n`'s first byte `b`. -/
theorem wordGuard_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 8 * 32 ≤ Z)
    {sPl sQl : Nat} (hP : sPl < 32) (hQ : sQl < 32) {k pl ql : Nat} {pN : Addr} {b : BitVec (8 * 1)}
    (hk : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) (hpl : word s.mem B (8 * sPl) = BitVec.ofNat 64 pl)
    (hql : word s.mem B (8 * sQl) = BitVec.ofNat 64 ql) (hn : word s.mem B (8 * Public.sN) = pN)
    (hb : s.mem.read pN 1 = b) (hrd : InRegions (s.rd ++ s.wr) pN 1)
    (hwo : writesOnly [.x3, .x4, .x9, .x13, .x14, .x15, .x16] (.block (wordGuard sPl sQl)) = true := by decide)
    (hnc : (Code.block (wordGuard sPl sQl) : Prog isa).noCalls = true := by decide)
    (hkv : Code.allInstrs keepsV (.block (wordGuard sPl sQl) : Prog isa) = true := by decide +kernel) :
    WP isa (.block (wordGuard sPl sQl)) s fun t =>
      (t.gpr .x9 = guardVal k pl ql b ∧ t.mem = s.mem) ∧ Keep [.x3, .x4, .x9, .x13, .x14, .x15, .x16] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
  refine WP.keep [.x3, .x4, .x9, .x13, .x14, .x15, .x16] ?_ hwo hnc hkv
  brun [wordGuard, h0, hdr_enc hP, hdr_enc hQ, hdr_enc (show Public.sK < 32 by decide),
    hdr_enc (show Public.sN < 32 by decide), hl _ hP, hl _ hQ, hl Public.sK (by decide), hl Public.sN (by decide),
    hk, hpl, hql, hn, hb, hrd, BitVec.add_zero]
  rfl

/-- A zero `guardVal`: `k = 16 i`, `p_len = q_len = k / 2` and `b ≥ 128`. -/
theorem guard_zero {k pl ql : Nat} {b : BitVec (8 * 1)} (hk : k < 2 ^ 24) (hp : pl < 2 ^ 24) (hq : ql < 2 ^ 24)
    (hg : guardVal k pl ql b = 0) : k % 16 = 0 ∧ 2 * pl = k ∧ pl = ql ∧ 128 ≤ b.toNat := by
  change guardVal k pl ql b = 0#64 at hg
  unfold guardVal at hg
  simp only [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff] at hg
  obtain ⟨⟨⟨hk16, hpk⟩, hpq⟩, hb⟩ := hg
  have e16 := congrArg BitVec.toNat hk16
  have epk := congrArg BitVec.toNat hpk
  have epq := congrArg BitVec.toNat hpq
  have eb := congrArg BitVec.toNat hb
  simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show pl < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show ql < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show pl + pl < 2 ^ 64 by omega_arith),
    show (15#16).toNat = 15 from rfl, show (0#64).toNat = 0 from rfl] at e16 epk epq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show b.toNat < 2 ^ 32 from Nat.lt_trans b.isLt (by decide)),
    Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 from Nat.lt_trans b.isLt (by decide)),
    show (1#16).toNat = 1 from rfl, Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)] at eb
  have hb' := b.isLt
  rw [Nat.mod_eq_of_lt (by decide : 2 ^ 4 - 1 < 2 ^ 64), Nat.and_two_pow_sub_one_eq_mod] at e16
  exact ⟨e16, by omega_arith, epq, by omega_arith⟩

/-- Under the guard, factors of `n` of `p_len = q_len = k / 2` bytes have
their top bits set, as words: `2^(64 m - 1) ≤ P - 1` and `P < 2^(64 m)` for
`m = w / 2` words (`Rsa.balanced_factor`). -/
theorem guard_factors {k pl ql : Nat} {nb pb qb : List Byte} (hnl : nb.length = k) (hk : 1 ≤ k)
    (hpl : pb.length = pl) (hql : qb.length = ql) (h16 : k % 16 = 0) (h2 : 2 * pl = k) (hpq : pl = ql)
    (hb : 128 ≤ (nb[0]'(by omega_arith)).toNat)
    (he : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb) :
    (2 ^ (64 * (wk k / 2) - 1) ≤ Spec.Rsa.os2ip pb - 1 ∧ Spec.Rsa.os2ip pb < 2 ^ (64 * (wk k / 2))) ∧
    (2 ^ (64 * (wk k / 2) - 1) ≤ Spec.Rsa.os2ip qb - 1 ∧ Spec.Rsa.os2ip qb < 2 ^ (64 * (wk k / 2))) := by
  have ep : 8 * pl = 64 * (wk k / 2) := by unfold wk; omega_arith
  have pb' := os2ip_lt pb
  have qb' := os2ip_lt qb
  rw [hpl, pow256_eq, ep] at pb'
  rw [hql, ← hpq, pow256_eq, ep] at qb'
  have nb' := Rsa.os2ip_high (bs := nb) (by omega_arith) hb
  rw [hnl, show 8 * k - 1 = 2 * (64 * (wk k / 2)) - 1 by unfold wk; omega_arith] at nb'
  have fb := Rsa.balanced_factor (b := 64 * (wk k / 2)) (by unfold wk; omega_arith) pb' qb' nb' he
  exact ⟨⟨fb.1, pb'⟩, fb.2, qb'⟩

/-- The top word of `V`, `2^(64 m - 1) ≤ V < 2^(64 m)`, is at least `2^63`. -/
theorem top_word_of {V m : Nat} (hm : 1 ≤ m) (lo : 2 ^ (64 * m - 1) ≤ V) (hi : V < 2 ^ (64 * m)) :
    2 ^ 63 ≤ V / 2 ^ (64 * (m - 1)) % 2 ^ 64 := by
  have e1 : 2 ^ (64 * m - 1) = 2 ^ 63 * 2 ^ (64 * (m - 1)) := by rw [← Nat.pow_add]; congr 1; omega_arith
  have e2 : 2 ^ (64 * m) = 2 ^ 64 * 2 ^ (64 * (m - 1)) := by rw [← Nat.pow_add]; congr 1; omega_arith
  have h1 : 2 ^ 63 ≤ V / 2 ^ (64 * (m - 1)) := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [← e1]; exact lo)
  have h2 : V / 2 ^ (64 * (m - 1)) < 2 ^ 64 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by rw [← e2]; exact hi)
  rw [Nat.mod_eq_of_lt h2]; exact h1

end VG.Proof.Rsa.AArch64
