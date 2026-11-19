module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT
meta import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxLazy8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxLazy8
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Bignum.X86_64.OpAt
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
meta import VerifiedGarbage.Proof.Bignum.X86_64.OpAt
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Bignum.X86_64.AdxLazy8`, which only this module used -/

section

/-!
# The lazy final subtraction, eight words at a time

`lazy8V_ok`: for `T < R + m` in `aTmp`, `lazy8 o` leaves in `o` a number
below `R` congruent to `T` modulo `m`. An iteration's group of four words
masks them (`maskWords_ok`) and subtracts them (`lst_ok`, for any word,
composed by induction), with the borrow in the carry flag (`Lc`) within the
group and in `rbp` between groups (`Lr`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- The words of `m` the mask lets through: `m`'s if the mask is set, none otherwise. -/
def mv (m : Mem) (B : Addr) (eN : Nat) (bit : Bool) (n : Nat) : Nat := if bit then wv m B eN n else 0

theorem mask_and (bit : Bool) (x : BitVec 64) :
    (mask bit &&& x).toNat = if bit then x.toNat else 0 := by
  cases bit
  · simp [mask_false]
  · rw [mask_true, BitVec.allOnes_and]; rfl

theorem mv_succ (m : Mem) (B : Addr) (eN : Nat) (bit : Bool) (n : Nat) :
    mv m B eN bit (n + 1) = mv m B eN bit n +
      2 ^ (64 * n) * (if bit then (word m B (eN + 8 * n)).toNat else 0) := by
  cases bit <;> simp [mv, wv]

/-- The registers a group changes. -/
def lazyRegs : List Reg := [.rax, .rbp, .rcx, .rdx, .r9, .r11]

/-- Within a group: `n` words of `T - (m ∧ mask)` at `eo`, the borrow in the
carry flag. -/
structure Lc (s₀ : State) (B : Addr) (Z eT eN eo : Nat) (bit : Bool) (n : Nat) (t : State) : Prop where
  scr : Scr t B Z
  out : Outside B eo (8 * n) s₀.mem t.mem
  val : ∃ c : Bool, t.cf = some c ∧
    wv t.mem B eo n + mv s₀.mem B eN bit n = wv s₀.mem B eT n + 2 ^ (64 * n) * c.toNat

/-- Word `n = 8 i + d` of `T - (m ∧ mask)`, the masked word of `m` in `r`. -/
theorem lst_ok {s₀ t : State} {B : Addr} {Z eT eN eo i d n : Nat} {bit : Bool} {r : Reg}
    (hr : r ≠ .rax) (hnd : n = 8 * i + d)
    (h8 : t.gpr .r8 = off B eT) (hbx : t.gpr .rbx = off B eo)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 (8 * i))
    (hm : (t.gpr r).toNat = if bit then (word s₀.mem B (eN + 8 * n)).toNat else 0)
    (hI : Lc s₀ B Z eT eN eo bit n t)
    (hT : eT + 8 * n + 8 ≤ Z) (ho : eo + 8 * n + 8 ≤ Z)
    (sT : eo + 8 * n + 8 ≤ eT ∨ eT + 8 * n + 8 ≤ eo) :
    WP isa (.block [.mov .rax (.mem (ix .r8 .r14 (8 * d))), .alu .sbb .rax (.reg r),
        .store (ix .rbx .r14 (8 * d)) .rax]) t fun t' =>
      Lc s₀ B Z eT eN eo bit (n + 1) t' ∧ Keep [.rax] t t' := by
  subst hnd
  have hn := hI.scr.nowrap
  obtain ⟨c, hc, hval⟩ := hI.val
  obtain ea : ∀ e, off B (e + 8 * (8 * i) + 8 * d) = off B (e + 8 * (8 * i + d)) := fun e => by
    congr 1; omega_using []
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.cf = some c' ∧ ∃ v : BitVec 64, t₁.mem = t.mem.writeW (off B (eo + 8 * (8 * i + d))) v ∧
        v.toNat + (t.gpr r).toNat + c.toNat =
          (word t.mem B (eT + 8 * (8 * i + d))).toNat + 2 ^ 64 * c'.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, v, hmem, hv⟩, k₁⟩ => ?_
  · xrun [State.ea, ix, h8, hbx, h14, addrDk, ea, hc, hr, hr.symm, hI.scr.ld hT, hI.scr.st ho]
    exact ⟨_, rfl, sbb_toNat _ _ _⟩
  obtain hx : word t.mem B (eT + 8 * (8 * i + d)) = word s₀.mem B (eT + 8 * (8 * i + d)) :=
    hI.out.word (by omega_using [sT]) (by omega_using [hT, hn])
  rw [hx, hm] at hv
  refine ⟨⟨hI.scr.congr k₁.2.2, ?_, ⟨c', h₁, ?_⟩⟩, k₁⟩
  · rw [hmem]
    intro x hx'
    rw [writeW_outside t.mem B v (by omega_using [ho, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega_using [ho, hn]), mv_succ]
    simp only [wv]
    rw [pow64_succ]
    grind

/-- Between groups: `n` words of `T - (m ∧ mask)` at `eo`, the borrow in `rbp`. -/
structure Lr (s₀ : State) (B : Addr) (Z eT eN eo : Nat) (bit : Bool) (n : Nat) (t : State) : Prop where
  scr : Scr t B Z
  out : Outside B eo (8 * n) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B eo n + mv s₀.mem B eN bit n = wv s₀.mem B eT n + 2 ^ (64 * n) * c.toNat

/-- Words `h`–`h + 3` of `m`, from `n = 8 i + h`, masked. -/
theorem maskWords_ok {t : State} {B : Addr} {Z eN i h : Nat} {bit : Bool} (hs : Scr t B Z)
    (h10 : t.gpr .r10 = off B eN) (h14 : t.gpr .r14 = BitVec.ofNat 64 (8 * i))
    (h13 : t.gpr .r13 = mask bit) (hN : eN + 8 * (8 * i + h + 4) ≤ Z) :
    WP isa (.block ((List.range 4).flatMap (maskWord h))) t fun t' =>
      t'.gpr .rcx = mask bit &&& word t.mem B (eN + 8 * (8 * i + h)) ∧
      t'.gpr .rdx = mask bit &&& word t.mem B (eN + 8 * (8 * i + h + 1)) ∧
      t'.gpr .r9 = mask bit &&& word t.mem B (eN + 8 * (8 * i + h + 2)) ∧
      t'.gpr .r11 = mask bit &&& word t.mem B (eN + 8 * (8 * i + h + 3)) ∧
      t'.mem = t.mem ∧ Keep [.rcx, .rdx, .r9, .r11] t t' := by
  obtain ea : ∀ j, off B (eN + 8 * (8 * i) + 8 * (h + j)) = off B (eN + 8 * (8 * i + h + j)) := fun j => by
    congr 1; omega_using []
  refine WP.mono (WP.keep [.rcx, .rdx, .r9, .r11] (Q := fun t' =>
      t'.gpr .rcx = mask bit &&& word t.mem B (eN + 8 * (8 * i + h)) ∧
      t'.gpr .rdx = mask bit &&& word t.mem B (eN + 8 * (8 * i + h + 1)) ∧
      t'.gpr .r9 = mask bit &&& word t.mem B (eN + 8 * (8 * i + h + 2)) ∧
      t'.gpr .r11 = mask bit &&& word t.mem B (eN + 8 * (8 * i + h + 3)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h', k⟩ => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2, k⟩
  obtain e0 := ea 0
  simp only [Nat.add_zero] at e0
  have hn := hs.nowrap
  rw [show (List.range 4).flatMap (maskWord h) = maskWord h 0 ++ maskWord h 1 ++ maskWord h 2 ++ maskWord h 3
    from rfl]
  simp only [maskWord, lazyReg, List.cons_append, List.nil_append]
  xrun [State.ea, ix, h10, h14, h13, addrDk, e0, ea 1, ea 2, ea 3, Nat.add_zero,
    hs.ld (show eN + 8 * (8 * i + h) + 8 ≤ Z by omega_using [hN]),
    hs.ld (show eN + 8 * (8 * i + h + 1) + 8 ≤ Z by omega_using [hN]),
    hs.ld (show eN + 8 * (8 * i + h + 2) + 8 ≤ Z by omega_using [hN]),
    hs.ld (show eN + 8 * (8 * i + h + 3) + 8 ≤ Z by omega_using [hN])]

/-- A group: words `n = 8 i + h` to `n + 3` of `T - (m ∧ mask)`. -/
theorem group_ok {s₀ t : State} {B : Addr} {Z eT eN eo i h : Nat} {bit : Bool}
    (h8 : t.gpr .r8 = off B eT) (h10 : t.gpr .r10 = off B eN) (hbx : t.gpr .rbx = off B eo)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 (8 * i)) (h13 : t.gpr .r13 = mask bit)
    (hI : Lr s₀ B Z eT eN eo bit (8 * i + h) t)
    (hT : eT + 8 * (8 * i + h + 4) ≤ Z) (hN : eN + 8 * (8 * i + h + 4) ≤ Z) (ho : eo + 8 * (8 * i + h + 4) ≤ Z)
    (sT : eo + 8 * (8 * i + h + 4) ≤ eT ∨ eT + 8 * (8 * i + h + 4) ≤ eo)
    (sN : eo ≤ eN ∨ eN + 8 * (8 * i + h + 4) ≤ eo) :
    WP isa (.block (lazyGroup h)) t fun t' =>
      Lr s₀ B Z eT eN eo bit (8 * i + h + 4) t' ∧ Keep lazyRegs t t' := by
  have hn := hI.scr.nowrap
  obtain ⟨c, hbp, hval⟩ := hI.val
  unfold lazyGroup
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (maskWords_ok hI.scr h10 h14 h13 hN) fun t₁ ⟨m0, m1, m2, m3, hm₁, k₁⟩ => ?_
  -- the masked words, as words of `m` in `s₀`
  obtain mw : ∀ j < 4, word t.mem B (eN + 8 * (8 * i + h + j)) = word s₀.mem B (eN + 8 * (8 * i + h + j)) :=
    fun j hj => hI.out.word (by omega_using [sN, hj]) (by omega_using [hN, hn, hj])
  obtain mv0 := mw 0 (by decide); have mv1 := mw 1 (by decide)
  obtain mv2 := mw 2 (by decide); have mv3 := mw 3 (by decide)
  simp only [Nat.add_zero] at mv0
  rw [mv0] at m0; rw [mv1] at m1; rw [mv2] at m2; rw [mv3] at m3
  refine WP.mono (WP.keep [.rbp] (Q := fun t₂ => t₂.cf = some c ∧ t₂.mem = t₁.mem) (by
    unfold cfFromRbp; xrun [(k₁.gpr (by decide) : t₁.gpr .rbp = t.gpr .rbp), hbp, cf_mask]) rfl)
    fun t₂ ⟨⟨c₂, hm₂⟩, k₂⟩ => ?_
  obtain k12 := k₁.trans k₂
  obtain g : ∀ r, r ∉ [Reg.rcx, .rdx, .r9, .r11, .rbp] → t₂.gpr r = t.gpr r := fun r hr => k12.gpr (by simpa using hr)
  obtain L0 : Lc s₀ B Z eT eN eo bit (8 * i + h) t₂ :=
    ⟨hI.scr.congr k12.2.2, by rw [hm₂, hm₁]; exact hI.out,
      ⟨c, c₂, by rw [hm₂, hm₁]; exact hval⟩⟩
  rw [show (List.range 4).flatMap (lazyWord h) = lazyWord h 0 ++ lazyWord h 1 ++ lazyWord h 2 ++ lazyWord h 3
    from rfl, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  obtain r8 : t₂.gpr .r8 = off B eT := (g .r8 (by decide)).trans h8
  obtain rbx : t₂.gpr .rbx = off B eo := (g .rbx (by decide)).trans hbx
  obtain r14 : t₂.gpr .r14 = BitVec.ofNat 64 (8 * i) := (g .r14 (by decide)).trans h14
  obtain q0 : (t₂.gpr .rcx).toNat = if bit then (word s₀.mem B (eN + 8 * (8 * i + h))).toNat else 0 := by
    rw [(k₂.gpr (by decide) : t₂.gpr .rcx = t₁.gpr .rcx), m0, mask_and]
  refine WP.mono (lst_ok (r := .rcx) (d := h + 0) (by decide) rfl r8 rbx r14 q0 L0
    (by omega_using [hT]) (by omega_using [ho]) (by omega_using [sT])) fun t₃ ⟨L1, k₃⟩ => ?_
  obtain q1 : (t₃.gpr .rdx).toNat = if bit then (word s₀.mem B (eN + 8 * (8 * i + h + 1))).toNat else 0 := by
    rw [(k₃.gpr (by decide) : t₃.gpr .rdx = t₂.gpr .rdx), (k₂.gpr (by decide) : t₂.gpr .rdx = t₁.gpr .rdx), m1,
      mask_and]
  refine WP.mono (lst_ok (r := .rdx) (d := h + 1) (by decide) (by omega_using []) ((k₃.gpr (by decide)).trans r8)
    ((k₃.gpr (by decide)).trans rbx) ((k₃.gpr (by decide)).trans r14) q1 L1
    (by omega_using [hT]) (by omega_using [ho]) (by omega_using [sT])) fun t₄ ⟨L2, k₄⟩ => ?_
  obtain k34 := k₃.trans k₄
  obtain q2 : (t₄.gpr .r9).toNat = if bit then (word s₀.mem B (eN + 8 * (8 * i + h + 2))).toNat else 0 := by
    rw [(k34.gpr (by decide) : t₄.gpr .r9 = t₂.gpr .r9), (k₂.gpr (by decide) : t₂.gpr .r9 = t₁.gpr .r9), m2,
      mask_and]
  refine WP.mono (lst_ok (r := .r9) (d := h + 2) (by decide) (by omega_using []) ((k34.gpr (by decide)).trans r8)
    ((k34.gpr (by decide)).trans rbx) ((k34.gpr (by decide)).trans r14) q2 L2
    (by omega_using [hT]) (by omega_using [ho]) (by omega_using [sT])) fun t₅ ⟨L3, k₅⟩ => ?_
  obtain k35 := k34.trans k₅
  obtain q3 : (t₅.gpr .r11).toNat = if bit then (word s₀.mem B (eN + 8 * (8 * i + h + 3))).toNat else 0 := by
    rw [(k35.gpr (by decide) : t₅.gpr .r11 = t₂.gpr .r11), (k₂.gpr (by decide) : t₂.gpr .r11 = t₁.gpr .r11), m3,
      mask_and]
  refine WP.mono (lst_ok (r := .r11) (d := h + 3) (by decide) (by omega_using []) ((k35.gpr (by decide)).trans r8)
    ((k35.gpr (by decide)).trans rbx) ((k35.gpr (by decide)).trans r14) q3 L3
    (by omega_using [hT]) (by omega_using [ho]) (by omega_using [sT])) fun t₆ ⟨L4, k₆⟩ => ?_
  obtain ⟨c₆, hc₆, hval₆⟩ := L4.val
  refine WP.mono (WP.keep [.rbp] (Q := fun t₇ => t₇.gpr .rbp = mask c₆ ∧ t₇.mem = t₆.mem) (by
    unfold cfToRbp; xrun [hc₆]; rfl) rfl) fun t₇ ⟨⟨b₇, m₇⟩, k₇⟩ => ?_
  refine ⟨⟨L4.scr.congr k₇.2.2, by rw [m₇]; exact L4.out,
    ⟨c₆, b₇, by rw [m₇]; exact hval₆⟩⟩, ?_⟩
  exact ((((k12.trans k₃).trans k₄).trans k₅).trans (k₆.trans k₇)).mono (by simp [lazyRegs])

/-- `0 - x` for a word `x ≤ 1` is the mask of `x = 1`. -/
theorem neg_bit_mask {x : BitVec 64} (h : x.toNat ≤ 1) : 0 - x = mask (decide (x.toNat = 1)) := by
  rcases Nat.lt_or_ge x.toNat 1 with h0 | h1
  · have : x = 0 := BitVec.eq_of_toNat_eq (by simp; omega_arith)
    subst this; rfl
  · have : x = 1 := BitVec.eq_of_toNat_eq (by simp; omega_arith)
    subst this; rfl

/-- `lazyLoads co`: `w`, and the bases of `T` and `o`. -/
theorem lazyLoads_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {co o : Nat}
    (po : OpAt s.mem B w co o) (qo : co < 20) :
    WP isa (.block (lazyLoads co)) s fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aTmp) ∧ t.gpr .rbx = off B (slot w o) ∧
      t.mem = s.mem ∧ Keep [.r12, .r8, .rbx] s t := by
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  refine WP.mono (WP.keep [.r12, .r8, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aTmp) ∧ t.gpr .rbx = off B (slot w o) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold lazyLoads
  xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aTmp) (by decide),
    hl (sArr co) (by unfold sArr; omega_using [qo]), hH.hw, hH.harr aTmp (by decide),
    show word s.mem B (8 * sArr co) = _ from po]

/-- `lazyMask`: the mask of `T_w` in `r13`, no borrow, `r14 = 0`. -/
theorem lazyMask_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hZ : slot w 8 ≤ Z)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h8 : s.gpr .r8 = off B (slot w aTmp)) :
    WP isa (.block lazyMask) s fun t =>
      t.gpr .r13 = 0 - word s.mem B (slot w aTmp + 8 * w) ∧ t.gpr .rbp = mask false ∧
      t.gpr .r14 = BitVec.ofNat 64 (8 * 0) ∧ t.mem = s.mem ∧ Keep [.r13, .rbp, .r14] s t := by
  obtain hTs := Nat.le_trans (slot_le (w := w) (show aTmp < 8 by decide)) hZ
  refine WP.mono (WP.keep [.r13, .rbp, .r14] (Q := fun t =>
      t.gpr .r13 = 0 - word s.mem B (slot w aTmp + 8 * w) ∧ t.gpr .rbp = mask false ∧
      t.gpr .r14 = BitVec.ofNat 64 (8 * 0) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold lazyMask
  xrun [State.ea, ix, addr0 h8 h12, hs.ld (show slot w aTmp + 8 * w + 8 ≤ Z by omega_using [hTs])]
  all_goals rfl

/-- The lazy subtraction's loop: before iteration `i`, from `s₀`. -/
structure LazyInv (s₀ : State) (B : Addr) (Z eT eN eo : Nat) (bit : Bool) (i : Nat) (t : State) : Prop where
  lr : Lr s₀ B Z eT eN eo bit (8 * i) t
  keep : Keep (.r14 :: lazyRegs) s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 (8 * i)

/-- `lazy8 co`, after the reduction: for `T < R + m` in `aTmp`, `o` holds a
number congruent to `T` modulo `m`. -/
theorem lazy8V_ok {s : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z)
    (hwN : w = 8 * n) (hn : 0 < n) (hw : w < 2 ^ 31) (h10 : s.gpr .r10 = off B (slot w aN))
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {co o : Nat} (po : (co, o) ∈ ps)
    (ho : o < 8) (ho2 : o ≠ aTmp)
    (hTlt : wv s.mem B (slot w aTmp) (w + 2) < 2 ^ (64 * w) + wv s.mem B (slot w aN) w) :
    WP isa (Adx.lazy8 co) s fun t =>
      wv t.mem B (slot w o) w % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w aTmp) (w + 2) % wv s.mem B (slot w aN) w ∧
      Arrays B w [o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := hs.nowrap
  obtain sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  obtain hTs := sl aTmp (by decide)
  obtain hNs := sl aN (by decide)
  obtain hos := sl o ho
  obtain soT : slot w o + 8 * (w + 2) ≤ slot w aTmp ∨ slot w aTmp + 8 * (w + 2) ≤ slot w o := slot_sep (Ne.symm ho2) |>.symm
  -- `o` may be `m`'s array: each word of `m` is read before the word of `o` at its place is written
  obtain soN : slot w o ≤ slot w aN ∨ slot w aN + 8 * (w + 2) ≤ slot w o := by
    by_cases h : o = aN
    · exact .inl (by rw [h])
    · have := slot_sep (w := w) h; unfold slot aN at *; omega_using [this]
  -- the top words of `T`
  obtain hR := wv_lt s.mem B (slot w aN) w
  rw [wv_top2] at hTlt
  obtain hT1 : (word s.mem B (slot w aTmp + 8 * w + 8)).toNat = 0 := by
    rcases Nat.eq_zero_or_pos (word s.mem B (slot w aTmp + 8 * w + 8)).toNat with h | h
    · exact h
    · have : 2 ^ (64 * w) * 2 ^ 64 ≤ 2 ^ (64 * w) * ((word s.mem B (slot w aTmp + 8 * w)).toNat +
          2 ^ 64 * (word s.mem B (slot w aTmp + 8 * w + 8)).toNat) :=
        Nat.mul_le_mul_left _ (by have := Nat.mul_le_mul_left (2 ^ 64) h; omega_arith)
      have : 2 ^ (64 * w) * 2 ^ 64 ≥ 2 * 2 ^ (64 * w) := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by decide)
      omega_arith
  rw [hT1, Nat.mul_zero, Nat.add_zero] at hTlt
  obtain hTw : (word s.mem B (slot w aTmp + 8 * w)).toNat ≤ 1 := by
    rcases Nat.lt_or_ge (word s.mem B (slot w aTmp + 8 * w)).toNat 2 with h | h
    · omega_arith
    · have : 2 ^ (64 * w) * 2 ≤ 2 ^ (64 * w) * (word s.mem B (slot w aTmp + 8 * w)).toNat :=
        Nat.mul_le_mul_left _ h
      omega_arith
  generalize hbit : decide ((word s.mem B (slot w aTmp + 8 * w)).toNat = 1) = bit
  unfold Adx.lazy8
  refine WP.seq (WP.mono (lazyLoads_ok hs hdi hH hZ (hv.at po) (hv.lt po))
    fun s₀ ⟨h12₀, h8₀, hbx₀, hm₀, k₀⟩ => ?_)
  refine WP.seq (WP.mono (lazyMask_ok (hs.congr k₀.2.2) hZ h12₀ h8₀)
    fun s₁ ⟨h13, hbp, h14, hm₁', k₀₁⟩ => ?_)
  rw [hm₀, neg_bit_mask hTw, hbit] at h13
  obtain hm₁ : s₁.mem = s.mem := hm₁'.trans hm₀
  obtain k₁ := k₀.trans k₀₁
  obtain h12 : s₁.gpr .r12 = BitVec.ofNat 64 w := (k₀₁.gpr (by decide)).trans h12₀
  obtain h8 : s₁.gpr .r8 = off B (slot w aTmp) := (k₀₁.gpr (by decide)).trans h8₀
  obtain hbx : s₁.gpr .rbx = off B (slot w o) := (k₀₁.gpr (by decide)).trans hbx₀
  obtain k₁' : Keep (.r14 :: lazyRegs) s₁ s₁ := Keep.refl _ _
  obtain I0 : LazyInv s₁ B Z (slot w aTmp) (slot w aN) (slot w o) bit 0 s₁ :=
    ⟨⟨hs.congr k₁.2.2, Outside.refl _ _ _ _, ⟨false, hbp, by simp [mv, wv]⟩⟩, k₁', h14⟩
  obtain s₁10 : s₁.gpr .r10 = off B (slot w aN) := (k₁.gpr (by decide)).trans h10
  refine wp_upto (a := 0) (N := n) hn (LazyInv s₁ B Z (slot w aTmp) (slot w aN) (slot w o) bit) ?_ ?_ I0
  · intro i _ hi t hI
    obtain g : ∀ r, r ∉ (.r14 :: lazyRegs) → t.gpr r = s₁.gpr r := fun r hr => hI.keep.gpr hr
    obtain t8 := (g .r8 (by decide)).trans h8
    obtain t10 := (g .r10 (by decide)).trans s₁10
    obtain tbx := (g .rbx (by decide)).trans hbx
    obtain t13 := (g .r13 (by decide)).trans h13
    obtain t12 := (g .r12 (by decide)).trans h12
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (group_ok (h := 0) t8 t10 tbx hI.r14 t13 hI.lr (by omega_using [hTs, hi, hwN])
      (by omega_using [hNs, hi, hwN]) (by omega_using [hos, hi, hwN]) (by omega_using [soT, hi, hwN])
      (by omega_using [soN, hi, hwN])) fun t₁ ⟨L₁, kg₁⟩ => ?_
    refine WP.mono (group_ok (h := 4) ((kg₁.gpr (by decide)).trans t8) ((kg₁.gpr (by decide)).trans t10)
      ((kg₁.gpr (by decide)).trans tbx) ((kg₁.gpr (by decide)).trans hI.r14) ((kg₁.gpr (by decide)).trans t13)
      L₁ (by omega_using [hTs, hi, hwN]) (by omega_using [hNs, hi, hwN]) (by omega_using [hos, hi, hwN])
      (by omega_using [soT, hi, hwN]) (by omega_using [soN, hi, hwN])) fun t₂ ⟨L₂, kg₂⟩ => ?_
    obtain k12 := kg₁.trans kg₂
    refine WP.mono (count8_ok t₂ (r := .r12) (by decide) ((k12.gpr (by decide)).trans hI.r14)
      (N := n) (by rw [(k12.gpr (by decide) : t₂.gpr .r12 = t.gpr .r12), t12, hwN]) (by omega_using [hw, hi, hwN])
      (by omega_using [hw, hwN])) fun t' ⟨hz, h14', hm', k'⟩ => ⟨hz, ?_, ?_, h14'⟩
    · rw [show 8 * (i + 1) = 8 * i + 4 + 4 by omega_arith]
      obtain ⟨c₂, b₂, v₂⟩ := L₂.val
      exact ⟨L₂.scr.congr k'.2.2, by rw [hm']; exact L₂.out,
        ⟨c₂, (k'.gpr (by decide)).trans b₂, by rw [hm']; exact v₂⟩⟩
    · exact ((hI.keep.trans k12).trans k').mono (by simp [lazyRegs])
  · intro t hI
    obtain ⟨c, _, hval⟩ := hI.lr.val
    rw [← hwN, hm₁] at hval
    have hout := hI.lr.out
    rw [← hwN, hm₁] at hout
    refine ⟨?_, Arrays.of_outside (j := o) (by simp) hout (Nat.le_refl _) (by omega_arith),
      (k₁.trans hI.keep).mono (by simp [lazyRegs, mmRegs])⟩
    rw [wv_top2, hT1, Nat.mul_zero, Nat.add_zero]
    refine VG.Proof.Bignum.lazy_sub (wv_lt _ _ _ _) (Bool.toNat_le c) hTw hTlt ?_
    rw [← hbit] at hval
    simp only [mv] at hval
    by_cases h1 : (word s.mem B (slot w aTmp + 8 * w)).toNat = 1
    · simp only [h1, decide_true, ite_true, Nat.one_mul] at hval ⊢; exact hval
    · have h0 : (word s.mem B (slot w aTmp + 8 * w)).toNat = 0 := by omega_arith
      simp only [h0, Nat.zero_mul, Nat.add_zero] at hval ⊢
      simpa using hval

end VG.Proof.Bignum.X86_64

end

end

/-! ### `Bignum.X86_64.MontFnLazyVerified`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.MontFnLazy`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTiledLazy`, which only this module used -/

section

/-! The reduction of a raw product `X < R²` and the lazy final subtraction. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- `redcFinish_ok` with the lazy final subtraction, for any raw product
`X < R²`: `o` is congruent to `X R⁻¹` modulo `m`. -/
theorem redcLazy_ok {s s₁ : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hwN : w=8*n) (hnN : 0<n) (hw : w < 2 ^ 31)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {co o : Nat} (po : (co, o) ∈ ps)
    (ho : o < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {X : Nat} (hX : X < 2 ^ (64 * w) * 2 ^ (64 * w))
    (hv₁ : wv s₁.mem B (slot w aAcc + 16) (2 * w) = X)
    (ho₁ : Outside B (slot w aAcc) (16*w+32) s.mem s₁.mem) (k₁ : Keep mmRegs s s₁) :
    WP isa (AdxTiledProduct.redcLazy co) s₁ fun t =>
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w = X % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  obtain hNs := slot_le (w := w) (show aN < 8 by decide)
  obtain hw1 : 2 ≤ w := by omega_using [hwN, hnN]
  obtain hg : hdrBytes ≤ slot w aAcc := by unfold slot; omega_using []
  obtain hsep : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega_using []
  obtain hmpos : 0 < wv s.mem B (slot w aN) w := wv_pos_of_inv (by omega_using [hw1]) hinv
  obtain hH₁ := hH.of_outside ho₁ hg
  obtain hn₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := ho₁.word (by omega_using [hsep]) (by omega_using [hZ, hn, hNs])
  unfold AdxTiledProduct.redcLazy
  refine WP.seq (WP.mono (AdxRotate8.redc_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hH₁ hZ hwN hnN)
    fun s₂ ⟨vred,ho₂,k₂⟩ => ?_)
  obtain ⟨q,hq,heq⟩ := vred (by rw [hn₁]; exact hinv)
  obtain hN₁ : wv s₁.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho₁.wv (by omega_using [hsep]) (by omega_using [hZ, hn, hNs])
  rw [hv₁, hN₁] at heq
  obtain ho12 := (ho₁.mono (o' := slot w aAcc) (n' := 16 * w + 32) (by omega_using []) (by omega_using [])).trans ho₂
  obtain hN₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho12.wv (by omega_using [hsep]) (by omega_using [hZ, hn, hNs])
  obtain k12 := k₁.trans k₂
  obtain hs₂ := hs.congr k12.2.2
  obtain hH₂ := hH.of_outside ho12 (by unfold slot; omega_using [])
  obtain hTlt : wv s₂.mem B (slot w aTmp) (w + 2) < 2 ^ (64 * w) + wv s.mem B (slot w aN) w :=
    VG.Proof.Bignum.redc_lt_add hq hX heq
  obtain hsrc : readSrc s₂ (.mem (hdr (sArr aN))) = some (off B (slot w aN)) := by
    rw [readSrc_word (d := 8 * sArr aN) hs₂ (by simp only [State.ea, hdr, (k12.gpr (by decide)).trans hdi, hdrOff])
      (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega_using [hZ, this]), hH₂.harr aN (by decide)]
  refine WP.seq (WP.mono (movMem_ok s₂ (dst := .r10) hsrc) fun s₃ ⟨h10, _, _, k₃⟩ => ?_)
  obtain k123 := k12.trans k₃.keep
  obtain hv₂ : Ops s₂.mem B w ps := hv.of_outside ho12 (by unfold slot sFn hdrBytes; omega_using [])
  refine WP.mono (lazy8V_ok (hs.congr k123.2.2) ((k123.gpr (by decide)).trans hdi)
    (k₃.2.1 ▸ hH₂) hZ hwN hnN hw h10 (k₃.2.1 ▸ hv₂) po ho ho2 (by rw [k₃.2.1, hN₂]; exact hTlt))
    fun t ⟨hv, hf, kt⟩ => ?_
  rw [k₃.2.1, hN₂] at hv
  refine ⟨?_, ?_, (k123.trans kt).mono (by decide)⟩
  · rw [Nat.mul_mod, hv, ← Nat.mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · intro x hx
    obtain h1 := hx aAcc (by simp)
    obtain h2 := hx aTmp (by simp)
    obtain h3 := hx o (by simp)
    obtain hfin : t.mem x = s₃.mem x := hf x (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact h3)
    rw [hfin, k₃.2.1]
    exact ho12 x (by
      obtain hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega_using []
      omega_using [h1, h2, hAT])

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end

end


/-!
# `vg_rsa_lazy_mont_mul_adx`: correctness

`mulAdx_ok`'s proof, with the lazy reduction of the tiles
(`AdxTiledProduct.redcLazy_ok`) and `montMul`'s rounds without `[b] < m`
(`mmTailLazy_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- `adxBodyLazy`: `adxBody_ok` without `[b] < m`, and so without `[o] < m`. -/
theorem adxBodyLazy_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hv : Ops s.mem B w (adxOps o a b))
    (hdx : s.gpr .rdx = BitVec.ofNat 64 o) (hcx : s.gpr .rcx = BitVec.ofNat 64 a)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 b)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa adxBodyLazy s fun t =>
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      (∃ m, Outside B (8 * sFn 12) 32 s.mem m ∧ Arrays B w [aAcc, aTmp, o] m t.mem) ∧ Keep mmRegs s t := by
  unfold adxBodyLazy
  refine WP.seq (WP.mono (alignTest_ok hs hdi hH hZ) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  obtain hs₁ := hs.congr k₁.2.2
  obtain hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hH hv ⊢
  obtain post : ∀ t, (wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      (∃ m, Outside B (8 * sFn 12) 32 s₁.mem m ∧ Arrays B w [aAcc, aTmp, o] m t.mem) ∧ Keep mmRegs s t) :=
    fun t ⟨h2, h3, k⟩ => ⟨h2, ⟨_, Outside.refl _ _ _ _, h3⟩, (k₁.trans k).mono (by decide)⟩
  by_cases h8w : AlignOk w
  · refine WP.ite true (by simp [eval, hz, h8w]) (fun _ => ?_) (by simp)
    obtain ⟨h8w, h8w', -⟩ := h8w
    unfold tiledLazy
    obtain hcx₁ : s₁.gpr .rcx = BitVec.ofNat 64 a := (k₁.gpr (by decide)).trans hcx
    obtain h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 b := (k₁.gpr (by decide)).trans h8
    refine WP.seq (WP.mono (cmpIdx_ok ha hb hcx₁ h8₁) fun s₂ ⟨hz₂, hm₂, _, k₂⟩ => ?_)
    obtain hs₂ := hs₁.congr k₂.2.2
    obtain hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
    rw [← hm₂] at hinv hH hv ⊢
    obtain hwN : w = 8 * (w / 8) := by omega_arith
    obtain hraw : WP isa (.ite .e (AdxTiledSquare.rawSquareBare xA) (AdxTiledProduct.rawProductBare xA xB)) s₂
        fun s₃ => ∃ m, Outside B (8 * sFn 12) 32 s₂.mem m ∧
          wv s₃.mem B (slot w aAcc + 16) (2 * w) = wv s₂.mem B (slot w a) w * wv s₂.mem B (slot w b) w ∧
          Outside B (slot w aAcc) (16 * w + 32) m s₃.mem ∧ Keep mmRegs s₂ s₃ := by
      by_cases hab : a = b
      · subst b
        exact WP.ite true (by simp [eval, hz₂]) (fun _ =>
          AdxTiledSquare.rawSquareBare_ok hs₂ hdi₂ hH hZ hwN (by omega_arith) hw' hv (mem_adxOps_a o a a) ha ha1 ha2)
          (by simp)
      · exact WP.ite false (by simp [eval, hz₂, hab]) (by simp) (fun _ =>
          AdxTiledProduct.rawProductBare_ok hs₂ hdi₂ hH hv (mem_adxOps_a o a b) (mem_adxOps_b o a b) hZ hw' hwN
            (by omega_arith) ha hb ha1 ha2 hb1 hb2)
    refine WP.seq (WP.mono hraw fun s₃ ⟨m, om, hv₃, ho₃, k₃⟩ => ?_)
    have hn := hs.nowrap
    obtain sl : ∀ j < 8, 8 * sFn 12 + 32 ≤ slot w j ∧ slot w j + 8 * (w + 2) ≤ Z := fun j hj =>
      ⟨by unfold slot sFn hdrBytes; omega_arith, Nat.le_trans (slot_le hj) hZ⟩
    obtain vm : ∀ j < 8, wv m B (slot w j) w = wv s₂.mem B (slot w j) w := fun j hj =>
      om.wv (Or.inr (sl j hj).1) (by have := (sl j hj).2; omega_arith)
    obtain hinvm : ((word m B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
      rw [om.word (Or.inr (sl aN (by decide)).1) (by have := (sl aN (by decide)).2; omega_arith)]; exact hinv
    refine WP.mono (AdxTiledProduct.redcLazy_ok (s := {s₂ with mem := m}) (hs₂.congr rfl) hdi₂
      (hH.of_outside_fn om (by unfold sFn; omega_arith)) hZ hwN (by omega_arith) hw'
      (hv.of_outside om (Nat.le_refl _)) (mem_adxOps_o o a b) ho ho1 ho2 hinvm
      (Nat.mul_lt_mul'' (wv_lt _ _ _ _) (wv_lt _ _ _ _)) hv₃ ho₃ k₃)
      fun t ⟨h2, h3, k⟩ => ?_
    dsimp only at h2 h3
    rw [vm aN (by decide)] at h2
    exact ⟨h2, ⟨m, om, h3⟩, ((k₁.trans k₂).trans k).mono (by decide)⟩
  · refine WP.ite false (by simp [eval, hz, h8w]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (basesR_ok hs₁ hdi₁ hH hZ ho ha hb ((k₁.gpr (by decide)).trans hdx)
      ((k₁.gpr (by decide)).trans hcx) ((k₁.gpr (by decide)).trans h8))
      fun s₂ ⟨hbx, h11, h9, h10, h8₂, h12, h15, hsi₂, hm₂, k₂⟩ => ?_)
    rw [← hm₂] at hinv
    refine WP.mono (mmTailLazy_ok (hs₁.congr k₂.2.2) hZ hw hw' (by decide) (by decide) (by decide) ho ha hb
      (by decide) (by decide) (Ne.symm ho1) (Ne.symm ha1) (Ne.symm hb1) (by decide) (Ne.symm ho2) hbx h11 h9 h10
      h8₂ h12 h15 hsi₂ hinv) fun t ⟨_, _, h2, h3, k⟩ => ?_
    rw [hm₂] at h2 h3
    exact post t ⟨h2, h3, (k₂.trans k).mono (by decide)⟩

/-- `vg_rsa_lazy_mont_mul_adx`'s code: what `mulAdx_ok` says, but `[o] < m`, without `[b] < m`. -/
theorem mulAdxLazy_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa mulAdxLazy s fun t =>
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s.gpr r := by
  have hn := hs.nowrap
  obtain h256 : 8 * sFn 0 + 48 ≤ slot w 0 := by unfold sFn slot hdrBytes; omega_arith
  have hxO : 8 * sArr xO = 8 * sFn 0 := rfl
  obtain sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  obtain s0 : ∀ j, slot w 0 ≤ slot w j := fun j => by unfold slot; omega_arith
  obtain hZ32 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 0 (show 31 < 32 by decide); have := sl 0 (by decide); omega_arith
  unfold mulAdxLazy
  refine WP.seq (WP.mono (adxHead_ok hs hdi hH hZ ho ha hb hdx hcx h8) fun s₁ ⟨hm₁, hdx₁, hcx₁, h8₁, k₁, sv, x3, x4, x5, x6, x7⟩ => ?_)
  obtain hs₁ := hs.congr k₁.2.2
  obtain hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  obtain ho₁ : Outside B (8 * sArr xO) 24 s.mem s₁.mem := hm₁ ▸ headMem_outside s.mem B w o a b
  obtain vj : ∀ j < 8, wv s₁.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj =>
    ho₁.wv (by have := s0 j; omega_arith) (by have := sl j hj; omega_arith)
  obtain hinv₁ : ((word s₁.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [ho₁.word (by have := s0 aN; omega_arith) (by have := sl aN (by decide); omega_arith)]; exact hinv
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (adxBodyLazy_ok hs₁ hdi₁ (hm₁ ▸ headMem_hdr hH o a b) hZ hw hw' ho
    ha hb ho1 ho2 ha1 ha2 hb1 hb2 (hm₁ ▸ headMem_ops s.mem B w o a b) hdx₁ hcx₁ h8₁ hinv₁))
    fun s₂ ⟨⟨heq, ⟨mb, omb, har⟩, k₂⟩, hx₂, _⟩ => ?_)
  obtain hs₂ := hs₁.congr k₂.2.2
  obtain hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  refine WP.mono (restore_ok hs₂ hdi₂ hZ32 (m₀ := s.mem) (by rw [hx₂, x3]) (by rw [hx₂, x4]) (by rw [hx₂, x5])
    (by rw [hx₂, x6]) (by rw [hx₂, x7]) (sv.of_xmm hx₂))
    fun t ⟨rs, o₃, in₃, inb₃, k₃⟩ => ?_
  obtain hvo : wv t.mem B (slot w o) w = wv s₂.mem B (slot w o) w :=
    o₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> have := s0 o <;> unfold sFn slot hdrBytes at * <;> omega_arith)
      (by have := sl o ho; omega_arith)
  rw [vj aN (by decide), vj a ha, vj b hb] at heq
  refine ⟨by rw [hvo]; exact heq, fun x hx => ?_,
    ((k₁.trans k₂).trans k₃).mono (by decide), ?_⟩
  · by_cases hr : 8 * sFn 0 ≤ ofs B x ∧ ofs B x < 8 * sFn 0 + 48
    · exact in₃ x hr.1 hr.2
    by_cases hb : 8 * sFn 12 ≤ ofs B x ∧ ofs B x < 8 * sFn 12 + 32
    · exact inb₃ x hb.1 hb.2
    obtain hb' : ofs B x < 8 * sFn 12 ∨ 8 * sFn 12 + 32 ≤ ofs B x := by omega_arith
    rw [o₃ x (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl <;> simp only [] <;> omega_arith), har x hx, omb x hb',
      ho₁ x (by rw [hxO]; unfold sFn at *; omega_arith)]
  · exact rs

end VG.Proof.Bignum.X86_64

end

end

/-! ### `Bignum.X86_64.MontFnLazyCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTiledLazyCT`, which only this module used -/

section

/-!
# The lazy final subtraction: constant time

`lazy8` addresses only from `w` and the bases of `T`, `m` and `o`, which
`lazyLoads` reads from the header; the mask, which is secret, only selects
data.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

/-- After `lazyLoads`: `w` and the bases of `T`, `o` and `m`. -/
def FL (o : Nat) (L : Ws) (t : State) : Prop :=
  t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .r8 = off L.B (slot L.w aTmp) ∧
  t.gpr .rbx = off L.B (slot L.w o) ∧ t.gpr .r10 = off L.B (slot L.w aN)

theorem pins_fl (o : Nat) : Pins (FL o) [.r12, .r8, .rbx, .r10] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]

/-- `redcLazy`, for slots and layouts given by any public data `x`. -/
theorem redcLazy_ct {α : Type} {P : α → List (Nat × Nat)} {L : α → Layout} {O : α → Nat} {co : Nat}
    (po : ∀ x, (co, O x) ∈ P x) {h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.lazyLoads co)) h₃).isSome=true) :
    RelCT isa (Two fun x s => GoodV (P x) (L x) s) (AdxTiledProduct.redcLazy co) (fun _ _ => True) := by
  have pins : Pins (fun x s => GoodV (P x) (L x) s) [.rdi] := fun x => pins_goodV (P x) (L x)
  unfold AdxTiledProduct.redcLazy
  refine RelCT.seq redcV_ct' ?_
  refine RelCT.seq (two_piece (Ψ := fun x s => GoodV (P x) (L x) s ∧ s.gpr .r10=off (L x).B (slot (L x).w aN))
    [.rdi] pins (by taint_decide) ?_) ?_
  · rintro x s ⟨⟨mi,hg⟩,hv⟩
    have hZ := (L x).hZ
    have hsrc : readSrc s (.mem (hdr (sArr aN)))=some (off (L x).B (slot (L x).w aN)) := by
      rw [readSrc_word (d := 8*sArr aN) hg.scr (by simp only [State.ea,hdr,hg.rdi,hdrOff])
        (by have := hdr_lt_slot (L x).w 8 (show sArr aN<32 by decide); omega_using [hZ, this]),hg.hdr.harr aN (by decide)]
    exact WP.mono (movMem_ok s (dst := .r10) hsrc) fun _ ⟨p,_,_,k⟩ =>
      ⟨⟨⟨mi,hg.scr.congr k.keep.2.2,(k.keep.gpr (by decide)).trans hg.rdi,k.2.1 ▸ hg.hdr⟩,k.2.1 ▸ hv⟩,p⟩
  unfold Adx.lazy8
  refine RelCT.seq (two_piece (Ψ := fun x => FL (O x) ⟨(L x).B,(L x).Z,(L x).w⟩) [.rdi]
    (fun x s t hs ht => pins x s t hs.1 ht.1) hF ?_)
    (two_taint _ (fun x => pins_fl (O x) ⟨(L x).B,(L x).Z,(L x).w⟩) (by taint_decide))
  rintro x s ⟨⟨⟨mi,hg⟩,hv⟩,p⟩
  exact WP.mono (lazyLoads_ok hg.scr hg.rdi hg.hdr (L x).hZ (hv.at (po x)) (hv.lt (po x)))
    fun _ ⟨p12,p8,pbx,_,k⟩ => ⟨p12,p8,pbx,(k.gpr (by decide)).trans p⟩

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end

end

/-!
# `vg_rsa_lazy_mont_mul_adx`: constant time

`vg_rsa_mont_mul_adx`'s proof, with the lazy reduction of the tiles
(`AdxTiledProduct.redcLazy_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- The tiles, with the lazy reduction. -/
theorem tiledLazy_ct : RelCT isa (Two fun d s => (AdxMid d s ∧ s.zf = some (decide (AlignOk d.w))) ∧
    isa.eval .e s = some true) tiledLazy fun _ _ => True := by
  unfold tiledLazy
  refine RelCT.seq (two_piece (Ψ := fun d s => (AdxMid d s ∧ AlignOk d.w) ∧ s.zf = some (decide (d.a = d.b)))
    [.rcx, .r8] (fun d s₁ s₂ h₁ h₂ r hr => pins_adxMid d s₁ s₂ h₁.1.1 h₂.1.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
    (by taint_decide) ?_) ?_
  · rintro d s ⟨⟨hm, hz⟩, he⟩
    have hA : AlignOk d.w := by simpa only [eval, hz, Option.some.injEq, decide_eq_true_eq] using he
    have ha := hm.1.2.2.2.2.1.2.1
    have hb := hm.1.2.2.2.2.1.2.2.1
    have hcx := hm.1.2.2.2.2.2.2.1
    have h8 := hm.1.2.2.2.2.2.2.2
    exact WP.mono (cmpIdx_ok ha hb hcx h8) fun t ⟨hz', hm', hc', k⟩ =>
      ⟨⟨⟨AdxIn.of_keep hm.1 hm' k hc' (by decide), hm' ▸ hm.2⟩, hA⟩, hz'⟩
  refine RelCT.seq (R := Two TiledMid)
    (two_ite (fun d s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_)
    (AdxTiledProduct.redcLazy_ct (P := fun x : TiledData => adxOps x.1.o x.1.a x.1.b)
      (L := fun x => adxLayout x.1 x.2.1 x.2.2) (O := fun x => x.1.o) (fun x => mem_adxOps_o _ _ _)
      (by taint_decide))
  · rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨d, ⟨⟨⟨h₁, hA⟩, z₁⟩, e₁⟩, ⟨⟨h₂, -⟩, -⟩, -⟩ e₁' e₂'
    have hab : d.a = d.b := by simpa only [eval, z₁, Option.some.injEq, decide_eq_true_eq] using e₁
    have hZ := h₁.1.2.2.2.1
    obtain ⟨-, ha, -, -, -, ha1, ha2, -⟩ := h₁.1.2.2.2.2.1
    obtain ⟨ht, -, u₁, u₂⟩ := two_post (α := Unit)
      (two_map (fun _ => adxLayout d hZ hA) (fun _ _ h => h)
        (AdxTiledSquare.rawBare_ct (ps := adxOps d.o d.a d.b) (mem_adxOps_a _ _ _) ha ha1 ha2
          (by taint_decide) (by taint_decide) (by taint_decide)))
      (fun _ s h => AdxTiledSquare.rawBare_fw (mem_adxOps_a _ _ _) ha ha1 ha2 (adxLayout d hZ hA) s h)
      _ _ _ _ _ _ ⟨(), goodV_of_mid h₁ hZ hA, goodV_of_mid h₂ hZ hA⟩ e₁' e₂'
    exact ⟨ht, ⟨d, hZ, hA⟩, u₁, u₂⟩
  · rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨d, ⟨⟨⟨h₁, hA⟩, -⟩, -⟩, ⟨⟨h₂, -⟩, -⟩, -⟩ e₁' e₂'
    have hZ := h₁.1.2.2.2.1
    obtain ⟨-, ha, hb, -, -, ha1, ha2, hb1, hb2⟩ := h₁.1.2.2.2.2.1
    obtain ⟨ht, -, u₁, u₂⟩ := two_post (α := Unit)
      (two_map (fun _ => adxLayout d hZ hA) (fun _ _ h => h)
        (AdxTiledProduct.rawBare_ct (ps := adxOps d.o d.a d.b) (mem_adxOps_a _ _ _) (mem_adxOps_b _ _ _) ha hb
          ha1 ha2 hb1 hb2 (by taint_decide) (by taint_decide)))
      (fun _ s h => AdxTiledProduct.rawBare_fw (mem_adxOps_a _ _ _) (mem_adxOps_b _ _ _) ha hb ha1 ha2 hb1 hb2
        (adxLayout d hZ hA) s h)
      _ _ _ _ _ _ ⟨(), goodV_of_mid h₁ hZ hA, goodV_of_mid h₂ hZ hA⟩ e₁' e₂'
    exact ⟨ht, ⟨d, hZ, hA⟩, u₁, u₂⟩

theorem adxBodyLazy_ct : RelCT isa (Two AdxMid) adxBodyLazy fun _ _ => True := by
  unfold adxBodyLazy
  refine RelCT.seq (two_piece (Ψ := fun d s => AdxMid d s ∧ s.zf = some (decide (AlignOk d.w))) [.rdi]
    (fun d s₁ s₂ h₁ h₂ r hr => pins_adxMid d s₁ s₂ h₁ h₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr])) (by taint_decide) ?_)
    (two_ite (fun d s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) tiledLazy_ct fallback_ct)
  rintro d s ⟨hm, hv⟩
  obtain ⟨hs, hdi, ⟨mi, hH⟩, hZ, -⟩ := id hm
  exact WP.mono (alignTest_ok hs hdi hH hZ) fun t ⟨hz, hm', k⟩ =>
    ⟨⟨AdxIn.of_keep hm hm' k (k.gpr (by decide)) (by decide), hm' ▸ hv⟩, hz⟩

/-- `vg_rsa_lazy_mont_mul_adx` after the head. -/
theorem adxTailLazy_ct : RelCT isa (Two AdxMid) (.seq adxBodyLazy (.block restore)) fun _ _ => True :=
  RelCT.seq (RelCT.keepRdi (f := CallData.B) adxBodyLazy_ct (by rw [← Code.allInstrs_eq]; decide +kernel)
    fun _ _ h => h.1.2.1)
    (two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h₁, h₂]) (by taint_decide))

end VG.Proof.Bignum.X86_64

end

end

/-! # The baseline Montgomery multiplication of `vg_rsa_lazy_mont_mul`, without `[b] < m` -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.MontFn

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64.MontFn
open VG.Impl.Bignum.X86_64.Public (aN aAcc aTmp)
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)
open VG.Proof.MlKem.X86_64

/-- `mulBase_ok` without `[b] < m`: the baseline is lazy too. -/
theorem mulBaseLazy_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa mulBase s fun t =>
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s.gpr r := by
  have hn := hs.nowrap
  unfold mulBase
  refine WP.seq (WP.mono (fnHead_ok hs hdi hH hZ ho ha hb hdx hcx h8)
    fun s₁ ⟨hbx, h11, h9, h10, h8₁, h12, h15, hsi₁, hm₁, k₁, sv⟩ => ?_)
  rw [← hm₁] at hinv
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (BaseSquare.tail_ok hs₁ hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hbx h11 h9 h10 h8₁ h12
    h15 hsi₁ hinv) fun s₂ ⟨_, _, heq, har, k₂, hx₂⟩ => ?_)
  refine WP.mono (unsaves_ok (sv.of_stashed hx₂)) fun t ⟨rs, mt, _, k₃⟩ => ?_
  rw [hm₁] at heq har
  rw [← mt] at heq har
  exact ⟨heq, har, ((k₁.trans k₂).trans k₃).mono (by decide), rs⟩

end VG.Proof.Bignum.X86_64.MontFn

end

end

/-!
# Lazy squarings by calls of `vg_rsa_lazy_mont_mul` and `vg_rsa_lazy_mont_mul_adx`

`MontS.fnLazy` and `MontS.fnLazyAdx`: the squarings of `aY` by calls of the
lazy Montgomery multiplications, inlined, whose results are below `R`. A call
of `vg_rsa_lazy_mont_mul`, inlined, is `vg_rsa_mont_mul`'s (`mmFnBase`),
whose timing `Mont.fnBase` already proves.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- The call of `vg_rsa_lazy_mont_mul_adx`, inlined. -/
def mmFnAdxLazy (o a b : Nat) : Prog isa := (call "vg_rsa_lazy_mont_mul_adx" mulAdxLazy o a b).inline

theorem mmFnAdxLazy_eq (o a b : Nat) : mmFnAdxLazy o a b = .seq (.block (args o a b)) mulAdxLazy := rfl

theorem mmFnAdxLazy_ct {o a b : Nat} (op : Opnds o a b) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.seq (.block (args o a b)) (.block (enter ++ slotsIn))) hc).isSome = true) :
    RelCT isa (Two GoodW) (mmFnAdxLazy o a b) fun _ _ => True := by
  rw [mmFnAdxLazy_eq]
  unfold mulAdxLazy
  refine RelCT.assoc (RelCT.seq (two_piece (Ψ := fun L s => AdxMid ⟨L.B, L.Z, L.w, o, a, b⟩ s) [.rdi] pins_goodW h
    fun L s ⟨_, hg, hZ⟩ => ?_) (two_map (fun L : Ws => (⟨L.B, L.Z, L.w, o, a, b⟩ : CallData)) (fun _ _ h => h)
      adxTailLazy_ct))
  refine WP.seq (WP.mono (fnArgs_ok s o a b) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
  exact WP.mono (adxHead_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ op.1 op.2.1
    op.2.2.1 hdx hcx h8) fun u ⟨hm', hdx', hcx', h8', k', _⟩ =>
      AdxMid.of_head (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ op hm' hdx' hcx' h8' k'

/-- Squarings by calls of `vg_rsa_lazy_mont_mul`, inlined: `vg_rsa_mont_mul`'s
code, whose result is below `R` for any operand below `R`. -/
def MontS.fnLazy : MontS where
  mm := mmFnBase aY aY aY
  bd _ R := R
  le h := h
  ok hg hZ hw hw' hinv _ := by
    rw [mmFnBase_eq]
    refine WP.seq (WP.mono (fnArgs_ok _ _ _ _) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
    rw [← hm] at hinv ⊢
    refine WP.mono (MontFn.mulBaseLazy_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr)
      hZ hw hw' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hdx hcx h8 hinv) fun t' ⟨h2, h3, k', _⟩ => ?_
    exact ⟨⟨hg.scr.congr ((k.trans k').2.2), ((k.trans k').gpr (by decide)).trans hg.rdi, h3.hdr (hm ▸ hg.hdr)⟩,
      wv_lt _ _ _ _, h2, h3, (k.trans k').mono (by decide)⟩
  ct := Mont.fnBase.ct (.inr (.inl ⟨rfl, rfl, rfl⟩))

/-- Squarings by calls of `vg_rsa_lazy_mont_mul_adx`, inlined. -/
def MontS.fnLazyAdx : MontS where
  mm := mmFnAdxLazy aY aY aY
  bd _ R := R
  le h := h
  ok hg hZ hw hw' hinv _ := by
    rw [mmFnAdxLazy_eq]
    refine WP.seq (WP.mono (fnArgs_ok _ _ _ _) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
    rw [← hm] at hinv ⊢
    refine WP.mono (mulAdxLazy_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ hw hw'
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hdx hcx h8 hinv) fun t' ⟨h2, h3, k', _⟩ => ?_
    exact ⟨⟨hg.scr.congr ((k.trans k').2.2), ((k.trans k').gpr (by decide)).trans hg.rdi, h3.hdr (hm ▸ hg.hdr)⟩,
      wv_lt _ _ _ _, h2, h3, (k.trans k').mono (by decide)⟩
  ct := by exact mmFnAdxLazy_ct (by unfold Opnds; decide) (by taint_decide)

end VG.Proof.Bignum.X86_64
