module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxLazy8
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Bignum.X86_64.OpAt
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

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
  have ea : ∀ e, off B (e + 8 * (8 * i) + 8 * d) = off B (e + 8 * (8 * i + d)) := fun e => by
    congr 1; omega_using []
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.cf = some c' ∧ ∃ v : BitVec 64, t₁.mem = t.mem.writeW (off B (eo + 8 * (8 * i + d))) v ∧
        v.toNat + (t.gpr r).toNat + c.toNat =
          (word t.mem B (eT + 8 * (8 * i + d))).toNat + 2 ^ 64 * c'.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, v, hmem, hv⟩, k₁⟩ => ?_
  · xrun [State.ea, ix, h8, hbx, h14, addrDk, ea, hc, hr, hr.symm, hI.scr.ld hT, hI.scr.st ho]
    exact ⟨_, rfl, sbb_toNat _ _ _⟩
  have hx : word t.mem B (eT + 8 * (8 * i + d)) = word s₀.mem B (eT + 8 * (8 * i + d)) :=
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
  have ea : ∀ j, off B (eN + 8 * (8 * i) + 8 * (h + j)) = off B (eN + 8 * (8 * i + h + j)) := fun j => by
    congr 1; omega_using []
  refine WP.mono (WP.keep [.rcx, .rdx, .r9, .r11] (Q := fun t' =>
      t'.gpr .rcx = mask bit &&& word t.mem B (eN + 8 * (8 * i + h)) ∧
      t'.gpr .rdx = mask bit &&& word t.mem B (eN + 8 * (8 * i + h + 1)) ∧
      t'.gpr .r9 = mask bit &&& word t.mem B (eN + 8 * (8 * i + h + 2)) ∧
      t'.gpr .r11 = mask bit &&& word t.mem B (eN + 8 * (8 * i + h + 3)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h', k⟩ => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2, k⟩
  have e0 := ea 0
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
  have mw : ∀ j < 4, word t.mem B (eN + 8 * (8 * i + h + j)) = word s₀.mem B (eN + 8 * (8 * i + h + j)) :=
    fun j hj => hI.out.word (by omega_using [sN, hj]) (by omega_using [hN, hn, hj])
  have mv0 := mw 0 (by decide); have mv1 := mw 1 (by decide)
  have mv2 := mw 2 (by decide); have mv3 := mw 3 (by decide)
  simp only [Nat.add_zero] at mv0
  rw [mv0] at m0; rw [mv1] at m1; rw [mv2] at m2; rw [mv3] at m3
  refine WP.mono (WP.keep [.rbp] (Q := fun t₂ => t₂.cf = some c ∧ t₂.mem = t₁.mem) (by
    unfold cfFromRbp; xrun [(k₁.gpr (by decide) : t₁.gpr .rbp = t.gpr .rbp), hbp, cf_mask]) rfl)
    fun t₂ ⟨⟨c₂, hm₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have g : ∀ r, r ∉ [Reg.rcx, .rdx, .r9, .r11, .rbp] → t₂.gpr r = t.gpr r := fun r hr => k12.gpr (by simpa using hr)
  have L0 : Lc s₀ B Z eT eN eo bit (8 * i + h) t₂ :=
    ⟨hI.scr.congr k12.2.2, by rw [hm₂, hm₁]; exact hI.out,
      ⟨c, c₂, by rw [hm₂, hm₁]; exact hval⟩⟩
  rw [show (List.range 4).flatMap (lazyWord h) = lazyWord h 0 ++ lazyWord h 1 ++ lazyWord h 2 ++ lazyWord h 3
    from rfl, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  have r8 : t₂.gpr .r8 = off B eT := (g .r8 (by decide)).trans h8
  have rbx : t₂.gpr .rbx = off B eo := (g .rbx (by decide)).trans hbx
  have r14 : t₂.gpr .r14 = BitVec.ofNat 64 (8 * i) := (g .r14 (by decide)).trans h14
  have q0 : (t₂.gpr .rcx).toNat = if bit then (word s₀.mem B (eN + 8 * (8 * i + h))).toNat else 0 := by
    rw [(k₂.gpr (by decide) : t₂.gpr .rcx = t₁.gpr .rcx), m0, mask_and]
  refine WP.mono (lst_ok (r := .rcx) (d := h + 0) (by decide) rfl r8 rbx r14 q0 L0
    (by omega_using [hT]) (by omega_using [ho]) (by omega_using [sT])) fun t₃ ⟨L1, k₃⟩ => ?_
  have q1 : (t₃.gpr .rdx).toNat = if bit then (word s₀.mem B (eN + 8 * (8 * i + h + 1))).toNat else 0 := by
    rw [(k₃.gpr (by decide) : t₃.gpr .rdx = t₂.gpr .rdx), (k₂.gpr (by decide) : t₂.gpr .rdx = t₁.gpr .rdx), m1,
      mask_and]
  refine WP.mono (lst_ok (r := .rdx) (d := h + 1) (by decide) (by omega_using []) ((k₃.gpr (by decide)).trans r8)
    ((k₃.gpr (by decide)).trans rbx) ((k₃.gpr (by decide)).trans r14) q1 L1
    (by omega_using [hT]) (by omega_using [ho]) (by omega_using [sT])) fun t₄ ⟨L2, k₄⟩ => ?_
  have k34 := k₃.trans k₄
  have q2 : (t₄.gpr .r9).toNat = if bit then (word s₀.mem B (eN + 8 * (8 * i + h + 2))).toNat else 0 := by
    rw [(k34.gpr (by decide) : t₄.gpr .r9 = t₂.gpr .r9), (k₂.gpr (by decide) : t₂.gpr .r9 = t₁.gpr .r9), m2,
      mask_and]
  refine WP.mono (lst_ok (r := .r9) (d := h + 2) (by decide) (by omega_using []) ((k34.gpr (by decide)).trans r8)
    ((k34.gpr (by decide)).trans rbx) ((k34.gpr (by decide)).trans r14) q2 L2
    (by omega_using [hT]) (by omega_using [ho]) (by omega_using [sT])) fun t₅ ⟨L3, k₅⟩ => ?_
  have k35 := k34.trans k₅
  have q3 : (t₅.gpr .r11).toNat = if bit then (word s₀.mem B (eN + 8 * (8 * i + h + 3))).toNat else 0 := by
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
  · have : x = 0 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst this; rfl
  · have : x = 1 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst this; rfl

/-- `lazyLoads co`: `w`, and the bases of `T` and `o`. -/
theorem lazyLoads_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {co o : Nat}
    (po : OpAt s.mem B w co o) (qo : co < 20) :
    WP isa (.block (lazyLoads co)) s fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aTmp) ∧ t.gpr .rbx = off B (slot w o) ∧
      t.mem = s.mem ∧ Keep [.r12, .r8, .rbx] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
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
  have hTs := Nat.le_trans (slot_le (w := w) (show aTmp < 8 by decide)) hZ
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
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hTs := sl aTmp (by decide)
  have hNs := sl aN (by decide)
  have hos := sl o ho
  have soT : slot w o + 8 * (w + 2) ≤ slot w aTmp ∨ slot w aTmp + 8 * (w + 2) ≤ slot w o := slot_sep (Ne.symm ho2) |>.symm
  -- `o` may be `m`'s array: each word of `m` is read before the word of `o` at its place is written
  have soN : slot w o ≤ slot w aN ∨ slot w aN + 8 * (w + 2) ≤ slot w o := by
    by_cases h : o = aN
    · exact .inl (by rw [h])
    · have := slot_sep (w := w) h; unfold slot aN at *; omega_using [this]
  -- the top words of `T`
  have hR := wv_lt s.mem B (slot w aN) w
  rw [wv_top2] at hTlt
  have hT1 : (word s.mem B (slot w aTmp + 8 * w + 8)).toNat = 0 := by
    rcases Nat.eq_zero_or_pos (word s.mem B (slot w aTmp + 8 * w + 8)).toNat with h | h
    · exact h
    · have : 2 ^ (64 * w) * 2 ^ 64 ≤ 2 ^ (64 * w) * ((word s.mem B (slot w aTmp + 8 * w)).toNat +
          2 ^ 64 * (word s.mem B (slot w aTmp + 8 * w + 8)).toNat) :=
        Nat.mul_le_mul_left _ (by have := Nat.mul_le_mul_left (2 ^ 64) h; omega)
      have : 2 ^ (64 * w) * 2 ^ 64 ≥ 2 * 2 ^ (64 * w) := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by decide)
      omega
  rw [hT1, Nat.mul_zero, Nat.add_zero] at hTlt
  have hTw : (word s.mem B (slot w aTmp + 8 * w)).toNat ≤ 1 := by
    rcases Nat.lt_or_ge (word s.mem B (slot w aTmp + 8 * w)).toNat 2 with h | h
    · omega
    · have : 2 ^ (64 * w) * 2 ≤ 2 ^ (64 * w) * (word s.mem B (slot w aTmp + 8 * w)).toNat :=
        Nat.mul_le_mul_left _ h
      omega
  generalize hbit : decide ((word s.mem B (slot w aTmp + 8 * w)).toNat = 1) = bit
  unfold Adx.lazy8
  refine WP.seq (WP.mono (lazyLoads_ok hs hdi hH hZ (hv.at po) (hv.lt po))
    fun s₀ ⟨h12₀, h8₀, hbx₀, hm₀, k₀⟩ => ?_)
  refine WP.seq (WP.mono (lazyMask_ok (hs.congr k₀.2.2) hZ h12₀ h8₀)
    fun s₁ ⟨h13, hbp, h14, hm₁', k₀₁⟩ => ?_)
  rw [hm₀, neg_bit_mask hTw, hbit] at h13
  have hm₁ : s₁.mem = s.mem := hm₁'.trans hm₀
  have k₁ := k₀.trans k₀₁
  have h12 : s₁.gpr .r12 = BitVec.ofNat 64 w := (k₀₁.gpr (by decide)).trans h12₀
  have h8 : s₁.gpr .r8 = off B (slot w aTmp) := (k₀₁.gpr (by decide)).trans h8₀
  have hbx : s₁.gpr .rbx = off B (slot w o) := (k₀₁.gpr (by decide)).trans hbx₀
  have k₁' : Keep (.r14 :: lazyRegs) s₁ s₁ := Keep.refl _ _
  have I0 : LazyInv s₁ B Z (slot w aTmp) (slot w aN) (slot w o) bit 0 s₁ :=
    ⟨⟨hs.congr k₁.2.2, Outside.refl _ _ _ _, ⟨false, hbp, by simp [mv, wv]⟩⟩, k₁', h14⟩
  have s₁10 : s₁.gpr .r10 = off B (slot w aN) := (k₁.gpr (by decide)).trans h10
  refine wp_upto (a := 0) (N := n) hn (LazyInv s₁ B Z (slot w aTmp) (slot w aN) (slot w o) bit) ?_ ?_ I0
  · intro i _ hi t hI
    have g : ∀ r, r ∉ (.r14 :: lazyRegs) → t.gpr r = s₁.gpr r := fun r hr => hI.keep.gpr hr
    have t8 := (g .r8 (by decide)).trans h8
    have t10 := (g .r10 (by decide)).trans s₁10
    have tbx := (g .rbx (by decide)).trans hbx
    have t13 := (g .r13 (by decide)).trans h13
    have t12 := (g .r12 (by decide)).trans h12
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (group_ok (h := 0) t8 t10 tbx hI.r14 t13 hI.lr (by omega_using [hTs, hi, hwN])
      (by omega_using [hNs, hi, hwN]) (by omega_using [hos, hi, hwN]) (by omega_using [soT, hi, hwN])
      (by omega_using [soN, hi, hwN])) fun t₁ ⟨L₁, kg₁⟩ => ?_
    refine WP.mono (group_ok (h := 4) ((kg₁.gpr (by decide)).trans t8) ((kg₁.gpr (by decide)).trans t10)
      ((kg₁.gpr (by decide)).trans tbx) ((kg₁.gpr (by decide)).trans hI.r14) ((kg₁.gpr (by decide)).trans t13)
      L₁ (by omega_using [hTs, hi, hwN]) (by omega_using [hNs, hi, hwN]) (by omega_using [hos, hi, hwN])
      (by omega_using [soT, hi, hwN]) (by omega_using [soN, hi, hwN])) fun t₂ ⟨L₂, kg₂⟩ => ?_
    have k12 := kg₁.trans kg₂
    refine WP.mono (count8_ok t₂ (r := .r12) (by decide) ((k12.gpr (by decide)).trans hI.r14)
      (N := n) (by rw [(k12.gpr (by decide) : t₂.gpr .r12 = t.gpr .r12), t12, hwN]) (by omega_using [hw, hi, hwN])
      (by omega_using [hw, hwN])) fun t' ⟨hz, h14', hm', k'⟩ => ⟨hz, ?_, ?_, h14'⟩
    · rw [show 8 * (i + 1) = 8 * i + 4 + 4 by omega]
      obtain ⟨c₂, b₂, v₂⟩ := L₂.val
      exact ⟨L₂.scr.congr k'.2.2, by rw [hm']; exact L₂.out,
        ⟨c₂, (k'.gpr (by decide)).trans b₂, by rw [hm']; exact v₂⟩⟩
    · exact ((hI.keep.trans k12).trans k').mono (by simp [lazyRegs])
  · intro t hI
    obtain ⟨c, _, hval⟩ := hI.lr.val
    rw [← hwN, hm₁] at hval
    have hout := hI.lr.out
    rw [← hwN, hm₁] at hout
    refine ⟨?_, Arrays.of_outside (j := o) (by simp) hout (Nat.le_refl _) (by omega),
      (k₁.trans hI.keep).mono (by simp [lazyRegs, mmRegs])⟩
    rw [wv_top2, hT1, Nat.mul_zero, Nat.add_zero]
    refine VG.Proof.Bignum.lazy_sub (wv_lt _ _ _ _) (Bool.toNat_le c) hTw hTlt ?_
    rw [← hbit] at hval
    simp only [mv] at hval
    by_cases h1 : (word s.mem B (slot w aTmp + 8 * w)).toNat = 1
    · simp only [h1, decide_true, ite_true, Nat.one_mul] at hval ⊢; exact hval
    · have h0 : (word s.mem B (slot w aTmp + 8 * w)).toNat = 0 := by omega
      simp only [h0, Nat.zero_mul, Nat.add_zero] at hval ⊢
      simpa using hval

end VG.Proof.Bignum.X86_64
