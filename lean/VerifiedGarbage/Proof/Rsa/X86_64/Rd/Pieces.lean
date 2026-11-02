module

public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.Rsa.X86_64.CvHead
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes

/-!
# `vg_rsa_recover_primes_det` on x86-64: the pieces

The pieces of `Impl/Rsa/X86_64/RecoverDet.lean` that the other key routines
do not have, in a working space of `w`-word numbers (`Ws`): a subtraction
(`subA_ok`), an addition (`addA_ok`), a halving (`shrA_ok`), a doubling with
a carry in, of `w` or `2 w + 2` words (`shlA_ok`), the widths (`width_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem ofNat_add2 (a : Nat) : BitVec.ofNat 64 a + 2 = BitVec.ofNat 64 (a + 2) := by
  rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat]

/-- Room for `c` arrays from array `j`. -/
theorem slot_room {w j c : Nat} (h : j + c ≤ 16) : slot w j + c * (8 * (w + 2)) ≤ slot w 16 := by
  have e := slot_add w j (16 - j)
  rw [show j + (16 - j) = 16 by omega_arith] at e
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show c ≤ 16 - j by omega_arith)
  omega_arith

/-- `ws`, then `rbp := 0` and three bases. -/
theorem wsBase3_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (i j k : Nat) {r₁ r₂ r₃ : Reg}
    (h₁ : r₁ ≠ .r9) (h₂ : r₂ ≠ .r9) (h₃ : r₃ ≠ .r9) (h₁₂ : r₂ ≠ r₁) (h₁₃ : r₃ ≠ r₁) (h₂₃ : r₃ ≠ r₂)
    (hr1 : r₁ ≠ .rdi) (hr2 : r₂ ≠ .rdi) (n1 : r₁ ≠ .r12) (n2 : r₂ ≠ .r12) (n3 : r₃ ≠ .r12)
    (b1 : r₁ ≠ .rbp) (b2 : r₂ ≠ .rbp) (b3 : r₃ ≠ .rbp) :
    WP isa (.block (ws ++ ([.mov32 .rbp (.imm 0)] : List Instr) ++ base i r₁ ++ base j r₂ ++ base k r₃)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .rbp = mask false ∧
      t.gpr r₁ = off B (slot w i) ∧ t.gpr r₂ = off B (slot w j) ∧ t.gpr r₃ = off B (slot w k) ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .rbp, r₁, r₂, r₃] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧ t.mem = s₁.mem) (by xrun) rfl)
    fun s₂ ⟨⟨hbp, m₂⟩, k₂⟩ => ?_
  refine WP.mono (base3_ok i j k h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ (w := w) (((k₁.trans k₂).gpr (by decide)).trans h.rdi)
    ((k₂.gpr (by decide)).trans h9) hr1 hr2) fun t ⟨e₁, e₂, e₃, m₃, k₃⟩ => ?_
  refine ⟨(k₃.gpr (by simp [n1.symm, n2.symm, n3.symm])).trans ((k₂.gpr (by decide)).trans h12),
    (k₃.gpr (by simp [h₁.symm, h₂.symm, h₃.symm])).trans ((k₂.gpr (by decide)).trans h9),
    (k₃.gpr (by simp [b1.symm, b2.symm, b3.symm])).trans hbp, e₁, e₂, e₃, by rw [m₃, m₂, m₁],
    ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `subA t a b`: `[t] := [a] - [b]` over `w` words, `rbp` the mask of its
borrow. -/
theorem subA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {t a b : Nat} (ht : t < 16) (ha : a < 16)
    (hb : b < 16) (hta : t ≠ a) (htb : t ≠ b) :
    WP isa (subA t a b) s fun s' =>
      s'.gpr .rbp = mask (decide (wv s.mem B (slot w a) w < wv s.mem B (slot w b) w)) ∧
      wv s'.mem B (slot w t) w + wv s.mem B (slot w b) w = wv s.mem B (slot w a) w +
        2 ^ (64 * w) * (decide (wv s.mem B (slot w a) w < wv s.mem B (slot w b) w)).toNat ∧
      Outside B (slot w t) (8 * w) s.mem s'.mem ∧ Keep [.r12, .r9, .rbp, .r8, .r10, .rsi, .rax, .r14] s s' := by
  have hn := h.scr.nowrap
  have st := h.sl ht
  have sa := h.sl ha
  have sb := h.sl hb
  have pta := slot_sep (w := w) hta
  have ptb := slot_sep (w := w) htb
  have hw1 := h.w1
  have hw2 := h.w2
  unfold subA
  refine WP.seq (WP.mono (wsBase3_ok h a b t (r₁ := .r8) (r₂ := .r10) (r₃ := .rsi) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₁ ⟨h12, _, hbp, h8, h10, hsi, m₁, k₁⟩ => ?_)
  refine WP.mono (sub_ok (h.scr.congr k₁.2.2) h8 h10 hsi h12 hbp (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₂ ⟨c, hc, hv, ho, k₂⟩ => ?_
  rw [m₁] at hv ho
  have e := lt_of_borrow (wv_lt _ _ _ _) hv
  subst e
  exact ⟨hc, hv, ho, (k₁.trans k₂).mono (by simp)⟩

/-- `addA o a b`: `[o] := [a] + [b]` modulo `2^(64 w)`. -/
theorem addA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {o a b : Nat} (ho : o < 16) (ha : a < 16)
    (hb : b < 16) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (addA o a b) s fun s' =>
      wv s'.mem B (slot w o) w = (wv s.mem B (slot w a) w + wv s.mem B (slot w b) w) % 2 ^ (64 * w) ∧
      Outside B (slot w o) (8 * w) s.mem s'.mem ∧
      Keep [.r12, .r9, .r15, .rbp, .r10, .r8, .rbx, .rax, .r14] s s' := by
  have hn := h.scr.nowrap
  have so := h.sl ho
  have sa := h.sl ha
  have sb := h.sl hb
  have poa := slot_sep (w := w) hoa
  have pob := slot_sep (w := w) hob
  have hw1 := h.w1
  have hw2 := h.w2
  unfold addA
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (WP.keep [.r15, .rbp] (Q := fun t => t.gpr .r15 = mask true ∧
      t.gpr .rbp = mask false ∧ t.mem = s₁.mem) (by xrun) rfl) fun s₂ ⟨⟨h15, hbp, m₂⟩, k₂⟩ =>
    WP.mono (base3_ok b a o (r₁ := .r10) (r₂ := .r8) (r₃ := .rbx) (w := w) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (((k₁.trans k₂).gpr (by decide)).trans h.rdi)
      ((k₂.gpr (by decide)).trans h9) (by decide) (by decide)) fun s₃ ⟨h10, h8, hbx, m₃, k₃⟩ => ?_)))
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (addM_ok (c := true) (h.scr.congr k13.2.2) hbx h10 h8 ((k₃.gpr (by decide)).trans h15)
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12)) ((k₃.gpr (by decide)).trans hbp)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₄ ⟨c, _, hv, hO, k₄⟩ => ?_
  rw [m₃, m₂, m₁] at hv hO
  refine ⟨?_, hO, (k13.trans k₄).mono (by simp)⟩
  simp only [ite_true] at hv
  have := wv_lt s₄.mem B (slot w o) w
  rw [Nat.add_comm (wv s.mem B (slot w a) w), ← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this]

/-- `shrA j`: `[j] := [j] / 2`, for a `[j]` whose word `w` is zero. -/
theorem shrA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16)
    (hz : word s.mem B (slot w j + 8 * w) = 0) :
    WP isa (shrA j) s fun s' =>
      wv s'.mem B (slot w j) w = wv s.mem B (slot w j) w / 2 ∧ Outside B (slot w j) (8 * w) s.mem s'.mem ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14] s s' := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hw1 := h.w1
  have hw2 := h.w2
  unfold shrA
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok j j (r₁ := .r8) (r₂ := .rsi) (w := w) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun s₂ ⟨h8, hsi, m₂, k₂⟩ => ?_))
  refine WP.mono (shr_ok (h.scr.congr (k₁.trans k₂).2.2) hsi h8 ((k₂.gpr (by decide)).trans h12) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (.inl (Nat.le_refl _))) fun t ⟨hv, ho, k₃⟩ => ?_
  rw [m₂, m₁, hz] at hv
  rw [m₂, m₁] at ho
  refine ⟨?_, ho, ((k₁.trans k₂).trans k₃).mono (by simp)⟩
  have := Nat.mod_lt (word s.mem B (slot w j)).toNat (show 0 < 2 by decide)
  have e : wv s.mem B (slot w j) w % 2 = (word s.mem B (slot w j)).toNat % 2 := by
    rw [wv_low (by omega_arith)]; omega_arith
  rw [show (0 : BitVec 64).toNat % 2 = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hv
  omega_arith

/-- The count of words of `shlA`. -/
abbrev shlN (wide : Bool) (w : Nat) : Nat := if wide then 2 * w + 2 else w

/-- `w` doubled and 2 added, if `wide`. -/
theorem wideIf_ok (wide : Bool) {w : Nat} {t₀ : State} (h12₀ : t₀.gpr .r12 = BitVec.ofNat 64 w) :
    WP isa (.block (if wide then wideR else [])) t₀ fun t =>
      (t.gpr .r12 = BitVec.ofNat 64 (shlN wide w) ∧ t.mem = t₀.mem) ∧ Keep [.r12] t₀ t := by
  cases wide
  · exact WP.keep [.r12] (by xrun [h12₀]; rfl) rfl
  · exact WP.keep [.r12] (by unfold wideR; xrun [h12₀, ofNat_dbl, ofNat_add2]; rfl) rfl

/-- `shlA wide j pre`: `[j] := 2 [j] + c₀` over `w` words, or `2 w + 2` if
`wide`, for the carry `c₀` into `rbp` that `pre` leaves; `rbp` the carry out. -/
theorem shlA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (wide : Bool) {j : Nat} {pre : List Instr}
    {c₀ : Bool} (hj : j + (if wide then 2 else 1) ≤ 16)
    (hpre : ∀ t : State, t.mem = s.mem → t.gpr .rbp = s.gpr .rbp → t.gpr .rdi = s.gpr .rdi → t.rd = s.rd →
      t.wr = s.wr → WP isa (.block pre) t fun t' => (t'.gpr .rbp = mask c₀ ∧ t'.mem = t.mem) ∧ Keep [.rbp] t t') :
    WP isa (shlA wide j pre) s fun s' => ∃ c : Bool, s'.gpr .rbp = mask c ∧
      wv s'.mem B (slot w j) (shlN wide w) + 2 ^ (64 * shlN wide w) * c.toNat =
        2 * wv s.mem B (slot w j) (shlN wide w) + c₀.toNat ∧
      Outside B (slot w j) (8 * shlN wide w) s.mem s'.mem ∧ Keep [.r12, .r9, .rbx, .rbp, .rax, .r14] s s' := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have sj : slot w j + 8 * shlN wide w ≤ Z := by
    have := slot_room (w := w) hj
    have := h.hZ
    cases wide <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] at this hj ⊢ <;> omega_arith
  have hN1 : 1 ≤ shlN wide w := by cases wide <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] <;> omega_arith
  have hN2 : shlN wide w < 2 ^ 31 := by
    cases wide <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] <;> omega_arith
  unfold shlA
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (wideIf_ok wide h12)
    fun s₂ ⟨⟨h12₂, m₂⟩, k₂⟩ => WP.block_append_iff.mpr (WP.mono (base_ok j (r := .rbx) (w := w) (by decide)
      (((k₁.trans k₂).gpr (by decide)).trans h.rdi) ((k₂.gpr (by decide)).trans h9))
    fun s₃ ⟨hbx, m₃, k₃⟩ => WP.mono (hpre s₃ (by rw [m₃, m₂, m₁])
      (((k₁.trans k₂).trans k₃).gpr (by decide)) (((k₁.trans k₂).trans k₃).gpr (by decide))
      ((k₁.trans k₂).trans k₃).2.1 ((k₁.trans k₂).trans k₃).2.2)
    fun s₄ ⟨⟨hbp, m₄⟩, k₄⟩ => ?_))))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  refine WP.mono (shl_ok (h.scr.congr k14.2.2) ((k₄.gpr (by decide)).trans hbx)
    ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h12₂)) hbp hN1 hN2 sj)
    fun t ⟨c, hc, hv, ho, k₅⟩ => ?_
  rw [m₄, m₃, m₂, m₁] at hv ho
  exact ⟨c, hc, hv, ho, (k14.trans k₅).mono (by simp)⟩

/-! ## The widths -/

/-- The narrow width `v = ⌈k / 8⌉ + 1`, and the wide one `2 v + 2`. -/
abbrev nv (k : Nat) : Nat := wk k + 1
abbrev wW (k : Nat) : Nat := 2 * nv k + 2
abbrev widthOf (wide : Bool) (k : Nat) : Nat := if wide then wW k else nv k

/-- Wide array `j` is narrow arrays `2 j` and `2 j + 1`. -/
theorem slot_wide (k j : Nat) : slot (wW k) j = slot (nv k) (2 * j) := by
  simp only [slot, hdrBytes]; grind

/-- The wide width from the narrow one, if `wide`. -/
theorem widen_ok (wide : Bool) {k : Nat} {t₀ : State} (h12₀ : t₀.gpr .r12 = BitVec.ofNat 64 (nv k)) :
    WP isa (.block (if wide then ([.alu .add .r12 (.reg .r12), .alu .add .r12 (.imm 2)] : List Instr) else []))
      t₀ fun t => (t.gpr .r12 = BitVec.ofNat 64 (widthOf wide k) ∧ t.mem = t₀.mem) ∧ Keep [.r12] t₀ t := by
  cases wide
  · exact WP.keep [.r12] (by xrun [h12₀]; rfl) rfl
  · exact WP.keep [.r12] (by xrun [h12₀, ofNat_dbl, ofNat_add2]; rfl) rfl

/-- `width wide`: `w`, the arrays' bases and the stride of the narrow or wide
width. -/
theorem width_ok {s : State} {B : Addr} {Z k : Nat} (wide : Bool) (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hk1 : 64 ≤ k) (hk2 : k ≤ 1024) (hZ : 128 * k ≤ Z)
    (hK : word s.mem B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 k) :
    WP isa (.block (width wide)) s fun t =>
      Ws t B Z (widthOf wide k) ∧ Frm B [(8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8)] s.mem t.mem ∧
        Keep [.rax, .rdx, .r12] s t := by
  have hn := hs.nowrap
  have hZ16 : slot (widthOf wide k) 16 ≤ Z := by
    cases wide <;> simp only [widthOf, ↓reduceIte, Bool.false_eq_true, slot, hdrBytes, wk, nv, wW] <;> omega_arith
  have eK : Impl.Bignum.X86_64.Public.sK = 18 := rfl
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  unfold width
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (nv k) ∧ t.mem = s.mem) ?_ rfl)
    fun t₀ ⟨⟨h12₀, hm₀⟩, k₀⟩ => ?_
  · xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * Impl.Bignum.X86_64.Public.sK) (by omega_arith), hK,
      shr3_w k (by omega_arith)]
    rw [← ofNat_add_one]
  refine WP.mono (widen_ok wide h12₀) fun t₁' ⟨⟨h12₁', hm₁'⟩, k₁'⟩ => ?_
  have hs₁' := hs.congr (k₀.trans k₁').2.2
  have hdi₁' : t₁'.gpr .rdi = B := ((k₀.trans k₁').gpr (by decide)).trans hdi
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₁'.mem.writeW (off B (8 * sW))
      (BitVec.ofNat 64 (widthOf wide k))) (by
    xrun [State.ea, hdr, hdi₁', hdrOff, hs₁'.st (d := 8 * sW) (by omega_arith), h12₁']) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  have hs₁ := hs₁'.congr k₁.2.2
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi₁'
  have h12 : t₁.gpr .r12 = BitVec.ofNat 64 (widthOf wide k) := (k₁.gpr (by decide)).trans h12₁'
  refine WP.mono (setBases_ok hs₁ hdi₁ h12 (by unfold sArr; omega_arith)) fun t₂ ⟨hb₂, ho₂, k₂⟩ => ?_
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  have h12₂ : t₂.gpr .r12 = BitVec.ofNat 64 (widthOf wide k) := (k₂.gpr (by decide)).trans h12
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = t₂.mem.writeW (off B (8 * sStride))
      (BitVec.ofNat 64 (8 * (widthOf wide k + 2)))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, h12₂, hs₂.st (d := 8 * sStride) (by omega_arith), ofNat_dbl]
    congr 1
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, ofNat_dbl, ofNat_dbl, ofNat_dbl]
    congr 1; omega_arith) rfl) fun t ⟨hm, k₃⟩ => ?_
  have o1 := writeW_outside t₂.mem B (BitVec.ofNat 64 (8 * (widthOf wide k + 2))) (d := 8 * sStride) (by omega_arith)
  rw [← hm] at o1
  have kk := (((k₀.trans k₁').trans k₁).trans k₂).trans k₃
  refine ⟨⟨hs₂.congr k₃.2.2, (k₃.gpr (by decide)).trans hdi₂, ?_, ?_, fun j hj => ?_, hZ16,
    by cases wide <;> simp only [widthOf, ↓reduceIte, Bool.false_eq_true, wk, nv, wW] <;> omega_arith,
    by cases wide <;> simp only [widthOf, ↓reduceIte, Bool.false_eq_true, wk, nv, wW] <;> omega_arith⟩,
    ?_, kk.mono (by simp)⟩
  · rw [o1.word (by omega_arith) (by omega_arith), ho₂.word (by omega_arith) (by omega_arith), hm₁, word_writeW_self]
  · rw [hm, word_writeW_self]
  · rw [o1.word (by unfold sArr; omega_arith) (by unfold sArr; omega_arith)]
    exact hb₂ j hj
  · intro x hx
    have a := hx (8 * sW, 8) (by simp)
    have b := hx (8 * sArr 0, 64) (by simp)
    have c := hx (8 * sStride, 8) (by simp)
    dsimp only at a b c
    rw [o1 x c, ho₂ x b, hm₁, writeW_outside t₁'.mem B _ (by omega_arith) x a, hm₁', hm₀]

/-! ## Frames as predicates on offsets -/

/-- Memory that changes only at offsets from `B` that `P` allows. -/
def FrmP (B : Addr) (P : Nat → Prop) (m m' : Mem) : Prop := ∀ x, ¬ P (ofs B x) → m' x = m x

theorem FrmP.refl (B : Addr) (P : Nat → Prop) (m : Mem) : FrmP B P m m := fun _ _ => rfl

theorem FrmP.trans {B : Addr} {P : Nat → Prop} {m₁ m₂ m₃ : Mem} (h₁ : FrmP B P m₁ m₂) (h₂ : FrmP B P m₂ m₃) :
    FrmP B P m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem FrmP.mono {B : Addr} {P P' : Nat → Prop} {m m' : Mem} (h : FrmP B P m m') (hP : ∀ y, P y → P' y) :
    FrmP B P' m m' := fun x hx => h x fun h' => hx (hP _ h')

theorem FrmP.of_out {B : Addr} {P : Nat → Prop} {m m' : Mem} {o n : Nat} (h : Outside B o n m m')
    (hP : ∀ y, o ≤ y → y < o + n → P y) : FrmP B P m m' := fun x hx =>
  h x (by
    rcases Nat.lt_or_ge (ofs B x) o with h1 | h1
    · exact .inl h1
    · rcases Nat.lt_or_ge (ofs B x) (o + n) with h2 | h2
      · exact absurd (hP _ h1 h2) hx
      · exact .inr h2)

theorem FrmP.of_frm {B : Addr} {P : Nat → Prop} {m m' : Mem} {rs : List (Nat × Nat)} (h : Frm B rs m m')
    (hP : ∀ r ∈ rs, ∀ y, r.1 ≤ y → y < r.1 + r.2 → P y) : FrmP B P m m' := fun x hx =>
  h x fun r hr => by
    rcases Nat.lt_or_ge (ofs B x) r.1 with h1 | h1
    · exact .inl h1
    · rcases Nat.lt_or_ge (ofs B x) (r.1 + r.2) with h2 | h2
      · exact absurd (hP r hr _ h1 h2) hx
      · exact .inr h2

theorem FrmP.of_frm2 {B : Addr} {m m' : Mem} {o₁ n₁ o₂ n₂ : Nat} (h : Frm B [(o₁, n₁), (o₂, n₂)] m m') :
    FrmP B (fun y => (o₁ ≤ y ∧ y < o₁ + n₁) ∨ (o₂ ≤ y ∧ y < o₂ + n₂)) m m' :=
  FrmP.of_frm h fun r hr y h1 h2 => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨h1, h2⟩
    · exact .inr ⟨h1, h2⟩

theorem FrmP.of_eq {B : Addr} {P : Nat → Prop} {m m' : Mem} (h : m' = m) : FrmP B P m m' := fun _ _ => by rw [h]

theorem FrmP.word_eq {B : Addr} {P : Nat → Prop} {m m' : Mem} (h : FrmP B P m m') {d : Nat}
    (hd : ∀ y, d ≤ y → y < d + 8 → ¬ P y) (hd' : d + 8 ≤ 2 ^ 64) : word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => (h _ (by
    rw [ofs_off B (d := d) (i := i) (by omega_arith)]
    exact hd _ (by omega_arith) (by omega_arith))).symm).symm

theorem FrmP.wv_eq {B : Addr} {P : Nat → Prop} {m m' : Mem} (h : FrmP B P m m') {d k : Nat}
    (hd : ∀ y, d ≤ y → y < d + 8 * k → ¬ P y) (hd' : d + 8 * k ≤ 2 ^ 64) : wv m' B d k = wv m B d k :=
  wv_congr fun i hi => h.word_eq (fun y h1 h2 => hd y (by omega_arith) (by omega_arith)) (by omega_arith)

/-- A store to a header slot. -/
theorem FrmP.of_writeW {B : Addr} {P : Nat → Prop} {m : Mem} {d : Nat} (v : BitVec 64) (hd : d + 8 ≤ 2 ^ 64)
    (hP : ∀ y, d ≤ y → y < d + 8 → P y) : FrmP B P m (m.writeW (off B d) v) :=
  FrmP.of_out (writeW_outside m B v hd) hP

/-- The offsets the recovery's pieces may change: the arrays, and the header
slots of `sElen` (20), `sMask` (22), the count and the masks (25 to 27), and
29 to 31 (`sMo`, `sC`). -/
def DOk (y : Nat) : Prop :=
  256 ≤ y ∨ (160 ≤ y ∧ y < 168) ∨ (176 ≤ y ∧ y < 184) ∨ (200 ≤ y ∧ y < 224) ∨ (232 ≤ y ∧ y < 256)

theorem _root_.VG.Proof.Rsa.X86_64.Ws.congrP {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {P : Nat → Prop}
    (hf : FrmP B P s.mem t.mem) (hP : ∀ y, P y → DOk y) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs) : Ws t B Z w := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hh : ∀ i, i ∈ [sW, sStride] ∨ (8 ≤ i ∧ i < 16) → word t.mem B (8 * i) = word s.mem B (8 * i) := by
    intro i hi
    have hi' : i = 6 ∨ i = 28 ∨ (8 ≤ i ∧ i < 16) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, sW, sStride, sFn] at hi; omega_arith
    exact hf.word_eq (fun y h1 h2 hy => by have := hP y hy; unfold DOk at this; omega_arith) (by omega_arith)
  exact ⟨h.scr.congr k.2.2, (k.gpr hr).trans h.rdi, (hh sW (.inl (by simp))).trans h.hw,
    (hh sStride (.inl (by simp))).trans h.hS, fun j hj => (hh (sArr j) (.inr (by unfold sArr; omega_arith))).trans
      (h.harr j hj), h.hZ, h.w1, h.w2⟩

/-- `Ws` after a piece that changes only bytes from offset 256 on. -/
theorem _root_.VG.Proof.Rsa.X86_64.Ws.congrO {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {o n : Nat}
    (ho : Outside B o n s.mem t.mem) (h256 : 256 ≤ o) {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) :
    Ws t B Z w :=
  h.congrP (P := fun y => o ≤ y ∧ y < o + n) (FrmP.of_out ho fun _ h1 h2 => ⟨h1, h2⟩)
    (fun y hy => .inl (by omega_arith)) k hr

/-- `Ws` after a store to a header slot the pieces may change. -/
theorem _root_.VG.Proof.Rsa.X86_64.Ws.congrW {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {i : Nat}
    {v : BitVec 64} (hm : t.mem = s.mem.writeW (off B (8 * i)) v) (hi : DOk (8 * i)) (hi' : i < 32)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : Ws t B Z w :=
  h.congrP (P := fun y => 8 * i ≤ y ∧ y < 8 * i + 8)
    (by rw [hm]; exact FrmP.of_writeW _ (by have := h.h256; have := h.scr.nowrap; omega_arith) fun _ h1 h2 => ⟨h1, h2⟩)
    (fun y hy => by unfold DOk at hi ⊢; omega_arith) k hr

/-- `loadA_ok`, with the array's two words above the number zero too. -/
theorem loadA2_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {p : Addr}
    {bs : List Byte} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : word s.mem B (8 * sPtr) = p) (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hsrc : Src s B Z p bs) (hlen : bs.length = len) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w) :
    WP isa (seqs (loadA j sPtr sLen)) s fun t =>
      wv t.mem B (slot w j) (w + 2) = Spec.Rsa.os2ip bs ∧ Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧
        Keep [.r12, .r9, .r8, .rax, .r14, .rbx, .rsi, .rcx, .rdx, .rbp] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hw2 := h.w2
  simp only [loadA, seqs]
  refine WP.seq (WP.mono (zeroA_ok h hj) fun s₁ ⟨hz, o₁, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot w j _) k₁ (by decide)
  have hh : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    o₁.word (Or.inl (by have := hdr_lt_slot w j hi; omega_arith)) (by omega_arith)
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h₁.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ =>
    WP.mono (base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h₁.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.gpr .rsi = p ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.mem = s₃.mem) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h₁.rdi
          have hs₃ := h₁.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega_arith)
          xrun [State.ea, hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hh sPtr hP, hh sLen hL, hp, hl]) rfl)
      fun s₄ ⟨⟨hsi, hcx, m₄⟩, k₄⟩ => ?_)))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hs₄ := h.scr.congr k14.2.2
  have hsrc₄ : Src s₄ B Z p bs := hsrc.congrK (fun x hx => by
    rw [m₄, m₃, m₂]; exact o₁ x (Or.inr (by omega_arith))) k14
  refine WP.mono (loadBE_ok (w := (len + 7) / 8) hs₄ hsi hcx ((k₄.gpr (by decide)).trans hbx) hlen hl1 (by omega_arith) rfl
    (by omega_arith) (fun i hi => hsrc₄.rd i (by omega_arith)) (fun i hi => hsrc₄.val i (by omega_arith))
    (fun i hi => Or.inr (by have := hsrc₄.out i (by omega_arith); omega_arith))) fun t ⟨hv, o, k₅⟩ => ?_
  rw [m₄, m₃, m₂] at o
  refine ⟨?_, fun x hx => by rw [o x (by omega_arith), o₁ x hx], (k14.trans k₅).mono (by decide)⟩
  -- The words above the loaded ones are still zero.
  have hz' : ∀ q < w + 2, word s₁.mem B (slot w j + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz
  have e := wv_add t.mem B (slot w j) ((len + 7) / 8) (w + 2 - (len + 7) / 8)
  rw [show (len + 7) / 8 + (w + 2 - (len + 7) / 8) = w + 2 by omega_arith] at e
  rw [e, hv, wv_zero (n := w + 2 - (len + 7) / 8) fun q hq => by
      rw [o.word (by omega_arith) (by omega_arith), Nat.add_assoc, ← Nat.mul_add]; exact hz' _ (by omega_arith)]
  simp

end VG.Proof.Rsa.X86_64.Rd
