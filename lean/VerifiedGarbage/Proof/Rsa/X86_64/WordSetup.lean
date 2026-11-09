module

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv

/-! # Public pointer and counter setup for word remainders -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.WordDivide
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The window's first three words are available beyond the old sixteen arrays. -/
theorem window_bound {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) : slot W aV + 24 ≤ Z := by
  have hw := h.w1
  change 256 + 17 * (8 * (W + 2)) ≤ Z at hZ
  change 256 + 16 * (8 * (W + 2)) + 24 ≤ Z
  omega_using [hw, hZ]

theorem off_add (B : Addr) (e n : Nat) : off B e + BitVec.ofNat 64 n = off B (e + n) := by
  simp only [off, BitVec.ofNat_add, BitVec.add_assoc]

/-- Registers for the existing reciprocal routine, at half the workspace width. -/
theorem recipSetup_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W) :
    WP isa (.block recipSetup) s fun t =>
      t.gpr .r10 = off B (slot W aM) ∧ t.gpr .r8 = off B (slot W aV) ∧
      t.gpr .r12 = BitVec.ofNat 64 (W / 2) ∧ t.mem = s.mem ∧ Keep mmRegs s t := by
  have hw := h.w2
  rw [show recipSetup = ws ++ ((base aM .r10 ++ base aV .r8) ++ [.shift .shr .r12 1]) by
    simp only [recipSetup, List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok aM aV (r₁ := .r10) (r₂ := .r8) (by decide) (by decide) (by decide)
    ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun t₂ ⟨h10, h8, hm₂, k₂⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (W / 2) ∧ t.mem = t₂.mem)
    (by xrun [(k₂.gpr (by decide) : t₂.gpr .r12 = _), h12, shr1_ofNat W (by omega)]) rfl)
    fun t ⟨⟨h12', hm₃⟩, k₃⟩ => ?_
  exact ⟨(k₃.gpr (by decide)).trans h10, (k₃.gpr (by decide)).trans h8, h12',
    hm₃.trans (hm₂.trans hm₁), ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- Initialize the public word counter to the workspace width. -/
theorem countSetup_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) :
    WP isa (.block countSetup) s fun t => t.gpr .rax = BitVec.ofNat 64 W ∧
      t.mem = s.mem.writeW (off B (slot W aV + 16)) (BitVec.ofNat 64 W) ∧ Keep mmRegs s t := by
  have hv := window_bound h hZ
  unfold countSetup
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aV (r := .rbp) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9)
    fun t₂ ⟨hbp, hm₂, k₂⟩ => ?_
  have hs := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 W ∧
    t.mem = t₂.mem.writeW (off B (slot W aV + 16)) (BitVec.ofNat 64 W)) (by
      xrun [State.ea, wm, hbp, (k₂.gpr (by decide) : t₂.gpr .r12 = _), h12,
        BitVec.ofInt_natCast, off_add,
        hs.st (d := slot W aV + 16) (by omega)]) rfl) fun t ⟨⟨ha, hm⟩, k₃⟩ => ?_
  exact ⟨ha, by rw [hm, hm₂, hm₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- Decrement the public word counter and set the loop's condition. -/
theorem next_ok {s : State} {B : Addr} {Z W j : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hj : 1 ≤ j) (hjW : j ≤ W)
    (hc : word s.mem B (slot W aV + 16) = BitVec.ofNat 64 j) :
    WP isa (.block next) s fun t => t.gpr .rax = BitVec.ofNat 64 (j - 1) ∧
      t.zf = some (decide (j = 1)) ∧
      t.mem = s.mem.writeW (off B (slot W aV + 16)) (BitVec.ofNat 64 (j - 1)) ∧ Keep mmRegs s t := by
  have hv := window_bound h hZ
  have hw := h.w2
  unfold next
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨_, h9, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aV (r := .rbp) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9)
    fun t₂ ⟨hbp, hm₂, k₂⟩ => ?_
  have hs := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (j - 1) ∧
    t.zf = some (decide (j = 1)) ∧
    t.mem = t₂.mem.writeW (off B (slot W aV + 16)) (BitVec.ofNat 64 (j - 1))) (by
      xrun [State.ea, wm, hbp, BitVec.ofInt_natCast, off_add,
        hs.ld (d := slot W aV + 16) (by omega), hs.st (d := slot W aV + 16) (by omega),
        hm₂, hm₁, hc, ofNat64_pred hj (by omega), ofNat64_beq_zero (show j - 1 < 2 ^ 64 by omega)]
      simp only [show (j - 1 = 0) ↔ j = 1 by omega_using [hj]]) rfl) fun t ⟨⟨ha, hz, hm⟩, k₃⟩ => ?_
  exact ⟨ha, hz, by rw [hm, hm₂, hm₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- Before the indexed digit load, its address and index are public. -/
theorem stepLoad_ok {s : State} {B : Addr} {Z W j : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hc : word s.mem B (slot W aV + 16) = BitVec.ofNat 64 j) :
    WP isa (.block stepLoad) s fun t =>
      t.gpr .rdi = B ∧ t.gpr .r12 = BitVec.ofNat 64 W ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (W + 2)) ∧
      t.gpr .rbp = off B (slot W aV) ∧ t.gpr .r11 = off B (slot W aD) ∧
      t.gpr .rcx = BitVec.ofNat 64 j := by
  have hv := window_bound h hZ
  rw [show stepLoad = ws ++ ((base aV .rbp ++ base aD .r11) ++ [.mov .rcx (.mem (wm 16))]) by
    simp only [stepLoad, List.append_assoc], WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok aV aD (r₁ := .rbp) (r₂ := .r11) (by decide) (by decide) (by decide)
    ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun t₂ ⟨hbp, h11, hm₂, k₂⟩ => ?_
  have hs := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 j) (by
    xrun [State.ea, wm, hbp, BitVec.ofInt_natCast, off_add,
      hs.ld (d := slot W aV + 16) (by omega), hm₂, hm₁, hc]) rfl) fun t ⟨hcx, k₃⟩ => ?_
  exact ⟨(((k₁.trans k₂).trans k₃).gpr (by decide)).trans h.rdi,
    ((k₂.trans k₃).gpr (by decide)).trans h12, ((k₂.trans k₃).gpr (by decide)).trans h9,
    (k₃.gpr (by decide)).trans hbp, (k₃.gpr (by decide)).trans h11, hcx⟩

/-- Load the next secret digit using the public word counter. -/
theorem stepSetup_ok {s : State} {B : Addr} {Z W j : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hj : 1 ≤ j) (hjW : j ≤ W)
    (hc : word s.mem B (slot W aV + 16) = BitVec.ofNat 64 j) :
    WP isa (.block stepSetup) s fun t =>
      t.gpr .rbx = off B (slot W aR) ∧ t.gpr .r10 = off B (slot W aM) ∧
      t.gpr .r8 = off B (slot W aT) ∧ t.gpr .rbp = off B (slot W aV) ∧
      t.gpr .r12 = BitVec.ofNat 64 (W / 2) ∧
      t.mem = s.mem.writeW (off B (slot W aV + 8)) (word s.mem B (slot W aD + 8 * (j - 1))) ∧
      Keep mmRegs s t := by
  have hv := window_bound h hZ
  have hw := h.w2
  have hd : slot W aD + 8 * W ≤ Z := by
    have := h.hZ
    simp only [slot, aD] at this ⊢
    omega_using [this]
  rw [show stepSetup = ws ++ ((base aV .rbp ++ base aD .r11) ++
    ([.mov .rcx (.mem (wm 16)), .alu .sub .rcx (.imm 1), .mov .rdx (.mem (ix .r11 .rcx)),
      .store (wm 8) .rdx] ++ ((base aR .rbx ++ base aM .r10 ++ base aT .r8) ++ [.shift .shr .r12 1]))) by
    simp only [stepSetup, stepLoad, stepDigit, List.append_assoc, List.cons_append, List.nil_append]]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok aV aD (r₁ := .rbp) (r₂ := .r11) (by decide) (by decide) (by decide)
    ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun t₂ ⟨hbp, h11, hm₂, k₂⟩ => ?_
  have hs := h.scr.congr (k₁.trans k₂).2.2
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .rdx] (Q := fun t =>
    t.mem = t₂.mem.writeW (off B (slot W aV + 8)) (word s.mem B (slot W aD + 8 * (j - 1)))) (by
    xrun [State.ea, wm, ix, hbp, BitVec.ofInt_natCast, off_add,
      hs.ld (d := slot W aV + 16) (by omega), hs.st (d := slot W aV + 8) (by omega),
      hm₂, hm₁, hc, ofNat64_pred hj (by omega), addr0 h11 (rfl : BitVec.ofNat 64 (j - 1) = _),
      hs.ld (d := slot W aD + 8 * (j - 1)) (by omega)]) rfl) fun t₃ ⟨hm₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  have k03 := (k₁.trans k₂).trans k₃
  refine WP.mono (base3_ok aR aM aT (r₁ := .rbx) (r₂ := .r10) (r₃ := .r8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((k03.gpr (by decide)).trans h.rdi) ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h9))
    (by decide) (by decide)) fun t₄ ⟨hbx, h10, h8, hm₄, k₄⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (W / 2) ∧ t.mem = t₄.mem)
    (by xrun [(k₄.gpr (by decide) : t₄.gpr .r12 = _), (k₃.gpr (by decide) : t₃.gpr .r12 = _),
      (k₂.gpr (by decide) : t₂.gpr .r12 = _), h12, shr1_ofNat W (by omega)]) rfl)
    fun t ⟨⟨h12', hm₅⟩, k₅⟩ => ?_
  exact ⟨(k₅.gpr (by decide)).trans hbx, (k₅.gpr (by decide)).trans h10,
    (k₅.gpr (by decide)).trans h8, (((k₃.trans k₄).trans k₅).gpr (by decide)).trans hbp,
    h12', by rw [hm₅, hm₄, hm₃, hm₂, hm₁], (((k03.trans k₄).trans k₅).mono (by decide))⟩

end VG.Proof.Rsa.X86_64.WordDivide
