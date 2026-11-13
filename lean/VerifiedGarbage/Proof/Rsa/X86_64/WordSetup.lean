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
import VerifiedGarbage.Proof.Bignum.X86_64.Copy

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

/-- The first digit's index, `X - W / 2 + 1` for the dividend's `X` words (`start`). -/
def j0 (W : Nat) : Option Nat → Nat
  | none => W - W / 2 + 1
  | some k => k + 1

/-- The dividend's words. -/
def xw (W : Nat) : Option Nat → Nat
  | none => W
  | some k => W / 2 + k

theorem j0_add {W : Nat} (top : Option Nat) (hW : 2 ≤ W) : j0 W top + (W / 2 - 1) = xw W top := by
  cases top <;> simp only [j0, xw] <;> omega

/-- `start top`: the first digit's index into `rax`, `r12` halved. -/
theorem start_ok {s : State} {W : Nat} {top : Option Nat} (h12 : s.gpr .r12 = BitVec.ofNat 64 W)
    (hW : W < 2 ^ 32) (hk : ∀ k, top = some k → k < 2 ^ 30) :
    WP isa (.block (start top)) s fun t => t.gpr .rax = BitVec.ofNat 64 (j0 W top) ∧
      t.gpr .r12 = BitVec.ofNat 64 (W / 2) ∧ t.mem = s.mem ∧ Keep [.rax, .r12] s t := by
  cases top with
  | none =>
    refine WP.mono (WP.keep [.rax, .r12] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (j0 W none) ∧
      t.gpr .r12 = BitVec.ofNat 64 (W / 2) ∧ t.mem = s.mem)
      (by
        xrun [start, h12, shr1_ofNat W (by omega)]
        apply BitVec.eq_of_toNat_eq
        have e1 : (1 : BitVec 64).toNat = 1 := rfl
        simp only [j0, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, e1]
        omega) rfl) fun t ⟨⟨ha, h12', hm⟩, k⟩ => ⟨ha, h12', hm, k⟩
  | some k =>
    have := hk k rfl
    refine WP.mono (WP.keep [.rax, .r12] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (j0 W (some k)) ∧
      t.gpr .r12 = BitVec.ofNat 64 (W / 2) ∧ t.mem = s.mem)
      (by
        xrun [start, h12, shr1_ofNat W (by omega)]
        apply BitVec.eq_of_toNat_eq
        simp only [j0, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        omega) rfl) fun t ⟨⟨ha, h12', hm⟩, k⟩ => ⟨ha, h12', hm, k⟩

/-- A first digit's index computation: from `W` in `r12`, `st` leaves the index `j` in `rax` and
`W / 2` in `r12`, and changes nothing else; the dividend's `j + (W / 2 - 1)` words fit in `W`. -/
structure StartOk (st : List Instr) (W j : Nat) : Prop where
  pos : 1 ≤ j
  fit : j + (W / 2 - 1) ≤ W
  lt : j < 2 ^ 31
  run : ∀ {s : State}, s.gpr .r12 = BitVec.ofNat 64 W →
    WP isa (.block st) s fun t => t.gpr .rax = BitVec.ofNat 64 j ∧
      t.gpr .r12 = BitVec.ofNat 64 (W / 2) ∧ t.mem = s.mem ∧ Keep [.rax, .r12] s t

/-- `start top`'s index is `j0 W top`. -/
theorem start_startOk {W : Nat} (hW : 6 ≤ W) (hW' : W < 2 ^ 30) {top : Option Nat}
    (hk : ∀ k, top = some k → k ≤ W / 2) : StartOk (start top) W (j0 W top) where
  pos := by cases top <;> simp only [j0] <;> omega
  fit := by
    rw [j0_add top (by omega)]; cases top with
    | none => simp only [xw]; omega
    | some k => have := hk k rfl; simp only [xw]; omega
  lt := by
    cases top with
    | none => simp only [j0]; omega
    | some k => have := hk k rfl; simp only [j0]; omega
  run h12 := start_ok h12 (by omega) fun k e => by have := hk k e; omega

/-- `seedSetupWith st`: `rsi` at the dividend's word `j₀`, `rbx` at the remainder, `r12 = W / 2 - 1`. -/
theorem seedSetupWith_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W) {st : List Instr} {j : Nat}
    (hst : StartOk st W j) :
    WP isa (.block (seedSetupWith st)) s fun t =>
      t.gpr .rsi = off B (slot W aD + 8 * j) ∧ t.gpr .rbx = off B (slot W aR) ∧
      t.gpr .r12 = BitVec.ofNat 64 (W / 2 - 1) ∧ t.mem = s.mem ∧ Keep mmRegs s t := by
  have hw := h.w2
  have hw1 := h.w1
  have hj := hst.lt
  unfold seedSetupWith
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hst.run h12) fun t₂ ⟨ha₂, h12₂, hm₂, k₂⟩ => ?_
  rw [show ([.shift .shl .rax 3] ++ (base aD .rsi ++ ([.alu .add .rsi (.reg .rax)] ++
      (base aR .rbx ++ [.alu .sub .r12 (.imm 1)]))) : List Instr) =
    [.shift .shl .rax 3] ++ (base aD .rsi ++ ([.alu .add .rsi (.reg .rax)] ++
      (base aR .rbx ++ [.alu .sub .r12 (.imm 1)]))) from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (8 * j) ∧ t.mem = t₂.mem)
    (by
      xrun [ha₂]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega) rfl) fun t₃ ⟨⟨ha₃, hm₃⟩, k₃⟩ => ?_
  have k13 := (k₁.trans k₂).trans k₃
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aD (r := .rsi) (by decide) ((k13.gpr (by decide)).trans h.rdi)
    (((k₂.trans k₃).gpr (by decide)).trans h9)) fun t₄ ⟨hsi, hm₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = off B (slot W aD + 8 * j) ∧ t.mem = t₄.mem)
    (by xrun [hsi, (k₄.gpr (by decide) : t₄.gpr .rax = _), ha₃, off_add]) rfl) fun t₅ ⟨⟨hsi₅, hm₅⟩, k₅⟩ => ?_
  have k15 := (k13.trans k₄).trans k₅
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aR (r := .rbx) (by decide) ((k15.gpr (by decide)).trans h.rdi)
    ((((k₂.trans k₃).trans k₄).trans k₅).gpr (by decide) |>.trans h9)) fun t₆ ⟨hbx, hm₆, k₆⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (W / 2 - 1) ∧ t.mem = t₆.mem)
    (by
      xrun [(k₆.gpr (by decide) : t₆.gpr .r12 = _), (k₅.gpr (by decide) : t₅.gpr .r12 = _),
        (k₄.gpr (by decide) : t₄.gpr .r12 = _), (k₃.gpr (by decide) : t₃.gpr .r12 = _), h12₂,
        ofNat64_pred (show 1 ≤ W / 2 by omega) (by omega)]) rfl) fun t ⟨⟨h12', hm₇⟩, k₇⟩ => ?_
  exact ⟨(k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans hsi₅), (k₇.gpr (by decide)).trans hbx, h12',
    by rw [hm₇, hm₆, hm₅, hm₄, hm₃, hm₂, hm₁], ((k15.trans k₆).trans k₇).mono (by decide)⟩

/-- `seedWith st`: the remainder's low `W / 2 - 1` words the dividend's from `j₀` on, for a dividend of
`j₀ + (W / 2 - 1) ≤ W` words. -/
theorem seedWith_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W) (hW : 6 ≤ W) {st : List Instr} {j : Nat}
    (hst : StartOk st W j) :
    WP isa (seedWith st) s fun t =>
      wv t.mem B (slot W aR) (W / 2 - 1) = wv s.mem B (slot W aD + 8 * j) (W / 2 - 1) ∧
      Outside B (slot W aR) (8 * (W / 2 - 1)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hw := h.w2
  have hR := h.sl (j := aR) (by decide)
  have hD := h.sl (j := aD) (by decide)
  have hx := hst.fit
  have sep : slot W aR + 8 * (W + 2) ≤ slot W aD := by simp only [slot, aR, aD]; omega_arith
  unfold seedWith
  refine WP.seq (WP.mono (seedSetupWith_ok h hst)
    fun s₁ ⟨hsi, hbx, h12, m₁, k₁⟩ => ?_)
  have hs₁ := h.scr.congr k₁.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega) (by omega) (by omega_arith)
    (fun i hi => hs₁.ld (by omega_arith)) (fun i hi => hs₁.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun t ⟨hv, _, o', k₂⟩ => ?_
  rw [m₁] at hv o'
  exact ⟨hv, o', (k₁.trans k₂).mono (by decide)⟩

/-- Initialize the public word counter to the first digit's index. -/
theorem countSetupWith_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) {st : List Instr} {j : Nat} (hst : StartOk st W j) :
    WP isa (.block (countSetupWith st)) s fun t => t.gpr .rax = BitVec.ofNat 64 (j) ∧
      t.mem = s.mem.writeW (off B (slot W aV + 16)) (BitVec.ofNat 64 (j)) ∧ Keep mmRegs s t := by
  have hv := window_bound h hZ
  have hw := h.w2
  unfold countSetupWith
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aV (r := .rbp) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9)
    fun t₂ ⟨hbp, hm₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hst.run ((k₂.gpr (by decide)).trans h12))
    fun t₃ ⟨ha₃, _, hm₃, k₃⟩ => ?_
  have hs := h.scr.congr ((k₁.trans k₂).trans k₃).2.2
  refine WP.mono (WP.keep [] (Q := fun t =>
    t.mem = t₃.mem.writeW (off B (slot W aV + 16)) (BitVec.ofNat 64 (j))) (by
      xrun [State.ea, wm, (k₃.gpr (by decide) : t₃.gpr .rbp = _), hbp, ha₃,
        BitVec.ofInt_natCast, off_add,
        hs.st (d := slot W aV + 16) (by omega)]) rfl) fun t ⟨hm, k₄⟩ => ?_
  exact ⟨(k₄.gpr (by decide)).trans ha₃, by rw [hm, hm₃, hm₂, hm₁], (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩

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
