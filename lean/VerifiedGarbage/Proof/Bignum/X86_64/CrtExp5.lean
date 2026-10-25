module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Proof.Bignum.CrtWin5
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math

/-!
# RSA with the CRT on x86-64: the exponentiation by windows of 5 bits

`Crt.expLoop5` (`Impl/Rsa/X86_64/Crt.lean`): `tabBuildN` writes the table
of the 32 powers, then each window takes the top 5 of the exponent's bits
kept at the top of `sV`, after `padBits L` zero bits (`padInit_ok`), a byte
more read below them when fewer than 5 are left (`refill_ok`).

The bits are those of `CrtWin5.lean`: after `i` bytes, with `b` bits left,
`sV = (P mod 2^b) 2^(64 - b)` for the value `P` of the bytes read,
`sPow = 2^(56 - b)`, and `Y ≡ x^⌊P / 2^b⌋ R`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## What the exponentiation changes -/

/-- What `expLoop5` changes: `crtExpRanges` with a table of 32 entries, and
`sPow`. -/
def crtExpRanges5 (wx : Nat) : List (Nat × Nat) := (8 * Crt.sPow, 8) :: crtExpRanges wx 32

theorem crtExpRanges_sub5 (wx : Nat) : ∀ r ∈ crtExpRanges wx 32, r ∈ crtExpRanges5 wx :=
  fun _ h => List.mem_cons_of_mem _ h

theorem crtExpRanges5_ok (wx : Nat) :
    ∀ r ∈ crtExpRanges5 wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + tabBytes wx 32 := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · have := hdr_lt_slot wx 8 (show Crt.sPow < 32 by decide)
    simp only [Crt.sPow, sFn] at *; omega_arith
  · exact crtExpRanges_ok wx r hr

theorem crtExpRanges5_arr (wx : Nat) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aY)
    (h4 : j ≠ Crt.aT) : ∀ r ∈ crtExpRanges5 wx, slot wx j + 8 * (wx + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot wx j := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · have := hdr_lt_slot wx j (show Crt.sPow < 32 by decide)
    simp only [Crt.sPow, sFn] at *; omega_arith
  · exact crtExpRanges_arr wx hj h1 h2 h3 h4 (n := 32) r hr

/-- Two different header words are disjoint. -/
theorem hdr_sep {k s : Nat} (h : k ≠ s) : 8 * k + 8 ≤ 8 * s ∨ 8 * s + 8 ≤ 8 * k := by omega

/-- A header slot that `expLoop5`'s ranges miss. -/
theorem crtExpRanges5_hdr (wx : Nat) {k : Nat} (hk : k < 32) (h0 : k ≠ Crt.sPow) (h1 : k ≠ Crt.sExp)
    (h2 : k ≠ Crt.sExpLen) (h3 : k ≠ Crt.sI) (h4 : k ≠ Crt.sTab) (h5 : k ≠ Crt.sV) (h6 : k ≠ Crt.sBit)
    (h7 : k ≠ Crt.sNib) (h8 : k ≠ Crt.sEnt) (h9 : k ≠ Crt.sJ) :
    ∀ r ∈ crtExpRanges5 wx, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  simp only [crtExpRanges5, crtExpRanges, crtWinRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [hdr_sep h0, hdr_sep h1, hdr_sep h2, hdr_sep h3, hdr_sep h4, Or.inl (hdr_lt_slot wx _ hk),
    Or.inl (hdr_lt_slot wx _ hk), Or.inl (hdr_lt_slot wx _ hk), Or.inl (hdr_lt_slot wx _ hk),
    Or.inl (hdr_lt_slot wx _ hk), hdr_sep h5, hdr_sep h6, hdr_sep h7, hdr_sep h8, hdr_sep h9]

/-- What changes only within `expLoop5`'s ranges keeps the context. -/
theorem CExpCtx.of_frm5 {t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc 32) (hf : Frm P (crtExpRanges5 wx) t.mem t'.mem) (hwr : t'.wr = t.wr)
    (hdi : t'.gpr .rdi = t.gpr .rdi) : CExpCtx t' P wx minv X Xc 32 := by
  have hn := hc.scrT.nowrap
  have rN := crtExpRanges5_arr wx (j := aN) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rX := crtExpRanges5_arr wx (j := Crt.aXc) (by decide) (by decide) (by decide) (by decide) (by decide)
  have lN := slot_le (w := wx) (show aN < 8 by decide)
  have lX := slot_le (w := wx) (show Crt.aXc < 8 by decide)
  have hh : ∀ i < 17, word t'.mem P (8 * i) = word t.mem P (8 * i) := fun i hi =>
    hf.word_eq (fun r hr => Or.inl (by have := crtExpRanges5_ok wx r hr; omega_arith))
      (by have := hdr_lt_slot wx 8 (show i < 32 by omega_arith); omega_arith)
  exact ⟨⟨hc.good.scr.congr hwr, hdi.trans hc.good.rdi,
    ⟨(hh _ (by decide)).trans hc.good.hdr.hw, (hh _ (by decide)).trans hc.good.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (hc.good.hdr.harr j hj)⟩⟩, hc.scrT.congr hwr,
    by rw [hf.wv_eq (fun r hr => by have := rN r hr; omega_arith) (by omega_arith)]; exact hc.n,
    by rw [hf.word_eq (fun r hr => by have := rN r hr; omega_arith) (by omega_arith)]; exact hc.inv,
    by rw [hf.wv_eq (fun r hr => by have := rX r hr; omega_arith) (by omega_arith)]; exact hc.x⟩

/-- The prime's workspace with room for a table of 32 entries. -/
theorem SubCtx.scr32 {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : SubCtx t B Z o w wx minv)
    (hT : o + slot wx 8 + wsTab wx ≤ Z) : Scr t (off B o) (slot wx 8 + tabBytes wx 32) :=
  h.scr.sub (by simp only [wsTab] at hT; omega_arith) (by unfold slot hdrBytes; omega_arith)

/-! ## The padding -/

theorem toNat_ofNat_of_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `⌊L / 5⌋`: the high word of `L M` shifted right by 2. -/
theorem div5_bv {L : Nat} (hL : L < 2 ^ 32) :
    BitVec.ofNat 64 ((0xCCCCCCCCCCCCCCCD : BitVec 64).toNat * (BitVec.ofNat 64 L).toNat / 2 ^ 64) >>> 2 =
      BitVec.ofNat 64 (L / 5) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ofNat_of_lt (by omega_arith : L < 2 ^ 64), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (0xCCCCCCCCCCCCCCCD : BitVec 64).toNat = 0xCCCCCCCCCCCCCCCD from rfl, Nat.mul_comm,
    toNat_ofNat_of_lt (by simp only [Nat.reducePow] at *; omega_arith), toNat_ofNat_of_lt (by omega_arith), div5_magic hL]

/-- `2 (L mod 5)` from `⌊L / 5⌋` by additions and a subtraction. -/
theorem mod5x2_bv (L : Nat) :
    (BitVec.ofNat 64 L - (BitVec.ofNat 64 (L / 5) + BitVec.ofNat 64 (L / 5) +
        (BitVec.ofNat 64 (L / 5) + BitVec.ofNat 64 (L / 5)) + BitVec.ofNat 64 (L / 5))) +
      (BitVec.ofNat 64 L - (BitVec.ofNat 64 (L / 5) + BitVec.ofNat 64 (L / 5) +
        (BitVec.ofNat 64 (L / 5) + BitVec.ofNat 64 (L / 5)) + BitVec.ofNat 64 (L / 5))) =
      BitVec.ofNat 64 (2 * (L % 5)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- `rdx := ⌊L / 5⌋` and `rcx := L`, `L` in `sExpLen`. -/
theorem padDiv_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n L : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hL : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L) (hL' : L < 2 ^ 32) :
    WP isa (.block [.mov .rcx (.mem (hdr Crt.sExpLen)), .movImm64 .rax 0xCCCCCCCCCCCCCCCD, .mul .rcx,
      .shift .shr .rdx 2]) t fun t' =>
      t'.gpr .rdx = BitVec.ofNat 64 (L / 5) ∧ t'.gpr .rcx = BitVec.ofNat 64 L ∧ t'.mem = t.mem ∧
      Keep [.rax, .rcx, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t' => t'.gpr .rdx = BitVec.ofNat 64 (L / 5) ∧
      t'.gpr .rcx = BitVec.ofNat 64 L ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sExpLen) (by decide), hL]
  exact div5_bv hL'

/-- `rax := padBits L` into `sBit`, from `rdx = ⌊L / 5⌋` and `rcx = L`. -/
theorem padMod_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n L : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hdx : t.gpr .rdx = BitVec.ofNat 64 (L / 5))
    (hcx : t.gpr .rcx = BitVec.ofNat 64 L) :
    WP isa (.block [.mov .rax (.reg .rdx), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rdx), .alu .sub .rcx (.reg .rax), .alu .add .rcx (.reg .rcx), .mov .rax (.reg .rcx),
      .alu .sub .rax (.imm 5), .cmov .b .rax (.reg .rcx), .store (hdr Crt.sBit) .rax]) t fun t' =>
      t'.gpr .rax = BitVec.ofNat 64 (padBits L) ∧
      t'.mem = t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (padBits L)) ∧
      Keep [.rax, .rcx] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t' => t'.gpr .rax = BitVec.ofNat 64 (padBits L) ∧
      t'.mem = t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (padBits L))) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  have h2r : (BitVec.ofNat 64 (2 * (L % 5))).toNat = 2 * (L % 5) := toNat_ofNat_of_lt (by omega_arith)
  have hpad := padBits_eq L
  by_cases h5 : 2 * (L % 5) < 5
  · rw [ite_eq_left h5] at hpad
    rw [← hpad]
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.st (i := Crt.sBit) (by decide), hdx, hcx, mod5x2_bv, execCmov, eval,
      h2r, show (5 : BitVec 64).toNat = 5 from rfl, h5]
  · rw [ite_eq_right h5] at hpad
    have e : BitVec.ofNat 64 (2 * (L % 5)) - 5 = BitVec.ofNat 64 (padBits L) := by
      rw [← hpad]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, h2r, toNat_ofNat_of_lt (by omega_arith)]
      simp only [show (5 : BitVec 64).toNat = 5 from rfl]; omega_arith
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.st (i := Crt.sBit) (by decide), hdx, hcx, mod5x2_bv, execCmov, eval,
      h2r, show (5 : BitVec 64).toNat = 5 from rfl, h5, e]

/-- One step of `2 ^ (56 - b)`: halve `rcx` once `b ≥ k + 1`. -/
theorem padStep_ok {s : State} {b k : Nat} (hb : b < 5) (hk : k < 4) (hax : s.gpr .rax = BitVec.ofNat 64 b)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (2 ^ (56 - min b k))) :
    WP isa (.block [.mov .rdx (.reg .rcx), .shift .shr .rdx 1, .alu .cmp .rax (.imm (BitVec.ofNat 32 (k + 1))),
      .cmov .ae .rcx (.reg .rdx)]) s fun s' => s'.gpr .rax = BitVec.ofNat 64 b ∧
        s'.gpr .rcx = BitVec.ofNat 64 (2 ^ (56 - min b (k + 1))) ∧ s'.mem = s.mem ∧
        s'.gpr .rdi = s.gpr .rdi ∧ s'.wr = s.wr := by
  have e1 : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_of_lt (by omega)
  have e2 := (by decide : ∀ k < 4, (BitVec.signExtend 64 (BitVec.ofNat 32 (k + 1))).toNat = k + 1) k hk
  by_cases h : k + 1 ≤ b
  · have v : ∀ k < 4, BitVec.ofNat 64 (2 ^ (56 - k)) >>> 1 = BitVec.ofNat 64 (2 ^ (56 - (k + 1))) := by decide
    xrun [hax, hcx, e1, e2, execCmov, eval, show ¬ b < k + 1 by omega, Nat.min_eq_right (by omega : k ≤ b),
      Nat.min_eq_right h, v k hk]
  · xrun [hax, hcx, e1, e2, execCmov, eval, show b < k + 1 by omega, Nat.min_eq_left (by omega : b ≤ k),
      Nat.min_eq_left (by omega : b ≤ k + 1)]

/-- `sV := 0` and `sPow := 2^(56 - b)` for `b < 5` in `rax`: `2^56` halved
for each of 1 to 4 that is at most `b`. -/
theorem padPow_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n b : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hax : t.gpr .rax = BitVec.ofNat 64 b) (hb : b < 5) :
    WP isa (.block (([.mov32 .rcx (.imm 0), .store (hdr Crt.sV) .rcx, .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 56))] : List Instr) ++
      (List.range 4).flatMap (fun k => [.mov .rdx (.reg .rcx), .shift .shr .rdx 1,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 (k + 1))), .cmov .ae .rcx (.reg .rdx)]) ++
      ([.store (hdr Crt.sPow) .rcx] : List Instr))) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
        (off P (8 * Crt.sPow)) (BitVec.ofNat 64 (2 ^ (56 - b))) ∧ Keep [.rax, .rcx, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t' => t'.mem = (t.mem.writeW (off P (8 * Crt.sV))
      (BitVec.setWidth 64 (0 : BitVec 32))).writeW (off P (8 * Crt.sPow)) (BitVec.ofNat 64 (2 ^ (56 - b)))) ?_
      (by decide))
    fun t' ⟨h, k⟩ => ⟨h, k⟩
  have hdi := hc.good.rdi
  have hsp := hc.st (i := Crt.sPow) (by decide)
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr ?_)
  refine WP.mono (Q := fun (s₁ : State) => s₁.gpr .rax = BitVec.ofNat 64 b ∧
    s₁.gpr .rcx = BitVec.ofNat 64 (2 ^ (56 - min b 0)) ∧
    s₁.mem = t.mem.writeW (off P (8 * Crt.sV)) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
    s₁.gpr .rdi = t.gpr .rdi ∧ s₁.wr = t.wr) ?_ fun s₁ h₁ => ?_
  · xrun [State.ea, hdr, hdi, hdrOff, hc.st (i := Crt.sV) (by decide), hax, Nat.min_zero, Nat.sub_zero]
  refine WP.mono (wp_range_flatMap (fun k (s : State) => s.gpr .rax = BitVec.ofNat 64 b ∧
    s.gpr .rcx = BitVec.ofNat 64 (2 ^ (56 - min b k)) ∧
    s.mem = t.mem.writeW (off P (8 * Crt.sV)) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
    s.gpr .rdi = t.gpr .rdi ∧ s.wr = t.wr)
    (fun k s hk h => WP.mono (padStep_ok hb hk h.1 h.2.1) fun _ h' =>
      ⟨h'.1, h'.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1, h'.2.2.2.2.trans h.2.2.2.2⟩)
    4 (Nat.le_refl _) s₁ h₁) fun s₂ ⟨_, hcx, hm, hdi₂, hwr⟩ => ?_
  rw [Nat.min_eq_left (by omega : b ≤ 4)] at hcx
  xrun [State.ea, hdr, hdi₂, hdi, hdrOff, hwr, hsp, hcx, hm]

theorem padInit_eq : Crt.padInit =
    ([.mov .rcx (.mem (hdr Crt.sExpLen)), .movImm64 .rax 0xCCCCCCCCCCCCCCCD, .mul .rcx, .shift .shr .rdx 2] :
      List Instr) ++
    (([.mov .rax (.reg .rdx), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx),
      .alu .sub .rcx (.reg .rax), .alu .add .rcx (.reg .rcx), .mov .rax (.reg .rcx), .alu .sub .rax (.imm 5),
      .cmov .b .rax (.reg .rcx), .store (hdr Crt.sBit) .rax] : List Instr) ++
    (([.mov32 .rcx (.imm 0), .store (hdr Crt.sV) .rcx, .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 56))] : List Instr) ++
      (List.range 4).flatMap (fun k => [.mov .rdx (.reg .rcx), .shift .shr .rdx 1,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 (k + 1))), .cmov .ae .rcx (.reg .rdx)]) ++
      ([.store (hdr Crt.sPow) .rcx] : List Instr))) := rfl

/-- `padInit`: `sBit := padBits L` for the exponent's length `L` in
`sExpLen`, `sV := 0` and `sPow := 2^(56 - padBits L)`. -/
theorem padInit_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n L : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hL : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L) (hL' : L < 2 ^ 32) :
    WP isa (.block Crt.padInit) t fun t' =>
      t'.mem = ((t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (padBits L))).writeW (off P (8 * Crt.sV))
        (BitVec.setWidth 64 (0 : BitVec 32))).writeW (off P (8 * Crt.sPow)) (BitVec.ofNat 64 (2 ^ (56 - padBits L))) ∧
      Keep [.rax, .rcx, .rdx] t t' := by
  rw [padInit_eq, WP.block_append_iff]
  refine WP.mono (padDiv_ok hc hL hL') fun t₁ ⟨hdx, hcx, hm₁, k₁⟩ => ?_
  have hc₁ : CExpCtx t₁ P wx minv X Xc n := hc.of_frm (by rw [hm₁]; exact Frm.refl _ _ _) k₁.2.2 (k₁.gpr (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (padMod_ok hc₁ hdx hcx) fun t₂ ⟨hax, hm₂, k₂⟩ => ?_
  have o₂ := writeW_outside t₁.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (padBits L)) (by decide)
  rw [← hm₂] at o₂
  have hc₂ : CExpCtx t₂ P wx minv X Xc n :=
    hc₁.of_frm (Frm.of_outside o₂ (by simp [crtExpRanges, crtWinRanges])) k₂.2.2 (k₂.gpr (by decide))
  refine WP.mono (padPow_ok hc₂ hax (padBits_lt L)) fun t' ⟨hm', k'⟩ => ⟨?_, ((k₁.trans k₂).trans k').mono (by decide)⟩
  rw [hm', hm₂, hm₁]

/-! ## A window's blocks -/

/-- `imul`'s result: the low word of the product. -/
theorem imul_eq (a b : BitVec 64) : BitVec.ofInt 64 (a.toInt * b.toInt) = a * b := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, BitVec.toInt_mul]

theorem shr8_pow {b : Nat} (hb : b < 5) :
    BitVec.ofNat 64 (2 ^ (56 - b)) >>> 8 = BitVec.ofNat 64 (2 ^ (56 - (b + 8))) := by
  rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl <;> decide

theorem shl5_pow {b : Nat} (hb : 5 ≤ b) (hb' : b ≤ 12) :
    BitVec.ofNat 64 (2 ^ (56 - b)) <<< 5 = BitVec.ofNat 64 (2 ^ (56 - (b - 5))) := by
  rcases (by omega_arith : b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ofNat_add8 (b : Nat) : BitVec.ofNat 64 b + 8 = BitVec.ofNat 64 (b + 8) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]

theorem ofNat_sub5 {b : Nat} (hb : 5 ≤ b) (hb' : b < 2 ^ 64) : BitVec.ofNat 64 b - 5 = BitVec.ofNat 64 (b - 5) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat_of_lt hb', toNat_ofNat_of_lt (by omega_arith),
    show (5 : BitVec 64).toNat = 5 from rfl]
  omega_arith

/-- `CF := b < 5`, `b` in `sBit`. -/
theorem bitCmp_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n b : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hb : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb' : b < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .cmp .rax (.imm 5)]) t fun t' =>
      t'.cf = some (decide (b < 5)) ∧ t'.mem = t.mem ∧ Keep [.rax] t t' := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.cf = some (decide (b < 5)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sBit) (by decide), hb, toNat_ofNat_of_lt hb',
    show (5 : BitVec 64).toNat = 5 from rfl]

/-- A byte more below the `b < 5` bits at the top of `sV`: the byte `y` at
`ep + i` (`sExp`, `sI`), by a multiplication by `sPow = 2^(56 - b)`. -/
theorem refill_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n : Nat}
    (hc : CExpCtx t P wx minv X Xc n) {ep : Addr} {i b r : Nat} {y : Byte}
    (he : word t.mem P (8 * Crt.sExp) = ep) (hi : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i)
    (hp : word t.mem P (8 * Crt.sPow) = BitVec.ofNat 64 (2 ^ (56 - b)))
    (hv : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (r * 2 ^ (64 - b)))
    (hbit : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb : b < 5) (hr : r < 2 ^ b)
    (hrd : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1) (hy : t.mem (ep + BitVec.ofNat 64 i) = y) :
    WP isa (.block Crt.refill) t fun t' =>
      t'.mem = (((t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 ((256 * r + y.toNat) * 2 ^ (56 - b)))).writeW
        (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i + 1))).writeW (off P (8 * Crt.sPow))
          (BitVec.ofNat 64 (2 ^ (56 - (b + 8))))).writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b + 8)) ∧
      Keep [.rax, .rcx, .rdx, .r8] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .r8] (Q := fun t' => t'.mem = (((t.mem.writeW (off P (8 * Crt.sV))
      (BitVec.ofNat 64 ((256 * r + y.toNat) * 2 ^ (56 - b)))).writeW (off P (8 * Crt.sI))
        (BitVec.ofNat 64 (i + 1))).writeW (off P (8 * Crt.sPow)) (BitVec.ofNat 64 (2 ^ (56 - (b + 8))))).writeW
          (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b + 8))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩
  have hw := refill_word hb hr y.isLt
  unfold Crt.refill
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sExp) (by decide), hc.ld (i := Crt.sI) (by decide),
    hc.ld (i := Crt.sPow) (by decide), hc.ld (i := Crt.sBit) (by decide), hc.ld (i := Crt.sV) (by decide),
    hc.st (i := Crt.sV) (by decide), hc.st (i := Crt.sI) (by decide), hc.st (i := Crt.sPow) (by decide),
    hc.st (i := Crt.sBit) (by decide), he, hi, hp, hv, hbit, byteRead, hrd, hy, execImul, imul_eq, setWidth_byte,
    Nat.pow_zero, Nat.mul_one, hw, ofNat_add_one, shr8_pow hb, ofNat_add8]

/-- The window: `sNib := ` the top 5 of the `b ≥ 5` bits at the top of `sV`,
the others moved up 5, `b - 5` left. -/
theorem takeWin_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n : Nat}
    (hc : CExpCtx t P wx minv X Xc n) {b r : Nat}
    (hp : word t.mem P (8 * Crt.sPow) = BitVec.ofNat 64 (2 ^ (56 - b)))
    (hv : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (r * 2 ^ (64 - b)))
    (hbit : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb : 5 ≤ b) (hb' : b ≤ 12) (hr : r < 2 ^ b) :
    WP isa (.block Crt.takeWin) t fun t' =>
      t'.mem = (((t.mem.writeW (off P (8 * Crt.sPow)) (BitVec.ofNat 64 (2 ^ (56 - (b - 5))))).writeW
        (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b - 5))).writeW (off P (8 * Crt.sNib))
          (BitVec.ofNat 64 (r / 2 ^ (b - 5)))).writeW (off P (8 * Crt.sV))
            (BitVec.ofNat 64 (r % 2 ^ (b - 5) * 2 ^ (64 - (b - 5)))) ∧
      Keep [.rax, .rcx, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t' => t'.mem = (((t.mem.writeW (off P (8 * Crt.sPow))
      (BitVec.ofNat 64 (2 ^ (56 - (b - 5))))).writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b - 5))).writeW
        (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (r / 2 ^ (b - 5)))).writeW (off P (8 * Crt.sV))
          (BitVec.ofNat 64 (r % 2 ^ (b - 5) * 2 ^ (64 - (b - 5))))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩
  unfold Crt.takeWin
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sV) (by decide), hc.ld (i := Crt.sPow) (by decide),
    hc.ld (i := Crt.sBit) (by decide), hc.st (i := Crt.sPow) (by decide), hc.st (i := Crt.sBit) (by decide),
    hc.st (i := Crt.sNib) (by decide), hc.st (i := Crt.sV) (by decide), hp, hv, hbit, shl5_pow hb hb',
    ofNat_sub5 hb (by omega_arith), take_hi hb hb' hr, take_lo hb hb' hr]

/-- `ZF` once no byte nor bit is left: `L - i + b = 0`. -/
theorem winEnd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n L i b : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hL : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L)
    (hi : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i) (hbit : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b)
    (hiL : i ≤ L) (hL' : L < 2 ^ 32) (hb : b < 2 ^ 32) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sExpLen)), .alu .sub .rax (.mem (hdr Crt.sI)),
      .alu .add .rax (.mem (hdr Crt.sBit))]) t fun t' =>
      t'.zf = some (decide (L - i + b = 0)) ∧ t'.mem = t.mem ∧ Keep [.rax] t t' := by
  have e : BitVec.ofNat 64 L - BitVec.ofNat 64 i + BitVec.ofNat 64 b = BitVec.ofNat 64 (L - i + b) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub, toNat_ofNat_of_lt (by omega_arith), toNat_ofNat_of_lt (by omega_arith),
      toNat_ofNat_of_lt (by omega_arith), toNat_ofNat_of_lt (by omega_arith)]
    omega_arith
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (decide (L - i + b = 0)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sExpLen) (by decide), hc.ld (i := Crt.sI) (by decide),
    hc.ld (i := Crt.sBit) (by decide), hL, hi, hbit, e, ofNat64_beq_zero (show L - i + b < 2 ^ 64 by omega_arith)]

/-! ## The window's invariant -/

/-- A store to a header slot is within `expLoop5`'s ranges if the slot is. -/
theorem frm5_hdrW (m : Mem) (P : Addr) (wx : Nat) {k : Nat} (v : BitVec 64) (hk : (8 * k, 8) ∈ crtExpRanges5 wx)
    (hk' : k < 32) : Frm P (crtExpRanges5 wx) m (m.writeW (off P (8 * k)) v) :=
  Frm.of_outside (writeW_outside m P v (by omega_arith)) hk

/-- Words past the header are kept by a store to a header slot. -/
theorem wv_hdrW (m : Mem) (P : Addr) {k d n : Nat} (v : BitVec 64) (hk : k < 32) (hd : 8 * 32 ≤ d)
    (hn : d + 8 * n ≤ 2 ^ 64) : wv (m.writeW (off P (8 * k)) v) P d n = wv m P d n :=
  (writeW_outside m P v (by omega_arith)).wv (by omega_arith) hn

/-- The table is kept by a store to a header slot but `sTab`. -/
theorem _root_.VG.Proof.Bignum.CTab.hdrW {m : Mem} {P : Addr} {wx X : Nat} {Q : Prop} {x n k : Nat} (h : CTab m P wx X Q x n)
    (v : BitVec 64) (hk : k < 32) (hkt : k ≠ Crt.sTab) (hn : slot wx 8 + tabBytes wx n ≤ 2 ^ 64) :
    CTab (m.writeW (off P (8 * k)) v) P wx X Q x n := by
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have he : ∀ j < n, wv (m.writeW (off P (8 * k)) v) P (slot wx (8 + j)) wx = wv m P (slot wx (8 + j)) wx :=
    fun j hj => wv_hdrW m P v hk (by have := slot_mono wx (show 8 ≤ 8 + j by omega_arith); omega_arith)
      (by have := ent_le wx hj; omega_arith)
  exact ⟨by rw [hdrStore_hdr _ _ _ hk (by decide) hkt]; exact h.tab, fun j hj => (he j hj).symm ▸ h.lt j hj,
    fun hq j hj => (he j hj).symm ▸ h.val hq j hj⟩

/-- After `i` bytes of the exponent (`L` bytes `eb` at `ep`) from `t₀`, `b`
of their bits left at the top of `sV`: `Y ≡ x^⌊P / 2^b⌋ R` for the value `P`
of the bytes read. -/
structure W5At (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x : Nat)
    (ep : Addr) (L : Nat) (eb : List Byte) (i b : Nat) (t : State) : Prop where
  ctx : CExpCtx t P wx minv X Xc 32
  tab : CTab t.mem P wx X Q x 32
  ylt : wv t.mem P (slot wx aY) wx < X
  y : Q → wv t.mem P (slot wx aY) wx % X = x ^ (pre eb i / 2 ^ b) * 2 ^ (64 * wx) % X
  v : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (pre eb i % 2 ^ b * 2 ^ (64 - b))
  bit : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b
  pow : word t.mem P (8 * Crt.sPow) = BitVec.ofNat 64 (2 ^ (56 - b))
  idx : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i
  e : word t.mem P (8 * Crt.sExp) = ep
  len : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L
  frm : Frm P (crtExpRanges5 wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

theorem W5At.of_mem {t₀ t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop} {x : Nat}
    {ep : Addr} {L : Nat} {eb : List Byte} {i b : Nat} (h : W5At t₀ P wx minv X Xc Q x ep L eb i b t)
    (hm : t'.mem = t.mem) {rs : List Reg} (k : Keep rs t t') (hrs : ∀ r ∈ rs, r ∈ mmRegs)
    (hdi : t'.gpr .rdi = t.gpr .rdi) : W5At t₀ P wx minv X Xc Q x ep L eb i b t' :=
  ⟨h.ctx.of_frm5 (by rw [hm]; exact Frm.refl _ _ _) k.2.2 hdi, hm ▸ h.tab, hm ▸ h.ylt,
    hm ▸ h.y, hm ▸ h.v, hm ▸ h.bit, hm ▸ h.pow, hm ▸ h.idx, hm ▸ h.e, hm ▸ h.len, hm ▸ h.frm,
    (h.keep.trans k).mono fun r hr => by
      rcases List.mem_append.mp hr with h' | h'
      · exact h'
      · exact hrs r h'⟩

/-- A byte more if fewer than 5 bits are left: then `b ≥ 5`. -/
theorem fill_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop} {x : Nat}
    {ep : Addr} {L : Nat} {eb : List Byte} {i b : Nat} (hL : eb.length = L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot wx 8 + tabBytes wx 32 ≤ ofs P (ep + BitVec.ofNat 64 i))
    (hb : b < 8) (hiL : i ≤ L) (hfill : b < 5 → i < L) (hI : W5At t₀ P wx minv X Xc Q x ep L eb i b t) :
    WP isa (seqs [.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .cmp .rax (.imm 5)],
        .ite .b (.block Crt.refill) (.block [])]) t fun t' =>
      ∃ i' b', 5 ≤ b' ∧ b' ≤ 12 ∧ 8 * i' + b = 8 * i + b' ∧ i' ≤ L ∧ W5At t₀ P wx minv X Xc Q x ep L eb i' b' t' := by
  have hn := hI.ctx.scrT.nowrap
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hY1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (bitCmp_ok hI.ctx hI.bit (by omega_arith)) fun t₁ ⟨hcf, hm₁, k₁⟩ => ?_)
  have hI₁ := hI.of_mem hm₁ k₁ (by decide) (k₁.gpr (by decide))
  refine WP.ite (decide (b < 5)) (by simp only [eval, hcf]) (fun h5 => ?_) (fun h5 => ?_)
  · have h5' : b < 5 := of_decide_eq_true h5
    have hi : i < L := hfill h5'
    have hrdi : InRegions (t₁.rd ++ t₁.wr) (ep + BitVec.ofNat 64 i) 1 := by
      rw [hI₁.keep.2.1, hI₁.keep.2.2]; exact hrd i hi
    have hbi : t₁.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith) := by
      rw [hI₁.frm _ fun r hr => Or.inr (by have := (crtExpRanges5_ok wx r hr).2; have := hout i hi; omega_arith)]
      exact hbytes i hi
    have hr : pre eb i % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
    refine WP.mono (refill_ok hI₁.ctx hI₁.e hI₁.idx hI₁.pow hI₁.v hI₁.bit h5' hr hrdi hbi) fun t₂ ⟨hm₂, k₂⟩ =>
      ⟨i + 1, b + 8, by omega_arith, by omega_arith, by omega_arith, by omega_arith, ?_⟩
    have hv := (refill_val (P := pre eb i) (b := b) (eb[i]'(by omega_arith)).isLt)
    rw [← pre_succ eb (by omega_arith)] at hv
    have hm : t₂.mem = (((t₁.mem.writeW (off P (8 * Crt.sV))
        (BitVec.ofNat 64 ((256 * (pre eb i % 2 ^ b) + (eb[i]'(by omega_arith)).toNat) * 2 ^ (56 - b)))).writeW
          (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i + 1))).writeW (off P (8 * Crt.sPow))
            (BitVec.ofNat 64 (2 ^ (56 - (b + 8))))).writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b + 8)) := hm₂
    have f₂ : Frm P (crtExpRanges5 wx) t₁.mem t₂.mem := by
      rw [hm]
      exact (((frm5_hdrW _ P wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide)).trans
        (frm5_hdrW _ P wx _ (by simp [crtExpRanges5, crtExpRanges]) (by decide))).trans
        (frm5_hdrW _ P wx _ (by simp [crtExpRanges5]) (by decide))).trans
        (frm5_hdrW _ P wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))
    have hY : wv t₂.mem P (slot wx aY) wx = wv t₁.mem P (slot wx aY) wx := by
      rw [hm, wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith), wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith),
        wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith), wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith)]
    have hnT : slot wx 8 + tabBytes wx 32 ≤ 2 ^ 64 := by omega_arith
    refine ⟨hI₁.ctx.of_frm5 f₂ k₂.2.2 (k₂.gpr (by decide)), ?_, hY ▸ hI₁.ylt, fun hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hI₁.frm.trans f₂, (hI₁.keep.trans k₂).mono (by decide)⟩
    · rw [hm]
      exact (((hI₁.tab.hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide)
        (by decide) hnT).hdrW _ (by decide) (by decide) hnT
    · rw [hY, hI₁.y hq, hv.2]
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        word_writeW_self, hv.1, show 64 - (b + 8) = 56 - b by omega_arith]
    · rw [hm, word_writeW_self]
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hI₁.e
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hI₁.len
  · have h5' : ¬ b < 5 := fun h => absurd (decide_eq_true h) (by rw [h5]; decide)
    exact WP.block_nil ⟨i, b, by omega_arith, by omega_arith, by omega_arith, hiL, hI₁⟩

/-! ## A window -/

theorem expWin5_eq (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sel : List (Prog isa)) :
    Crt.expWin5 sq mul sel =
    ([.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .cmp .rax (.imm 5)], .ite .b (.block Crt.refill) (.block [])] : List (Prog isa)) ++
    ([sq, sq, sq, sq, sq, .block Crt.takeWin] ++
      (sel ++ [mul aY aY Crt.aT, .block [.mov .rax (.mem (hdr Crt.sExpLen)), .alu .sub .rax (.mem (hdr Crt.sI)),
        .alu .add .rax (.mem (hdr Crt.sBit))]])) := rfl

/-- A header slot but `sEnt` and `sJ` is kept by a change within `selRanges`. -/
theorem sel_hdr {m m' : Mem} {P : Addr} {wx : Nat} (f : Frm P (selRanges wx) m m') {k : Nat} (hk : k < 32)
    (h1 : k ≠ Crt.sEnt) (h2 : k ≠ Crt.sJ) : word m' P (8 * k) = word m P (8 * k) :=
  f.word_eq (fun r hr => by
    have := hdr_lt_slot wx Crt.aT hk
    simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only; omega_arith
    · simp only [Crt.sEnt, sFn] at h1 ⊢; omega_arith
    · simp only [Crt.sJ, sFn] at h2 ⊢; omega_arith) (by omega_arith)

/-- The last window: no byte nor bit left after it. -/
theorem win5_last {K p L i j b i' b' : Nat} (hK : 5 * K = p + 8 * L) (hib : p + 8 * i = 5 * j + b)
    (hrel : 8 * i' + b = 8 * i + b') (hiL : i' ≤ L) (hb5 : 5 ≤ b') (hb12 : b' ≤ 12) :
    L - i' + (b' - 5) = 0 ↔ j + 1 = K := by
  have e : 5 * K + 5 = 5 * (j + 1) + 8 * (L - i') + b' := by omega_using [hK, hib, hrel, hiL]
  constructor
  · intro h
    rw [Nat.add_eq_zero_iff, Nat.sub_eq_zero_iff_le, Nat.sub_eq_zero_iff_le] at h
    rw [Nat.sub_eq_zero_of_le h.1, Nat.le_antisymm h.2 hb5] at e
    omega_using [e]
  · intro h
    subst h
    have e1 : L - i' = 0 := by omega_using [e, hb5, hb12]
    rw [e1]; omega_using [e]

/-- Window `j` of `K`: a byte more if fewer than 5 bits are left, then
`Y := Y³² T_v R⁻¹` for `v` the top 5 of the `b'` bits left;
`ZF` after the last. -/
theorem crtWin5_ok (M : Mont) (Sq : MontS) (S : CrtSel 32) {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    {Q : Prop} {x : Nat} {ep : Addr} {L : Nat} {eb : List Byte} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hL : eb.length = L) (hL' : L < 2 ^ 31)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot wx 8 + tabBytes wx 32 ≤ ofs P (ep + BitVec.ofNat 64 i))
    {K j : Nat} (hK : 5 * K = padBits L + 8 * L) (hj : j < K) {i b : Nat} (hib : padBits L + 8 * i = 5 * j + b)
    (hb : b < 8) (hiL : i ≤ L) (hI : W5At t₀ P wx minv X Xc Q x ep L eb i b t) :
    WP isa (seqs (Crt.expWin5 Sq.mm M.mm S.code)) t fun t' => t'.zf = some (decide (j + 1 = K)) ∧
      ∃ i' b', padBits L + 8 * i' = 5 * (j + 1) + b' ∧ b' < 8 ∧ i' ≤ L ∧
        W5At t₀ P wx minv X Xc Q x ep L eb i' b' t' := by
  rw [expWin5_eq]
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (fill_ok hL hrd hbytes hout hb hiL (fun h5 => by
    rcases Nat.lt_or_ge i L with h | h
    · exact h
    · omega_arith) hI) fun t₁ ⟨i', b', hb5, hb12, hrel, hiL', hI₁⟩ => ?_
  have hc := hI₁.ctx
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  -- Five squarings, whose results stay below `Sq.bd X R`.
  have hXR : X ≤ 2 ^ (64 * wx) := by rw [← hc.n]; exact Nat.le_of_lt (wv_lt _ _ _ _)
  refine WP.seq (WP.mono (crtSqS_ok Sq hc hw hw' hR (Nat.lt_of_lt_of_le hI₁.ylt (Sq.le hXR)) hI₁.y)
    fun t₂ ⟨hc₂, hY₂, hYv₂, hh₂, f₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (crtSqS_ok Sq hc₂ hw hw' hR hY₂ hYv₂) fun t₃ ⟨hc₃, hY₃, hYv₃, hh₃, f₃, k₃⟩ => ?_)
  refine WP.seq (WP.mono (crtSqS_ok Sq hc₃ hw hw' hR hY₃ hYv₃) fun t₄ ⟨hc₄, hY₄, hYv₄, hh₄, f₄, k₄⟩ => ?_)
  refine WP.seq (WP.mono (crtSqS_ok Sq hc₄ hw hw' hR hY₄ hYv₄) fun t₅ ⟨hc₅, hY₅, hYv₅, hh₅, f₅, k₅⟩ => ?_)
  refine WP.seq (WP.mono (crtSqS_ok Sq hc₅ hw hw' hR hY₅ hYv₅) fun t₆ ⟨hc₆, _, hYv₆, hh₆, f₆, k₆⟩ => ?_)
  have hh16 : ∀ k < 32, word t₆.mem P (8 * k) = word t₁.mem P (8 * k) := fun k hk =>
    (hh₆ k hk).trans ((hh₅ k hk).trans ((hh₄ k hk).trans ((hh₃ k hk).trans (hh₂ k hk))))
  have f16 : Frm P (crtWinRanges wx) t₁.mem t₆.mem := (((f₂.trans f₃).trans f₄).trans f₅).trans f₆
  have k16 : Keep mmRegs t₁ t₆ := ((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)
  have htab₆ : CTab t₆.mem P wx X Q x 32 := hI₁.tab.of_win f16 hn
  -- The window.
  have hr : pre eb i' % 2 ^ b' < 2 ^ b' := Nat.mod_lt _ (Nat.two_pow_pos b')
  refine wp_seqs_append (a := [.block Crt.takeWin]) (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.mono (takeWin_ok hc₆ (by rw [hh16 _ (by decide)]; exact hI₁.pow)
    (by rw [hh16 _ (by decide)]; exact hI₁.v) (by rw [hh16 _ (by decide)]; exact hI₁.bit) hb5 hb12 hr)
    fun t₇ ⟨hm₇, k₇⟩ => ?_
  have hY1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have hnT : slot wx 8 + tabBytes wx 32 ≤ 2 ^ 64 := by omega_arith
  have f₇ : Frm P (crtExpRanges5 wx) t₆.mem t₇.mem := by
    rw [hm₇]
    exact (((frm5_hdrW _ P wx _ (by simp [crtExpRanges5]) (by decide)).trans
      (frm5_hdrW _ P wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))).trans
      (frm5_hdrW _ P wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))).trans
      (frm5_hdrW _ P wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))
  have hc₇ := hc₆.of_frm5 f₇ k₇.2.2 (k₇.gpr (by decide))
  have htab₇ : CTab t₇.mem P wx X Q x 32 := by
    rw [hm₇]
    exact (((htab₆.hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide)
      (by decide) hnT).hdrW _ (by decide) (by decide) hnT
  have hY₇ : wv t₇.mem P (slot wx aY) wx = wv t₆.mem P (slot wx aY) wx := by
    rw [hm₇, wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith), wv_hdrW _ _ _ (by decide) (by omega_arith)
      (by omega_arith), wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith),
      wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith)]
  have hh₇ : ∀ k < 32, k ≠ Crt.sPow → k ≠ Crt.sBit → k ≠ Crt.sNib → k ≠ Crt.sV →
      word t₇.mem P (8 * k) = word t₁.mem P (8 * k) := fun k hk h1 h2 h3 h4 => by
    rw [hm₇, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h4), hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h3),
      hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h1), hh16 k hk]
  have hv32 : pre eb i' % 2 ^ b' / 2 ^ (b' - 5) < 32 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_add,
      show 5 + (b' - 5) = b' by omega_arith]
    exact hr
  -- `T := T_v`.
  refine wp_seqs_append S.ne (by simp) ?_
  have ht₇ : word t₇.mem P (8 * Crt.sTab) = off P (slot wx 8) := by
    rw [hh₇ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI₁.tab.tab
  refine WP.mono (S.ok hc₇ hw hw' hv32 ht₇
      (by rw [hm₇, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]))
    fun t₈ ⟨hc₈, hT₈, f₈, k₈⟩ => ?_
  have hY₈ : wv t₈.mem P (slot wx aY) wx = wv t₇.mem P (slot wx aY) wx :=
    f₈.wv_eq (fun r hr => by
      have := slot_sep (w := wx) (show aY ≠ Crt.aT by decide)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega_arith
      · simp only [Crt.sEnt, sFn]; have := hdr_lt_slot wx aY (show 31 < 32 by decide); omega_arith
      · simp only [Crt.sJ, sFn]; have := hdr_lt_slot wx aY (show 31 < 32 by decide); omega_arith) (by omega_arith)
  have htab₈ : CTab t₈.mem P wx X Q x 32 := htab₇.of_win (f₈.mono (selRanges_sub wx)) hn
  simp only [seqs]
  -- `Y := Y T`.
  have hv := take_val (P := pre eb i') hb5
  refine WP.seq (WP.mono (crtMulT_ok M (Q := Q) (x := x) (E := 32 * (pre eb i' / 2 ^ b'))
    (v := pre eb i' % 2 ^ b' / 2 ^ (b' - 5)) hc₈ hw hw' hR (by rw [hT₈]; exact htab₇.lt _ hv32)
    (fun hq => by rw [hY₈, hY₇, hYv₆ hq, show ∀ C : Nat, 2 * (2 * (2 * (2 * (2 * C)))) = 32 * C from fun C => by omega_arith])
    (fun hq => by rw [hT₈]; exact htab₇.val hq _ hv32)) fun t₉ ⟨hc₉, hY₉, hYv₉, hh₉, f₉, k₉⟩ => ?_)
  have hh₉' : ∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → word t₉.mem P (8 * k) = word t₇.mem P (8 * k) :=
    fun k hk h1 h2 => (hh₉ k hk).trans (sel_hdr f₈ hk h1 h2)
  -- The end.
  refine WP.mono (winEnd_ok (L := L) (i := i') (b := b' - 5) hc₉
    (by rw [hh₉' _ (by decide) (by decide) (by decide), hh₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hI₁.len)
    (by rw [hh₉' _ (by decide) (by decide) (by decide), hh₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hI₁.idx)
    (by rw [hh₉' _ (by decide) (by decide) (by decide), hm₇, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self])
    hiL' (by omega_arith) (by omega_arith)) fun t' ⟨hz, hm', k'⟩ => ⟨by rw [hz]; congr 1; exact decide_eq_decide.mpr (win5_last hK hib hrel hiL' hb5 hb12),
      i', b' - 5, by omega_arith, by omega_arith, hiL', ?_⟩
  have fall : Frm P (crtExpRanges5 wx) t₁.mem t'.mem := by
    rw [hm']
    exact ((f16.mono fun r hr => crtExpRanges_sub5 wx r (crtWinRanges_sub wx r hr)).trans f₇).trans
      ((f₈.mono fun r hr => crtExpRanges_sub5 wx r (crtWinRanges_sub wx r (selRanges_sub wx r hr))).trans
        (f₉.mono fun r hr => crtExpRanges_sub5 wx r (crtWinRanges_sub wx r hr)))
  have htab' : CTab t'.mem P wx X Q x 32 := by rw [hm']; exact htab₈.of_win f₉ hn
  have hY' : wv t'.mem P (slot wx aY) wx < X := by rw [hm']; exact hY₉
  refine ⟨hc₉.of_frm5 (by rw [hm']; exact Frm.refl _ _ _) k'.2.2 (k'.gpr (by decide)), htab', hY', fun hq => ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, hI₁.frm.trans fall,
    ((((((hI₁.keep.trans k16).trans k₇).trans k₈).trans k₉).trans k').mono (by decide))⟩
  · rw [hm', hYv₉ hq, hv.1]
  · rw [hm', hh₉' _ (by decide) (by decide) (by decide), hm₇, word_writeW_self, hv.2]
  · rw [hm', hh₉' _ (by decide) (by decide) (by decide), hm₇, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm', hh₉' _ (by decide) (by decide) (by decide), hm₇, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [hm', hh₉' _ (by decide) (by decide) (by decide), hh₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hI₁.idx
  · rw [hm', hh₉' _ (by decide) (by decide) (by decide), hh₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hI₁.e
  · rw [hm', hh₉' _ (by decide) (by decide) (by decide), hh₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hI₁.len

/-! ## The exponentiation -/

/-- What changes within `expLoop5`'s ranges keeps the prime's workspace. -/
theorem SubCtx.of_frm5 {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (h : SubCtx s B Z o w wx minv) (hT : o + slot wx 8 + wsTab wx ≤ Z) (hf : Frm (off B o) (crtExpRanges5 wx) s.mem t.mem)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) : SubCtx t B Z o w wx minv := by
  have hn := h.scr.nowrap
  simp only [wsTab] at hT
  have hL : o + (slot wx 8 + tabBytes wx 32) ≤ 2 ^ 64 := by omega_arith
  have hr := crtExpRanges5_ok wx
  have hr' : ∀ r ∈ crtExpRanges5 wx, r.1 + r.2 ≤ slot wx 8 + tabBytes wx 32 := fun r hr' => (hr r hr').2
  have hh : ∀ i < 17, word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi' =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega_arith))
      (by have : 8 * 32 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
          omega_arith)
  have hb : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    hf.word_below hr' hL (by unfold slot hdrBytes at hL; omega_arith) (by have := hdr_lt_slot w 8 hi'; have := h.lo; omega_arith)
  exact ⟨h.scr.congr hwr, hdi.trans h.rdi,
    ⟨(hh _ (by decide)).trans h.hdr.hw, (hh _ (by decide)).trans h.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega_arith)).trans (h.narr j hj), h.lo, h.hi⟩

/-- After `j` windows: `padBits L + 8 i = 5 j + b`. -/
def W5Inv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x : Nat)
    (ep : Addr) (L : Nat) (eb : List Byte) (j : Nat) (t : State) : Prop :=
  ∃ i b, padBits L + 8 * i = 5 * j + b ∧ b < 8 ∧ i ≤ L ∧ W5At t₀ P wx minv X Xc Q x ep L eb i b t

theorem expLoop5_eq (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sel : List (Prog isa)) (sp sl : Nat) :
    Crt.expLoop5S sq mul sel sp sl = ((expInit sp sl :: Crt.tabBuildN mul 30) ++
      ([.block Crt.padInit] : List (Prog isa))) ++ ([.loop (seqs (Crt.expWin5 sq mul sel)) .ne] : List (Prog isa)) := by
  simp [Crt.expLoop5S, expInit]

/-- `expLoop5`'s start, table and padding: the windows' invariant. -/
theorem crtExpHead5_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    {X x : Nat} {Q : Prop} (hc : SubCtx s B Z o w wx minv) (hT : o + slot wx 8 + wsTab wx ≤ Z) (hw2 : 2 ≤ wx)
    (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL2 : eb.length ≤ 1024) :
    WP isa (seqs ((expInit sp sl :: Crt.tabBuildN M.mm 30) ++ ([.block Crt.padInit] : List (Prog isa)))) s
      (W5Inv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) Q x ep eb.length eb 0) := by
  have hi := hc.hi
  have hlo := hc.lo
  have hBn := hc.scr.nowrap
  have hs32 := hc.scr32 hT
  have hPn := hs32.nowrap
  have hT' := hT
  simp only [wsTab] at hT'
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc₀ : CExpCtx s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) 32 :=
    ⟨hc.good, hs32, hn, hinv, rfl⟩
  refine wp_seqs_append (by simp) (by simp) ?_
  -- The start and the table.
  rw [← List.singleton_append]
  refine wp_seqs_append (by simp) (by simp [tabBuild_eq, tabPre]) ?_
  simp only [seqs, expInit]
  refine WP.mono (crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := writeW_outside s.mem (off B o) (d := 8 * Crt.sExp) ep (by decide)
  have o2 := writeW_outside (s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep) (off B o) (d := 8 * Crt.sExpLen)
    (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := writeW_outside ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).writeW
    (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (off B o) (d := 8 * Crt.sI)
    (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (off B o) (crtExpRanges wx 32) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [crtExpRanges])).trans (Frm.of_outside o2 (by simp [crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [crtExpRanges]))
  have hc₁ := hc₀.of_frm f₁ k₁.2.2 (k₁.gpr (by decide))
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hY1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have hYe₁ : wv t₁.mem (off B o) (slot wx aY) wx = wv s.mem (off B o) (slot wx aY) wx := by
    rw [o3.wv (by unfold Crt.sI sFn at *; omega_arith) (by omega_arith), o2.wv (by unfold Crt.sExpLen sFn at *; omega_arith)
      (by omega_arith), o1.wv (by unfold Crt.sExp sFn at *; omega_arith) (by omega_arith)]
  refine WP.mono (tabBuild_ok M (Q := Q) (x := x) hc₁ (by decide) (by decide) hw2 (by omega_arith) hR hxl hxc
    (by rw [hYe₁]; exact hyl) (fun hq => by rw [hYe₁]; exact hyc hq)) fun t₂ ⟨hc₂, htab₂, hYe₂, hh₂, f₂, k₂⟩ => ?_
  -- The padding.
  have hlen₂ : word t₂.mem (off B o) (8 * Crt.sExpLen) = BitVec.ofNat 64 eb.length := by
    rw [hh₂ _ (by decide) (by decide) (by decide) (by decide), hm₁,
      hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  refine WP.mono (padInit_ok hc₂ hlen₂ (by omega_arith)) fun t₃ ⟨hm₃, k₃⟩ => ?_
  have hnT : slot wx 8 + tabBytes wx 32 ≤ 2 ^ 64 := by omega_arith
  have f₃ : Frm (off B o) (crtExpRanges5 wx) t₂.mem t₃.mem := by
    rw [hm₃]
    exact ((frm5_hdrW _ _ wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide)).trans
      (frm5_hdrW _ _ wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))).trans
      (frm5_hdrW _ _ wx _ (by simp [crtExpRanges5]) (by decide))
  have f03 : Frm (off B o) (crtExpRanges5 wx) s.mem t₃.mem :=
    ((f₁.mono (crtExpRanges_sub5 wx)).trans (f₂.mono (crtExpRanges_sub5 wx))).trans f₃
  have hh₃ : ∀ k < 32, k ≠ Crt.sBit → k ≠ Crt.sV → k ≠ Crt.sPow → word t₃.mem (off B o) (8 * k) =
      word t₂.mem (off B o) (8 * k) := fun k hk h1 h2 h3 => by
    rw [hm₃, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h3), hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h2),
      hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h1)]
  have hY₃ : wv t₃.mem (off B o) (slot wx aY) wx = wv s.mem (off B o) (slot wx aY) wx := by
    rw [hm₃, wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith), wv_hdrW _ _ _ (by decide) (by omega_arith)
      (by omega_arith), wv_hdrW _ _ _ (by decide) (by omega_arith) (by omega_arith), hYe₂, hYe₁]
  have h0 : W5Inv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) Q x ep eb.length eb 0 t₃ := by
    refine ⟨0, padBits eb.length, by omega_arith, by have := padBits_lt eb.length; omega_arith, by omega_arith,
      hc₂.of_frm5 f₃ k₃.2.2 (k₃.gpr (by decide)), ?_, hY₃ ▸ hyl, fun hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_, f03,
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    · rw [hm₃]
      exact ((htab₂.hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide)
        (by decide) hnT
    · rw [hY₃, hyc hq, pre_zero, Nat.zero_div, Nat.pow_zero, Nat.one_mul]
    · rw [hm₃, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, pre_zero, Nat.zero_mod,
        Nat.zero_mul]; rfl
    · rw [hm₃, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm₃, word_writeW_self]
    · rw [hh₃ _ (by decide) (by decide) (by decide) (by decide), hh₂ _ (by decide) (by decide) (by decide) (by decide),
        hm₁, word_writeW_self]; rfl
    · rw [hh₃ _ (by decide) (by decide) (by decide) (by decide), hh₂ _ (by decide) (by decide) (by decide) (by decide),
        hm₁, hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr (i := Crt.sExpLen) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hh₃ _ (by decide) (by decide) (by decide) (by decide)]; exact hlen₂
  exact h0

/-- The exponentiation in a prime's workspace by windows of 5 bits, with room
for its table of 32 entries: as `crtExpLoop_ok`. -/
theorem crtExpLoop5S_ok (M : Mont) (Sq : MontS) (S : CrtSel 32) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    {X x : Nat} {Q : Prop} (hc : SubCtx s B Z o w wx minv) (hT : o + slot wx 8 + wsTab wx ≤ Z) (hw2 : 2 ≤ wx)
    (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (Crt.expLoop5S Sq.mm M.mm S.code sp sl)) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
      (Q → wv t.mem (off B o) (slot wx aY) wx % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
      Frm (off B o) (crtExpRanges5 wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hi := hc.hi
  have hlo := hc.lo
  have hBn := hc.scr.nowrap
  have hs32 := hc.scr32 hT
  have hPn := hs32.nowrap
  have hT' := hT
  simp only [wsTab] at hT'
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hout : ∀ i < eb.length, slot wx 8 + tabBytes wx 32 ≤ ofs (off B o) (ep + BitVec.ofNat 64 i) := fun i hi' => by
    have := he.out i hi'
    rcases ofs_rebase B (ep + BitVec.ofNat 64 i) (o := o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega_arith
    · omega_arith
  rw [expLoop5_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (crtExpHead5_ok M hc hT hw2 hwx hw30 hn hinv hodd hxl hxc hyl
    hyc hsp hsl hep hel hL2) fun t₃ h0 => ?_)
  simp only [seqs]
  -- The windows.
  have hK := win5_dvd eb.length
  refine wp_upto (a := 0) (N := (padBits eb.length + 8 * eb.length) / 5) (by omega_arith)
    (W5Inv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) Q x ep eb.length eb)
    (fun j _ hj t ⟨i, b, hib, hb, hiL, hI⟩ => crtWin5_ok M Sq S hw2 (by omega_arith) hR rfl (by omega_arith) he.rd he.val
      hout (by omega_arith) hj hib hb hiL hI)
    (fun t ⟨i, b, hib, hb, hiL, hI⟩ => ?_) h0
  have hb0 : b = 0 := by omega_arith
  have hiL' : i = eb.length := by omega_arith
  subst hb0 hiL'
  exact ⟨hc.of_frm5 hT hI.frm hI.keep.2.2 (hI.keep.gpr (by decide)), hI.ylt,
    fun hq => by rw [hI.y hq, Nat.pow_zero, Nat.div_one, pre_len], hI.frm, hI.keep⟩

/-- `crtExpLoop5S_ok` with the squarings by `M`: `Crt.expLoop5`. -/
theorem crtExpLoop5_ok (M : Mont) (S : CrtSel 32) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    {X x : Nat} {Q : Prop} (hc : SubCtx s B Z o w wx minv) (hT : o + slot wx 8 + wsTab wx ≤ Z) (hw2 : 2 ≤ wx)
    (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (Crt.expLoop5 M.mm S.code sp sl)) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
      (Q → wv t.mem (off B o) (slot wx aY) wx % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
      Frm (off B o) (crtExpRanges5 wx) s.mem t.mem ∧ Keep mmRegs s t :=
  crtExpLoop5S_ok M M.toS S hc hT hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc hsp hsl hep hel hL1 hL2 he

end VG.Proof.Bignum.X86_64
