module

public import VerifiedGarbage.Impl.AesXts.RISCV64Unit
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.AesXts.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Spec.Xts
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
public import VerifiedGarbage.Impl.AesXts.RISCV64
import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.AesXts.Unit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Impl.AesXts.RISCV64Unit
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Spec.Xts
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Xts.Contract
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.Align
meta import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Impl.AesXts.RISCV64
meta import VerifiedGarbage.Proof.AesXts.Alpha
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad

/-! ### `AesXts.RISCV64.Unit.CT`, which only this module used -/

section

/-! ### `AesXts.RISCV64.Unit.Dec`, which this module and modules that import it used -/

section

/-! ### `AesXts.RISCV64.Unit.Enc`, which this module and modules that import it used -/

section

/-! ### `AesXts.RISCV64.Unit.Steps`, which this module and modules that import it used -/

section

/-! ### `AesXts.RISCV64.Steps`, which this module and modules that import it used -/

section

/-!
# XTS-AES on RISC-V: multiplication by `α`

`mulA` run once, in continuation-passing style, as on ARMv7: the tweak's
four 32-bit words loaded a byte at a time (zero-extended), each shifted left
by one bit with the top bit of the word before it shifted in, the first
XORed with `0x87` if the last word's top bit was set, and the low 32 bits of
each stored a byte at a time (`mulWord_wp`): the words of
`mulAlpha_words32` (`Proof/AesXts/Alpha.lean`), once the 64-bit operations
are cut to 32 bits (`shl_cut`, `ushr31`, `mask_87`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.ByteLoad VG.Impl.Words.RISCV64 VG.Impl.AesXts.RISCV64
open VG.Spec.Aes (bytesAt)

theorem wp_and {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

/-! ## 32-bit words in 64-bit registers -/

/-- A zero-extended word shifted left by one bit, cut to 32 bits. -/
theorem shl_cut (w : BitVec 32) : ((w.setWidth 64) <<< 1).setWidth 32 = w <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  have hw := w.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := w.toNat) (by omega_using []), Nat.mod_mod_of_dvd _ (by decide)]

/-- The top bit of a zero-extended word, as a bit. -/
theorem ushr31 (w : BitVec 32) : (w.setWidth 64) >>> 31 = if w.msb then (1 : BitVec 64) else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, BitVec.msb_eq_decide]
  have := w.isLt
  rw [Nat.mod_eq_of_lt (by omega_using [])]
  by_cases h : 2 ^ 31 ≤ w.toNat
  · rw [decide_eq_true h]; show _ = 1; omega_using [h]
  · rw [decide_eq_false h]; show _ = 0; omega_using [h]

theorem mask_87 (b : Bool) :
    (BitVec.ofNat 64 0 - (if b then (1 : BitVec 64) else 0)) &&& BitVec.ofNat 64 0x87 =
      if b then (0x87 : BitVec 64) else 0 := by
  cases b <;> decide

theorem ite_cut (b : Bool) (x : Nat) :
    (if b then (BitVec.ofNat 64 x) else 0).setWidth 32 = if b then BitVec.ofNat 32 x else 0 := by
  cases b
  · rfl
  · simp

/-- Word `j` of the tweak times `α`: `w` shifted left with `p`'s top bit
shifted in. -/
theorem word_val (w p : BitVec 32) :
    (((w.setWidth 64) <<< 1) ||| ((p.setWidth 64) >>> 31)).setWidth 32 =
      (w <<< 1) ||| (if p.msb then (1 : BitVec 32) else 0) := by
  rw [BitVec.setWidth_or, shl_cut, ushr31, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ite_cut]
  rfl

/-- Word 0 of the tweak times `α`: `w` shifted left, XORed with `0x87` if
`l`'s top bit is set. -/
theorem word0_val (w l : BitVec 32) :
    (((w.setWidth 64) <<< 1) ^^^ ((BitVec.ofNat 64 0 - (l.setWidth 64) >>> 31) &&& BitVec.ofNat 64 0x87)).setWidth 32 =
      (w <<< 1) ^^^ (if l.msb then (0x87 : BitVec 32) else 0) := by
  rw [BitVec.setWidth_xor, shl_cut, ushr31, mask_87, show (0x87 : BitVec 64) = BitVec.ofNat 64 0x87 from rfl,
    ite_cut]
  rfl

/-! ## The words loaded and stored -/

/-- `d :=` the word at `off(n)`, a byte at a time through `t2`. -/
theorem loadW_wp {s : State} {d n : Reg} {off : Nat} {rest : List Instr} {Φ : State → Prop}
    (hdn : d ≠ n) (htn : Reg.t2 ≠ n) (hdt : d ≠ .t2) (ho : off + 3 < 2048)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 4)
    (k : ∀ s', s'.gpr d = (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 32).setWidth 64 →
      (∀ r, r ≠ d → r ≠ .t2 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Φ) :
    WP isa (.block (loadLE32 d .t2 n off ++ rest)) s Φ := by
  rw [WP.block_append_iff]
  refine WP.mono (loadLE32_ok hdn htn hdt ho h) fun s' e => ?_
  subst e
  refine k _ (RegUpd.gpr_write_self _ _ _) (fun r h1 h2 => ?_) ?_ ?_ ?_ ?_
  · rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  · rw [RegUpd.mem_write, RegUpd.mem_write]
  · rw [RegUpd.rd_write, RegUpd.rd_write]
  · rw [RegUpd.wr_write, RegUpd.wr_write]
  · rw [RegUpd.sp_write, RegUpd.sp_write]

/-- The low 32 bits of `a6` stored at `off(s3)`, a byte at a time through `t2`. -/
theorem storeW_wp {s : State} {off : Nat} {rest : List Instr} {Φ : State → Prop} (ho : off + 3 < 2048)
    (h : InRegions s.wr (s.gpr .s3 + BitVec.ofNat 64 off) 4)
    (k : ∀ s', (∀ r, r ≠ .t2 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW (s.gpr .s3 + BitVec.ofNat 64 off) ((s.gpr .a6).setWidth 32) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Φ) :
    WP isa (.block (storeLE32 .a6 .t2 .s3 off ++ rest)) s Φ := by
  rw [WP.block_append_iff]
  refine WP.mono (storeLE32_ok (by decide) (by decide) ho h) fun s' e => ?_
  subst e
  refine k _ (fun r h1 => ?_) ?_ ?_ ?_ ?_
  · rw [RegUpd.gpr_write_of_ne _ _ h1]
  · rw [RegUpd.mem_write]
  · rw [RegUpd.rd_write]
  · rw [RegUpd.wr_write]
  · rw [RegUpd.sp_write]

/-- `mulWord w p off`: the word in `w` shifted left with the top bit of the
word in `p` shifted in, stored at `off(s3)`. -/
theorem mulWord_wp {s : State} {w p : Reg} {off : Nat} {x y : BitVec 32} {Q : Addr} {rest : List Instr}
    {Φ : State → Prop} (hp6 : p ≠ .a6) (ho : off + 3 < 2048)
    (h3 : s.gpr .s3 = Q) (hx : s.gpr w = x.setWidth 64) (hy : s.gpr p = y.setWidth 64)
    (wq : InRegions s.wr (Q + BitVec.ofNat 64 off) 4)
    (k : ∀ s', (∀ r, r ≠ .a6 → r ≠ .t6 → r ≠ .t2 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW (Q + BitVec.ofNat 64 off) ((x <<< 1) ||| (if y.msb then (1 : BitVec 32) else 0)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Φ) :
    WP isa (.block (mulWord w p off ++ rest)) s Φ := by
  unfold mulWord
  rw [List.append_assoc, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_sll (by decide) fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ => wp_or fun s₃ u₃ => ?_
  obtain v₃ : s₃.gpr .a6 = ((x.setWidth 64) <<< 1) ||| ((y.setWidth 64) >>> 31) := by
    rw [u₃.gpr, u₂.other .a6 (by decide), u₁.gpr, u₂.gpr, u₁.other _ hp6, hx, hy]
  have g₃ (r : Reg) (h6 : r ≠ .a6) (ht : r ≠ .t6) : s₃.gpr r = s.gpr r := by
    rw [u₃.other _ h6, u₂.other _ ht, u₁.other _ h6]
  refine storeW_wp ho (by rw [g₃ _ (by decide) (by decide), h3, u₃.wr, u₂.wr, u₁.wr]; exact wq)
    fun s₄ g₄ m₄ rd₄ wr₄ sp₄ => k s₄ (fun r h6 ht h2 => by rw [g₄ r h2, g₃ r h6 ht]) ?_
      (by rw [rd₄, u₃.rd, u₂.rd, u₁.rd]) (by rw [wr₄, u₃.wr, u₂.wr, u₁.wr])
      (by rw [sp₄, u₃.sp, u₂.sp, u₁.sp])
  rw [m₄, g₃ _ (by decide) (by decide), h3, v₃, word_val, u₃.mem, u₂.mem, u₁.mem]

/-- The registers `mulA` writes. -/
abbrev mulRegs : List Reg := [.t1, .t2, .t3, .t4, .t5, .t6, .a6]

/-- The tweak at `Q` (in `s3`) times `α`. -/
theorem mulA_wp {s : State} {Q : Addr} {rest : List Instr} {Φ : State → Prop} (h3 : s.gpr .s3 = Q)
    (inR : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) 4)
    (inW : ∀ d, d + 4 ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) 4)
    (k : ∀ s', (∀ r, r ∉ mulRegs → s'.gpr r = s.gpr r) →
      bytesAt s'.mem Q 16 = Spec.Xts.mulAlpha (bytesAt s.mem Q 16) → Frame [⟨Q, 16⟩] s.mem s'.mem →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Φ) :
    WP isa (.block (mulA ++ rest)) s Φ := by
  generalize hw : (fun d : Nat => s.mem.readW (Q + BitVec.ofNat 64 d) 32) = w
  have hwd (d : Nat) : s.mem.readW (Q + BitVec.ofNat 64 d) 32 = w d := by rw [← hw]
  unfold mulA
  simp only [List.append_assoc]
  refine loadW_wp (by decide) (by decide) (by decide) (by decide) (by rw [h3]; exact inR 0 (by decide))
    fun s₁ v₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_
  obtain q₁ : s₁.gpr .s3 = Q := by rw [g₁ _ (by decide) (by decide), h3]
  refine loadW_wp (by decide) (by decide) (by decide) (by decide)
    (by rw [q₁, rd₁, wr₁]; exact inR 4 (by decide)) fun s₂ v₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  obtain q₂ : s₂.gpr .s3 = Q := by rw [g₂ _ (by decide) (by decide), q₁]
  refine loadW_wp (by decide) (by decide) (by decide) (by decide)
    (by rw [q₂, rd₂, wr₂, rd₁, wr₁]; exact inR 8 (by decide)) fun s₃ v₃ g₃ m₃ rd₃ wr₃ sp₃ => ?_
  obtain q₃ : s₃.gpr .s3 = Q := by rw [g₃ _ (by decide) (by decide), q₂]
  refine loadW_wp (by decide) (by decide) (by decide) (by decide)
    (by rw [q₃, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact inR 12 (by decide)) fun s₄ v₄ g₄ m₄ rd₄ wr₄ sp₄ => ?_
  -- The words, zero-extended.
  obtain e1 : s₄.gpr .t1 = (w 0).setWidth 64 := by
    rw [g₄ _ (by decide) (by decide), g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), v₁, h3, hwd]
  obtain e3 : s₄.gpr .t3 = (w 4).setWidth 64 := by
    rw [g₄ _ (by decide) (by decide), g₃ _ (by decide) (by decide), v₂, q₁, m₁, hwd]
  obtain e4 : s₄.gpr .t4 = (w 8).setWidth 64 := by
    rw [g₄ _ (by decide) (by decide), v₃, q₂, m₂, m₁, hwd]
  obtain e5 : s₄.gpr .t5 = (w 12).setWidth 64 := by rw [v₄, q₃, m₃, m₂, m₁, hwd]
  obtain q₄ : s₄.gpr .s3 = Q := by rw [g₄ _ (by decide) (by decide), q₃]
  obtain m₄' : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  have g₄' (r : Reg) (hr : r ∉ mulRegs) : s₄.gpr r = s.gpr r := by
    simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3', h4', h5, -, -⟩ := hr
    rw [g₄ r h5 h2, g₃ r h4' h2, g₂ r h3' h2, g₁ r h1 h2]
  -- Word 0, with the mask.
  simp only [List.cons_append, List.nil_append]
  refine wp_srl (by decide) fun s₅ u₅ => wp_li (imm := 0) (by decide) fun s₆ u₆ => wp_sub fun s₇ u₇ => ?_
  refine wp_li (imm := 0x87) (by decide) fun s₈ u₈ => wp_and fun s₉ u₉ => ?_
  refine wp_sll (by decide) fun s₁₀ u₁₀ => wp_xor fun s₁₁ u₁₁ => ?_
  obtain v₁₁ : s₁₁.gpr .a6 = ((w 0).setWidth 64 <<< 1) ^^^
      ((BitVec.ofNat 64 0 - (w 12).setWidth 64 >>> 31) &&& BitVec.ofNat 64 0x87) := by
    rw [u₁₁.gpr, u₁₀.gpr, u₁₀.other .t6 (by decide), u₉.gpr, u₉.other .t1 (by decide), u₈.gpr,
      u₈.other .t6 (by decide), u₈.other .t1 (by decide), u₇.gpr, u₇.other .t1 (by decide), u₆.gpr,
      u₆.other .t6 (by decide), u₆.other .t1 (by decide), u₅.gpr, u₅.other .t1 (by decide), e1, e5]
  have g₁₁ (r : Reg) (h6 : r ≠ .t6) (h2 : r ≠ .t2) (ha : r ≠ .a6) : s₁₁.gpr r = s₄.gpr r := by
    rw [u₁₁.other _ ha, u₁₀.other _ ha, u₉.other _ h6, u₈.other _ h2, u₇.other _ h6, u₆.other _ h2,
      u₅.other _ h6]
  obtain m₁₁ : s₁₁.mem = s.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄']
  obtain wr₁₁ : s₁₁.wr = s.wr := by
    rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄']
  refine storeW_wp (off := 0) (by decide)
    (by rw [g₁₁ _ (by decide) (by decide) (by decide), q₄, wr₁₁]; exact inW 0 (by decide))
    fun s₁₂ g₁₂ m₁₂ rd₁₂ wr₁₂ sp₁₂ => ?_
  have k₁₂ (r : Reg) (h6 : r ≠ .t6) (h2 : r ≠ .t2) (ha : r ≠ .a6) : s₁₂.gpr r = s₄.gpr r := by
    rw [g₁₂ r h2, g₁₁ r h6 h2 ha]
  -- Words 1 to 3.
  refine mulWord_wp (x := w 4) (y := w 0) (Q := Q) (by decide) (by decide)
    (by rw [k₁₂ _ (by decide) (by decide) (by decide), q₄]) (by rw [k₁₂ _ (by decide) (by decide) (by decide), e3])
    (by rw [k₁₂ _ (by decide) (by decide) (by decide), e1])
    (by rw [wr₁₂, wr₁₁]; exact inW 4 (by decide)) fun s₁₃ g₁₃ m₁₃ rd₁₃ wr₁₃ sp₁₃ => ?_
  have k₁₃ (r : Reg) (h6 : r ≠ .t6) (h2 : r ≠ .t2) (ha : r ≠ .a6) : s₁₃.gpr r = s₄.gpr r := by
    rw [g₁₃ r ha h6 h2, k₁₂ r h6 h2 ha]
  refine mulWord_wp (x := w 8) (y := w 4) (Q := Q) (by decide) (by decide)
    (by rw [k₁₃ _ (by decide) (by decide) (by decide), q₄]) (by rw [k₁₃ _ (by decide) (by decide) (by decide), e4])
    (by rw [k₁₃ _ (by decide) (by decide) (by decide), e3])
    (by rw [wr₁₃, wr₁₂, wr₁₁]; exact inW 8 (by decide)) fun s₁₄ g₁₄ m₁₄ rd₁₄ wr₁₄ sp₁₄ => ?_
  have k₁₄ (r : Reg) (h6 : r ≠ .t6) (h2 : r ≠ .t2) (ha : r ≠ .a6) : s₁₄.gpr r = s₄.gpr r := by
    rw [g₁₄ r ha h6 h2, k₁₃ r h6 h2 ha]
  refine mulWord_wp (x := w 12) (y := w 8) (Q := Q) (by decide) (by decide)
    (by rw [k₁₄ _ (by decide) (by decide) (by decide), q₄]) (by rw [k₁₄ _ (by decide) (by decide) (by decide), e5])
    (by rw [k₁₄ _ (by decide) (by decide) (by decide), e4])
    (by rw [wr₁₄, wr₁₃, wr₁₂, wr₁₁]; exact inW 12 (by decide)) fun s₁₅ g₁₅ m₁₅ rd₁₅ wr₁₅ sp₁₅ => ?_
  obtain mem₁₅ : s₁₅.mem = (((s.mem.writeW Q ((w 0 <<< 1) ^^^ (if (w 12).msb then (0x87 : BitVec 32) else 0))).writeW
      (Q + BitVec.ofNat 64 4) ((w 4 <<< 1) ||| (if (w 0).msb then (1 : BitVec 32) else 0))).writeW
      (Q + BitVec.ofNat 64 8) ((w 8 <<< 1) ||| (if (w 4).msb then (1 : BitVec 32) else 0))).writeW
      (Q + BitVec.ofNat 64 12) ((w 12 <<< 1) ||| (if (w 8).msb then (1 : BitVec 32) else 0)) := by
    rw [m₁₅, m₁₄, m₁₃, m₁₂, m₁₁, g₁₁ _ (by decide) (by decide) (by decide), q₄, v₁₁, word0_val,
      AesCbc.RISCV64.ofNat_zero_add]
  refine k s₁₅ (fun r hr => ?_) ?_ ?_ ?_ ?_ ?_
  · have hr' := hr
    simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain ⟨-, h2, -, -, -, h6, ha⟩ := hr'
    rw [g₁₅ r ha h6 h2, k₁₄ r h6 h2 ha, g₄' r hr]
  · rw [mem₁₅, ← hw]
    exact AesXts.mulAlpha_words32 s.mem Q
  · rw [mem₁₅]
    refine ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
      (Offset.contains_base Q (d := 4) (n := 4) (k := 16) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 8) (n := 4) (k := 16) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 12) (n := 4) (k := 16) (by decide) (by decide))
    simpa using Offset.contains_base Q (d := 0) (n := 4) (k := 16) (by decide) (by decide)
  · rw [rd₁₅, rd₁₄, rd₁₃, rd₁₂, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄, rd₃, rd₂, rd₁]
  · rw [wr₁₅, wr₁₄, wr₁₃, wr₁₂, wr₁₁]
  · rw [sp₁₅, sp₁₄, sp₁₃, sp₁₂, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, sp₄, sp₃, sp₂, sp₁]

end VG.Proof.AesXts.RISCV64

end

end

/-!
# XTS-AES of data units on RISC-V: the code between the calls

Each straight-line piece of `encrypt` and `decrypt`, run once, with the
registers and memory it leaves, and the swap loop (`swap_wp`), which leaves
`swapMem` (`Proof/AesXts/Unit.lean`), as on PPC64LE
(`Proof/AesXts/PPC64LE/Unit/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesXts.RISCV64Unit
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Proof.AesXts.Unit (swapMem swapMem_step swapMem_lo swapMem_hi)
open VG.Spec.Aes (bytesAt)

/-- A callee-saved register is none of those that are not. -/
theorem pres_ne {r x : Reg} (hr : r ∈ preserved) (hx : x ∉ preserved) : r ≠ x :=
  fun e => hx (e ▸ hr)

theorem shr4 (x : BitVec 64) : x >>> 4 = BitVec.ofNat 64 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])]

theorem shr4_shl4 (x : BitVec 64) : (x >>> 4) <<< 4 = BitVec.ofNat 64 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  simp only [Nat.reducePow]
  omega_using []

theorem byte_rt (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega_using []

/-! ## Registers only -/

theorem setup_wp (s : State) :
    WP isa (.block setup) s fun s' =>
      s'.gpr .s1 = s.gpr .a0 ∧ s'.gpr .s2 = s.gpr .a2 ∧ s'.gpr .s4 = s.gpr .a4 ∧
      s'.gpr .s5 = s.gpr .a5 ∧ s'.gpr .s6 = s.gpr .a6 ∧
      (∀ r, r ≠ .s1 → r ≠ .s2 → r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold setup mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₅.other _ h₅, u₄.other _ h₄, u₃.other _ h₃, u₂.other _ h₂, u₁.other _ h₁]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

theorem tArgs_wp (s : State) :
    WP isa (.block tArgs) s fun s' =>
      s'.gpr .a0 = s.gpr .a1 ∧ s'.gpr .a1 = s.gpr .s2 ∧
      s'.gpr .a2 = s.gpr .s6 + BitVec.ofNat 64 zO ∧ s'.gpr .a3 = s.gpr .s6 + BitVec.ofNat 64 tO ∧
      s'.gpr .a4 = BitVec.ofNat 64 1 ∧ s'.gpr .a5 = s.gpr .s6 + BitVec.ofNat 64 wO ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold tArgs mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (imm := zO) (by decide) fun s₃ u₃ =>
    wp_addi (imm := tO) (by decide) fun s₄ u₄ => wp_li (imm := 1) (by decide) fun s₅ u₅ =>
    wp_addi (imm := wO) (by decide) fun s₆ u₆ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (pres_ne hr (by decide)), u₅.other _ (pres_ne hr (by decide)),
      u₄.other _ (pres_ne hr (by decide)), u₃.other _ (pres_ne hr (by decide)),
      u₂.other _ (pres_ne hr (by decide)), u₁.other _ (pres_ne hr (by decide))]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

theorem argsAll_wp' (s : State) :
    WP isa (.block argsAll) s fun s' =>
      s'.gpr .a0 = s.gpr .s1 ∧ s'.gpr .a1 = s.gpr .s2 ∧
      s'.gpr .a2 = s.gpr .s6 + BitVec.ofNat 64 tO ∧ s'.gpr .a3 = s.gpr .s4 ∧
      s'.gpr .a4 = BitVec.ofNat 64 ((s.gpr .s5).toNat / 16) ∧ s'.gpr .a5 = s.gpr .s6 + BitVec.ofNat 64 wO ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold argsAll mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (imm := tO) (by decide) fun s₃ u₃ =>
    wp_mv fun s₄ u₄ => wp_srl (by decide) fun s₅ u₅ => wp_addi (imm := wO) (by decide) fun s₆ u₆ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), shr4]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (pres_ne hr (by decide)), u₅.other _ (pres_ne hr (by decide)),
      u₄.other _ (pres_ne hr (by decide)), u₃.other _ (pres_ne hr (by decide)),
      u₂.other _ (pres_ne hr (by decide)), u₁.other _ (pres_ne hr (by decide))]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

theorem argsHead_wp' (s : State) (hm : 1 ≤ (s.gpr .s5).toNat / 16) :
    WP isa (.block argsHead) s fun s' =>
      s'.gpr .a0 = s.gpr .s1 ∧ s'.gpr .a1 = s.gpr .s2 ∧
      s'.gpr .a2 = s.gpr .s6 + BitVec.ofNat 64 tO ∧ s'.gpr .a3 = s.gpr .s4 ∧
      s'.gpr .a4 = BitVec.ofNat 64 ((s.gpr .s5).toNat / 16 - 1) ∧ s'.gpr .a5 = s.gpr .s6 + BitVec.ofNat 64 wO ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [argsHead, WP.block_append_iff]
  refine WP.mono (argsAll_wp' s) fun s₁ ⟨a0, a1, a2, a3, a4, a5, cs, mem, rd, wr, sp⟩ =>
    wp_subi (imm := 1) (by decide) fun s₂ u₂ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.other _ (by decide), a0]
  · rw [u₂.other _ (by decide), a1]
  · rw [u₂.other _ (by decide), a2]
  · rw [u₂.other _ (by decide), a3]
  · rw [u₂.gpr, a4]; exact Offset.ofNat_sub_ofNat hm
  · rw [u₂.other _ (by decide), a5]
  · rw [u₂.other _ (pres_ne hr (by decide)), cs r hr]
  · rw [u₂.mem, mem]
  · rw [u₂.rd, rd]
  · rw [u₂.wr, wr]
  · rw [u₂.sp, sp]

theorem split_wp' (s : State) :
    WP isa (.block split) s fun s' =>
      s'.gpr .t1 = BitVec.ofNat 64 (16 * ((s.gpr .s5).toNat / 16)) ∧
      s'.gpr .t2 = BitVec.ofNat 64 ((s.gpr .s5).toNat % 16) ∧
      (∀ r, r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e : s.gpr .s5 - BitVec.ofNat 64 (16 * ((s.gpr .s5).toNat / 16)) =
      BitVec.ofNat 64 ((s.gpr .s5).toNat % 16) := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .s5).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * _) (by omega_using []),
      Nat.mod_eq_of_lt (a := _ % 16) (by omega_using [])]
    omega_using []
  unfold split
  refine wp_srl (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_sub fun s₃ u₃ =>
    WP.block_nil ⟨?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, shr4_shl4]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₂.gpr, u₁.gpr, shr4_shl4, e]
  · rw [u₃.other _ h₂, u₂.other _ h₁, u₁.other _ h₁]
  · rw [u₃.mem, u₂.mem, u₁.mem]
  · rw [u₃.rd, u₂.rd, u₁.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr]
  · rw [u₃.sp, u₂.sp, u₁.sp]

theorem lastAddr_wp' (s : State) :
    WP isa (.block lastAddr) s fun s' => s'.gpr .t3 = s.gpr .s4 + s.gpr .t1 - BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .t3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold lastAddr
  refine wp_add fun s₁ u₁ => wp_subi (imm := 16) (by decide) fun s₂ u₂ =>
    WP.block_nil ⟨?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.gpr]
  · rw [u₂.other _ h, u₁.other _ h]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [u₂.sp, u₁.sp]

/-- The last whole block, from the bytes of the whole blocks. -/
theorem last_eq (p : Addr) {m : Nat} (hm : 1 ≤ m) :
    p + BitVec.ofNat 64 (16 * m) - BitVec.ofNat 64 16 = p + BitVec.ofNat 64 (16 * (m - 1)) := by
  rw [show 16 * m = 16 * (m - 1) + 16 by omega_using [hm], ← Offset.add_add]
  exact BitVec.add_sub_cancel _ _

theorem argsL_wp' (s : State) {o : Nat} (ho : o < 2048) :
    WP isa (.block (argsL o)) s fun s' =>
      s'.gpr .a0 = s.gpr .s1 ∧ s'.gpr .a1 = s.gpr .s2 ∧
      s'.gpr .a2 = s.gpr .s6 + BitVec.ofNat 64 o ∧ s'.gpr .a3 = s.gpr .s4 + s.gpr .t1 - BitVec.ofNat 64 16 ∧
      s'.gpr .a4 = BitVec.ofNat 64 1 ∧ s'.gpr .a5 = s.gpr .s6 + BitVec.ofNat 64 wO ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold argsL mov
  refine wp_add fun s₁ u₁ => wp_subi (imm := 16) (by decide) fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    wp_mv fun s₄ u₄ => wp_addi ho fun s₅ u₅ => wp_li (imm := 1) (by decide) fun s₆ u₆ =>
    wp_addi (imm := wO) (by decide) fun s₇ u₇ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.gpr]
  · rw [u₇.other _ (by decide), u₆.gpr]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (pres_ne hr (by decide)), u₆.other _ (pres_ne hr (by decide)),
      u₅.other _ (pres_ne hr (by decide)), u₄.other _ (pres_ne hr (by decide)),
      u₃.other _ (pres_ne hr (by decide)), u₂.other _ (pres_ne hr (by decide)),
      u₁.other _ (pres_ne hr (by decide))]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-! ## Memory -/

theorem zeroZ_wp (s : State) {Z : Addr} (hz : s.gpr .s6 + BitVec.ofNat 64 zO = Z)
    (hw : ∀ i < 16, InRegions s.wr (Z + BitVec.ofNat 64 i) 1) :
    WP isa (.block zeroZ) s fun s' => (∀ r, r ≠ .t1 → s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem Z 16 = List.replicate 16 0 ∧ Frame [⟨Z, 16⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have ez (i : Nat) : s.gpr .s6 + BitVec.ofNat 64 (zO + i) = Z + BitVec.ofNat 64 i := by
    rw [← hz, Offset.add_add]
  refine WP.mono (Bytes.storeBytes_ok (tmp := .t1) (dst := .s6) (doff := zO) (bs := List.replicate 16 0)
    (by decide) (by decide) (by decide) fun i hi => by rw [ez]; exact hw i (by simpa using hi))
    fun s' h => ⟨h.gpr, ?_, ?_, h.rd, h.wr, h.sp⟩
  · apply List.ext_getElem (by simp [bytesAt])
    intro j h₁ _
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have := h.stored j (by simpa using h₁)
    rw [ez] at this
    simp only [bytesAt, List.getElem_map, List.getElem_range, this, List.getElem_replicate,
      List.getD_eq_getElem?_getD, List.getElem?_replicate, h₁, ite_true, Option.getD_some]
    rfl
  · have := h.frame
    rwa [hz, List.length_replicate] at this

/-! ## The swap -/

theorem swapStep_wp (s : State) {L : Addr} {k b : Nat} (hx : s.gpr .t3 = L + BitVec.ofNat 64 k)
    (hc : s.gpr .t2 = BitVec.ofNat 64 b) (hb : 1 ≤ b)
    (w₀ : InRegions s.wr (L + BitVec.ofNat 64 k) 1) (w₁ : InRegions s.wr (L + BitVec.ofNat 64 (16 + k)) 1) :
    WP isa (.block swapBody) s fun s' =>
      s'.mem = (s.mem.writeW (L + BitVec.ofNat 64 k) (s.mem (L + BitVec.ofNat 64 (16 + k)))).writeW
        (L + BitVec.ofNat 64 (16 + k)) (s.mem (L + BitVec.ofNat 64 k)) ∧
      s'.gpr .t3 = L + BitVec.ofNat 64 (k + 1) ∧ s'.gpr .t2 = BitVec.ofNat 64 (b - 1) ∧
      (∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have r₀ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 k) 1 :=
    let ⟨r, hr, c⟩ := w₀; ⟨r, List.mem_append_right _ hr, c⟩
  have r₁ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 (16 + k)) 1 :=
    let ⟨r, hr, c⟩ := w₁; ⟨r, List.mem_append_right _ hr, c⟩
  have e16 : L + BitVec.ofNat 64 k + BitVec.ofNat 64 16 = L + BitVec.ofNat 64 (16 + k) := by
    rw [Offset.add_add, Nat.add_comm]
  unfold swapBody
  refine wp_lbu (a := L + BitVec.ofNat 64 k) (by decide) (by rw [hx]; simp) r₀ fun s₁ u₁ => ?_
  refine wp_lbu (a := L + BitVec.ofNat 64 (16 + k)) (by decide) (by rw [u₁.other _ (by decide), hx, e16])
    (by rw [u₁.rd, u₁.wr]; exact r₁) fun s₂ u₂ => ?_
  refine wp_sb (a := L + BitVec.ofNat 64 k) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hx]; simp)
    (by rw [u₂.wr, u₁.wr]; exact w₀) fun s₃ u₃ => ?_
  refine wp_sb (a := L + BitVec.ofNat 64 (16 + k)) (by decide)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx, e16])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact w₁) fun s₄ u₄ => ?_
  refine wp_addi (imm := 1) (by decide) fun s₅ u₅ => wp_subi (imm := 1) (by decide) fun s₆ u₆ =>
    WP.block_nil ⟨?_, ?_, ?_, fun r h₂ h₃ h₄ h₅ => ?_, ?_, ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.other _ (by decide : Reg.t4 ≠ .t5), u₂.mem,
      u₁.gpr, u₁.mem, byte_rt, byte_rt]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx,
      Offset.add_add]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hc]
    exact Offset.ofNat_sub_ofNat hb
  · rw [u₆.other _ h₂, u₅.other _ h₃, u₄.gpr, u₃.gpr, u₂.other _ h₅, u₁.other _ h₄]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

theorem swap_wp (s : State) {L : Addr} {b : Nat} (hb₀ : 0 < b) (hb : b < 16) (hx : s.gpr .t3 = L)
    (hc : s.gpr .t2 = BitVec.ofNat 64 b) (hw : ∀ i < 16 + b, InRegions s.wr (L + BitVec.ofNat 64 i) 1) :
    WP isa swap s fun s' => s'.mem = swapMem s.mem L b ∧
      (∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine WP.loop (M := isa) (body := .block swapBody) (c := .nonzero .t2)
    (fun (n : Nat) (t : State) => ∃ k, n = b - k ∧ k < b ∧ t.gpr .t3 = L + BitVec.ofNat 64 k ∧
      t.gpr .t2 = BitVec.ofNat 64 (b - k) ∧ t.mem = swapMem s.mem L k ∧
      (∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp) ?_ (b - 0) _
    ⟨0, rfl, hb₀, by rw [hx, BitVec.add_zero], hc, (Proof.AesXts.Unit.swapMem_zero _ _).symm,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨k, rfl, hk, x3, x2, mem, g, rd, wr, sp⟩
  refine WP.mono (swapStep_wp t (k := k) (b := b - k) x3 x2 (by omega_using [hk]) (by rw [wr]; exact hw k (by omega_using [hk]))
    (by rw [wr]; exact hw (16 + k) (by omega_using [hk]))) fun t' ⟨mem', x3', x2', g', rd', wr', sp'⟩ => ?_
  have hmem : t'.mem = swapMem s.mem L (k + 1) := by
    rw [mem', mem, swapMem_lo _ _ (Nat.le_refl k) (by omega_using [hb, hk]), swapMem_hi _ _ (Nat.le_refl k) (by omega_using [hb, hk]),
      swapMem_step _ _ (by omega_using [hb, hk])]
  have hz := eval_nonzero_ofNat t' .t2 (k := b - k - 1) (by omega_using [hb]) x2'
  have gg : ∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : k + 1 = b
  · left
    refine ⟨by rw [hz]; simp [show b - k - 1 = 0 by omega_using [he]], by rw [hmem, he], gg, by rw [rd', rd],
      by rw [wr', wr], by rw [sp', sp]⟩
  · right
    refine ⟨by rw [hz]; simp [show b - k - 1 ≠ 0 by omega_using [hk, he]], b - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, he], x3',
      by rw [x2', show b - k - 1 = b - (k + 1) by omega_using []], hmem, gg, by rw [rd', rd], by rw [wr', wr],
      by rw [sp', sp]⟩

/-! ## The next tweak -/

theorem nextT_wp (s : State) {T Z : Addr} (ht : s.gpr .s6 + BitVec.ofNat 64 tO = T)
    (hz : s.gpr .s6 + BitVec.ofNat 64 zO = Z) (hd : (⟨Z, 16⟩ : Region).Disjoint ⟨T, 16⟩)
    (rT : ∀ i < 16, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 i) 1)
    (wZ : ∀ i < 16, InRegions s.wr (Z + BitVec.ofNat 64 i) 1)
    (inR : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (Z + BitVec.ofNat 64 d) 4)
    (inW : ∀ d, d + 4 ≤ 16 → InRegions s.wr (Z + BitVec.ofNat 64 d) 4) :
    WP isa (.block nextT) s fun s' =>
      (∀ r, r ∉ AesXts.RISCV64.mulRegs → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.gpr .s3 = Z ∧
      Frame [⟨Z, 16⟩] s.mem s'.mem ∧ bytesAt s'.mem Z 16 = Spec.Xts.mulAlpha (bytesAt s.mem T 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have et (i : Nat) : s.gpr .s6 + BitVec.ofNat 64 (tO + i) = T + BitVec.ofNat 64 i := by
    rw [← ht, Offset.add_add]
  have ez (i : Nat) : s.gpr .s6 + BitVec.ofNat 64 (zO + i) = Z + BitVec.ofNat 64 i := by
    rw [← hz, Offset.add_add]
  rw [nextT, List.singleton_append]
  refine wp_addi (imm := zO) (by decide) fun s₁ u₁ => ?_
  have g6 : s₁.gpr .s6 = s.gpr .s6 := u₁.other _ (by decide)
  rw [List.append_eq, WP.block_append_iff]
  refine WP.mono (Bytes.copyBytes_ok (s := s₁) (tmp := .t3) (src := .s6) (dst := .s6) (soff := tO)
    (doff := zO) (n := 16) (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by rw [g6, et, u₁.rd, u₁.wr]; exact rT i hi)
    (fun i hi => by rw [g6, ez, u₁.wr]; exact wZ i hi)
    (fun i hi hc => by
      rw [g6, hz, et] at hc
      exact hd _ hc (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])))) fun s₂ h₂ => ?_
  have hb₂ : bytesAt s₂.mem Z 16 = bytesAt s.mem T 16 := by
    apply List.ext_getElem (by simp [bytesAt])
    intro j h₁ _
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have := h₂.copied j h₁
    rw [g6, ez, et, u₁.mem] at this
    simp [bytesAt, this]
  have f₂ : Frame [⟨Z, 16⟩] s.mem s₂.mem := by
    have := h₂.frame
    rwa [g6, hz, u₁.mem] at this
  have s3₂ : s₂.gpr .s3 = Z := by rw [h₂.gpr _ (by decide), u₁.gpr, hz]
  rw [← List.append_nil Impl.AesXts.RISCV64.mulA]
  refine AesXts.RISCV64.mulA_wp s3₂ (by rw [h₂.rd, h₂.wr, u₁.rd, u₁.wr]; exact inR)
    (by rw [h₂.wr, u₁.wr]; exact inW) fun s₃ g₃ b₃ f₃ rd₃ wr₃ sp₃ => WP.block_nil ?_
  refine ⟨fun r h₁ h₂' => ?_, by rw [g₃ _ (by decide), s3₂], f₂.trans f₃, by rw [b₃, hb₂],
    by rw [rd₃, h₂.rd, u₁.rd], by rw [wr₃, h₂.wr, u₁.wr], by rw [sp₃, h₂.sp, u₁.sp]⟩
  have h3 : r ≠ .t3 := fun e => h₁ (by rw [e]; decide)
  rw [g₃ r h₁, h₂.gpr r h3, u₁.other r h₂']

end VG.Proof.AesXts.RISCV64.Unit

end

end

/-! ### `AesXts.RISCV64.Unit.Pre`, which this module and modules that import it used -/

section

/-! ### `AesXts.RISCV64.Unit.Contract`, which this module and modules that import it used -/

section

/-!
# XTS-AES of data units on RISC-V: the contract the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Xts/Contract.lean`, which imply `unitRISCV64`
(`Verified.lean`): `(schedule = a0, tweak_schedule = a1, rounds = a2,
i = a3, data = a4, len = a5, scratch = a6)`. A call (`jal`) stores nothing
in memory, and the return address is saved in the scratch buffer, so no
stack is used.

`UPre` names the facts of the precondition; the regions of the scratch
buffer (the tweaks `tzR`, the slots `slotR` of the saved registers, the
working space `wkR`) are apart from each other and from everything else, as
on PPC64LE (`Proof/AesXts/PPC64LE/Unit/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.RISCV64.Align
open VG.Impl.AesXts.RISCV64Unit (tO zO wO)
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

abbrev W : Addr := s.gpr .a0
abbrev K : Addr := s.gpr .a1
abbrev R : Nat := (s.gpr .a2).toNat
abbrev I : Addr := s.gpr .a3
abbrev D : Addr := s.gpr .a4
abbrev Len : Nat := (s.gpr .a5).toNat
abbrev S : Addr := s.gpr .a6

abbrev schR : Region := ⟨W s, 240⟩
abbrev tschR : Region := ⟨K s, 240⟩
abbrev iR : Region := ⟨I s, 16⟩
abbrev dataR : Region := ⟨D s, Len s⟩
abbrev scrR : Region := ⟨S s, 2432⟩

/-- The tweak, the second tweak, both of them, the working space of the
calls, and where the slots of the saved registers are, in the scratch
buffer. -/
abbrev tR : Region := ⟨S s + BitVec.ofNat 64 tO, 16⟩
abbrev zR : Region := ⟨S s + BitVec.ofNat 64 zO, 16⟩
abbrev tzR : Region := ⟨S s, 32⟩
abbrev Wk : Addr := S s + BitVec.ofNat 64 wO
abbrev wkR : Region := ⟨Wk s, 2176⟩
abbrev slotR : Region := ⟨S s + BitVec.ofNat 64 32, 64⟩

/-- The slots: `scratch + 32`, rounded up. -/
abbrev sv : Addr := S s + BitVec.ofNat 64 32 + BitVec.ofNat 64 (pad (S s + BitVec.ofNat 64 32))

/-- The number of whole blocks, the bytes after them, and the last whole block. -/
abbrev M : Nat := Len s / 16
abbrev B : Nat := Len s % 16
abbrev L : Addr := D s + BitVec.ofNat 64 (16 * (M s - 1))

end

/-- What the functions need: the permissions, the buffers apart, `rounds`
of 10, 12 or 14, and a data unit of 16 bytes to 2²⁰ blocks. -/
def unitPre (s : State) : Prop :=
  s.rd = [schR s, tschR s, iR s] ∧ s.wr = [dataR s, scrR s] ∧
    (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (scrR s) ∧ (tschR s).Disjoint (dataR s) ∧
    (tschR s).Disjoint (scrR s) ∧ (iR s).Disjoint (dataR s) ∧ (iR s).Disjoint (scrR s) ∧
    (dataR s).Disjoint (scrR s) ∧
    (I s).toNat + 16 ≤ 2 ^ 64 ∧ (D s).toNat + Len s ≤ 2 ^ 64 ∧ (S s).toNat + 2432 ≤ 2 ^ 64 ∧
    (R s = 10 ∨ R s = 12 ∨ R s = 14) ∧ 16 ≤ Len s ∧ Len s ≤ 16 * Spec.Xts.maxBlocks

/-- XTS-AES of the data unit in a direction. -/
def xtsOf : Bool → List Byte → List Byte → List Byte → Option (List Byte)
  | true => Spec.Xts.aesXtsEncrypt
  | false => Spec.Xts.aesXtsDecrypt

def unitPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.sp = s₂.sp

/-- `vg_aes_xts_encrypt_unit` (`enc`) or `vg_aes_xts_decrypt_unit`. -/
def unitRISCV64 (enc : Bool) : Contract isa where
  pre := unitPre
  post s s' := ∀ key, Spec.Xts.KeySchedules s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2).toNat key →
    xtsOf enc key (bytesAt s.mem (s.gpr .a3) 16) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) =
      some (bytesAt s'.mem (s.gpr .a4) (s.gpr .a5).toNat)
  pub := unitPub

/-- The precondition, by name. -/
structure UPre (s : State) : Prop where
  rd : s.rd = [schR s, tschR s, iR s]
  wr : s.wr = [dataR s, scrR s]
  sch_data : (schR s).Disjoint (dataR s)
  sch_scr : (schR s).Disjoint (scrR s)
  tsch_data : (tschR s).Disjoint (dataR s)
  tsch_scr : (tschR s).Disjoint (scrR s)
  i_data : (iR s).Disjoint (dataR s)
  i_scr : (iR s).Disjoint (scrR s)
  data_scr : (dataR s).Disjoint (scrR s)
  i_wrap : (I s).toNat + 16 ≤ 2 ^ 64
  data_wrap : (D s).toNat + Len s ≤ 2 ^ 64
  scr_wrap : (S s).toNat + 2432 ≤ 2 ^ 64
  rounds : R s = 10 ∨ R s = 12 ∨ R s = 14
  len_lo : 16 ≤ Len s
  len_hi : Len s ≤ 16 * Spec.Xts.maxBlocks

theorem UPre.of {s : State} (h : unitPre s) : UPre s :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩

/-! ## Regions -/

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

/-- The regions the code writes, but the slots. -/
abbrev Wr (s : State) : List Region := [dataR s, tzR s, wkR s]

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.m_pos : 1 ≤ M s := by have := hp.len_lo; simp only [M]; omega_using [this]

omit hp in
theorem len_eq (s : State) : Len s = 16 * M s + B s := by simp only [M, B]; omega_using []

omit hp in
theorem scr_sub {d n : Nat} (h : d + n ≤ 2432) : Region.Sub ⟨S s + BitVec.ofNat 64 d, n⟩ (scrR s) :=
  Offset.sub_base _ h

omit hp in
theorem data_sub {d n : Nat} (h : d + n ≤ Len s) : Region.Sub ⟨D s + BitVec.ofNat 64 d, n⟩ (dataR s) :=
  Offset.sub_base _ h

omit hp in
theorem wk_sub : Region.Sub (wkR s) (scrR s) := scr_sub (by simp [wO])

omit hp in
theorem tz_sub : Region.Sub (tzR s) (scrR s) := Region.sub_prefix (by decide)

omit hp in
theorem slot_scr : Region.Sub (slotR s) (scrR s) := scr_sub (by decide)

omit hp in
theorem t_sub : Region.Sub (tR s) (tzR s) := by
  show Region.Sub ⟨S s + BitVec.ofNat 64 0, 16⟩ ⟨S s, 32⟩
  rw [show S s + BitVec.ofNat 64 0 = S s by simp]; exact Region.sub_prefix (by decide)

omit hp in
theorem z_sub : Region.Sub (zR s) (tzR s) := Offset.sub_base _ (by simp [zO])

theorem UPre.t_wk : (tR s).Disjoint (wkR s) :=
  Offset.disjoint _ (by simp [tO, wO]) (by have := hp.scr_wrap; simp only [tO]; omega_using [])
    (by have := hp.scr_wrap; simp only [wO]; omega_using [])

theorem UPre.z_wk : (zR s).Disjoint (wkR s) :=
  Offset.disjoint _ (by simp [zO, wO]) (by have := hp.scr_wrap; simp only [zO]; omega_using [])
    (by have := hp.scr_wrap; simp only [wO]; omega_using [])

theorem UPre.t_z : (tR s).Disjoint (zR s) :=
  Offset.disjoint _ (by simp [tO, zO]) (by have := hp.scr_wrap; simp only [tO]; omega_using [])
    (by have := hp.scr_wrap; simp only [zO]; omega_using [])

theorem UPre.slot_tz : (slotR s).Disjoint (tzR s) :=
  Offset.disjoint_base (S s) (d := 32) (n := 64) (k := 32) (Nat.le_refl _) (by have := hp.scr_wrap; omega_using [])

theorem UPre.slot_wk : (slotR s).Disjoint (wkR s) :=
  Offset.disjoint _ (by simp [wO]) (by have := hp.scr_wrap; omega_using []) (by have := hp.scr_wrap; simp only [wO]; omega_using [])

theorem UPre.slot_data : (slotR s).Disjoint (dataR s) := hp.data_scr.symm.sub_left slot_scr

omit hp in
/-- The slots of the saved registers. -/
theorem sv_slot (d : Nat) (h : d + 8 ≤ 56) : Region.Sub ⟨sv s + BitVec.ofNat 64 d, 8⟩ (slotR s) := by
  have := pad_lt (S s + BitVec.ofNat 64 32)
  rw [align_add]
  exact Offset.sub _ (by omega_using []) (by omega_using [h, this])

/-- Everything the code writes but the slots lies within the data, the
tweaks or the working space. -/
theorem UPre.slots_disj {r : Region} (hr : ∃ r' ∈ Wr s, Region.Sub r r') : (slotR s).Disjoint r := by
  obtain ⟨r', hr', hs⟩ := hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact hp.slot_data.sub_right hs
  · exact hp.slot_tz.sub_right hs
  · exact hp.slot_wk.sub_right hs

theorem UPre.l_sub : Region.Sub ⟨L s, 16⟩ (dataR s) := data_sub (by have := len_eq s; have := hp.m_pos; omega_arith)

theorem UPre.l_wrap : (L s).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := len_eq s; have := hp.m_pos
  rw [L, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (M s - 1)) (by omega),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

end

/-! ## The parts of the data unit -/

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.wrapD : (D s).toNat + 16 * M s + B s ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := len_eq s; omega_arith

omit hp in
theorem blocks_sub {N : Nat} (h : N ≤ M s) : Region.Sub ⟨D s, 16 * N⟩ (dataR s) :=
  Region.sub_prefix (by have := len_eq s; omega_using [h, this])

theorem UPre.lb_sub : Region.Sub ⟨L s, 16 + B s⟩ (dataR s) :=
  data_sub (by have := len_eq s; have := hp.m_pos; omega_arith)

theorem UPre.tl_eq : L s + 16 = D s + BitVec.ofNat 64 (16 * M s) := by
  rw [L, Proof.AesXts.Unit.add16, show 16 * (M s - 1) + 16 = 16 * M s by have := hp.m_pos; omega_using [this]]

theorem UPre.tl_sub : Region.Sub ⟨L s + 16, B s⟩ (dataR s) := by
  rw [hp.tl_eq]; exact data_sub (by have := len_eq s; omega_using [this])

theorem UPre.hd_lb : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16 + B s⟩ :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.wrapD; have := hp.m_pos; omega_arith)

theorem UPre.hd_l : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  hp.hd_lb.sub_right (Region.sub_prefix (by omega_using []))

theorem UPre.hd_tl : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s + 16, B s⟩ := by
  rw [hp.tl_eq]
  exact Offset.base_disjoint _ (by omega_using []) (by have := hp.wrapD; omega_using [this])

omit hp in
theorem tl_l : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  Offset.disjoint_base (L s) (d := 16) (n := B s) (k := 16) (Nat.le_refl _) (by simp only [B]; omega_using [])

theorem UPre.tl_blocks : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨D s, 16 * M s⟩ := by
  rw [hp.tl_eq]
  exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.wrapD; omega_using [this])

theorem UPre.l_hd : (⟨L s, 16⟩ : Region).Disjoint ⟨D s, 16 * (M s - 1)⟩ := hp.hd_l.symm

end

end VG.Proof.AesXts.RISCV64.Unit

end

end

/-! ### `AesXts.RISCV64.Unit.Call`, which this module and modules that import it used -/

section

/-!
# XTS-AES of data units on RISC-V: a call of a whole-block function

As on PPC64LE (`Proof/AesXts/PPC64LE/Unit/Verified.lean`): `xts_call`, a call of
`vg_aes_xts_encrypt` or `vg_aes_xts_decrypt` (`enc` true or false) on `N`
blocks at `D`, from the tweak at `T`, with working space `S`, from its
contract (`WP.call`): the blocks are then XTS of them, the tweak the one
after them, and only the tweak, the blocks and `S` change. `xts_rel`: such
calls, with the same arguments in both runs, are constant time.
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64
open VG.Proof.AesCbc.RISCV64 (modeRISCV64 toNat_rounds)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesXts.Unit (blocks_bytesAt)
open VG.Spec.Aes (bytesAt)

/-- What a call of a whole-block function on `N` blocks needs. -/
structure XPre (s : State) (W T D S : Addr) (N R : Nat) : Prop where
  a0 : s.gpr .a0 = W
  a1 : s.gpr .a1 = BitVec.ofNat 64 R
  a2 : s.gpr .a2 = T
  a3 : s.gpr .a3 = D
  a4 : s.gpr .a4 = BitVec.ofNat 64 N
  a5 : s.gpr .a5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  n : N < 2 ^ 60
  wt : (⟨W, 240⟩ : Region).Disjoint ⟨T, 16⟩
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16 * N⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  td : (⟨T, 16⟩ : Region).Disjoint ⟨D, 16 * N⟩
  ts : (⟨T, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  ds : (⟨D, 16 * N⟩ : Region).Disjoint ⟨S, 2176⟩
  wrapT : T.toNat + 16 ≤ 2 ^ 64
  wrapD : D.toNat + 16 * N ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩] s.wr

/-- What a call of a whole-block function on `N` blocks leaves. -/
structure XPost (enc : Bool) (s : State) (W T D S : Addr) (N R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem D N =
    Spec.Xts.crypt (ciphOf enc R (bytesAt s.mem W (16 * (R + 1)))) (bytesAt s.mem T 16)
      (Spec.Cbc.blocksAt s.mem D N)
  tw : bytesAt s'.mem T 16 = Spec.Xts.next (bytesAt s.mem T 16) N

theorem toNat_n {N : Nat} (h : N < 2 ^ 60) : (BitVec.ofNat 64 N).toNat = N := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [h])

theorem ce0 (s : State) : s.callEntry.gpr .a0 = s.gpr .a0 := s.callEntry_gpr (by decide)
theorem ce1 (s : State) : s.callEntry.gpr .a1 = s.gpr .a1 := s.callEntry_gpr (by decide)
theorem ce2 (s : State) : s.callEntry.gpr .a2 = s.gpr .a2 := s.callEntry_gpr (by decide)
theorem ce3 (s : State) : s.callEntry.gpr .a3 = s.gpr .a3 := s.callEntry_gpr (by decide)
theorem ce4 (s : State) : s.callEntry.gpr .a4 = s.gpr .a4 := s.callEntry_gpr (by decide)
theorem ce5 (s : State) : s.callEntry.gpr .a5 = s.gpr .a5 := s.callEntry_gpr (by decide)

/-- The whole-block function's precondition, on entry to a call with the
regions it is given. -/
theorem XPre.mode_pre {enc : Bool} {s : State} {W T D S : Addr} {N R : Nat} (h : XPre s W T D S N R) :
    (modeRISCV64 (AesXts.xtsMode enc)).pre
      (s.callEntry.withRegions [⟨W, 240⟩] [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce0, ce1, ce2, ce3, ce4, ce5, h.a0, h.a1, h.a2, h.a3, h.a4, h.a5, hR, hN]
  exact ⟨trivial, trivial, h.wt, h.wd, h.ws, h.td, h.ts, h.ds, h.wrapT, h.wrapD, h.wrapS, h.rounds⟩

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  rw [← blocks_bytesAt, ← blocks_bytesAt, Proof.Cmac.bytesAt_frame hf hd hn]

theorem xts_call (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeRISCV64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (AesXts.xtsMode enc)).post s s')
    (nf : c.noFrames = true)
    {s : State} {W T D S : Addr} {N R : Nat} (h : XPre s W T D S N R) :
    WP isa (.call n c) s (XPost enc s W T D S N R) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  refine WP.call (k := modeRISCV64 (AesXts.xtsMode enc)) ok (rd := [⟨W, 240⟩])
    (wr := [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) h.mode_pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hsaved _ hpost
  simp only [modeRISCV64, AesXts.xtsMode, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    ce0, ce1, ce2, ce3, ce4, h.a0, h.a1, h.a2, h.a3, h.a4, hR, hN,
    Proof.AesXts.Unit.length_blocksAt] at hpost
  exact ⟨hrd, hwr, hsp, hsaved, hf, hpost.1, hpost.2⟩

/-- Calls of a whole-block function, with the same arguments in both runs,
are constant time. -/
theorem xts_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeRISCV64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (AesXts.xtsMode enc)).post s s')
    (ct : ConstantTime isa (modeRISCV64 (AesXts.xtsMode enc)).pre (modeRISCV64 (AesXts.xtsMode enc)).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : Addr, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine RelCT.callEx ok ct fun s₁ s₂ hp => ?_
  obtain ⟨W, T, D, S, N, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.mode_pre (enc := enc), h₂.mode_pre (enc := enc), ?_, h₁.reads, h₁.writes, h₂.reads,
    h₂.writes⟩
  simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    ce0, ce1, ce2, ce3, ce4, ce5, h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₁.a5, h₂.a0, h₂.a1, h₂.a2, h₂.a3,
    h₂.a4, h₂.a5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesXts.RISCV64.Unit

end

end

/-!
# XTS-AES of data units on RISCV64: the arguments of each call

The five calls of a whole-block function the functions make, each with
`XPre` from the precondition (`UPre`), for a state with the permissions
of the entry state and the call's arguments in its registers:

* `xpre_tweak`: the tweak value `i`, copied to the tweak (`tR`), enciphered
  with `tweak_schedule` from the zero second tweak (`zR`);
* `xpre_blocks`: the first `N` whole blocks of the data, from the tweak;
* `xpre_last`: the last whole block (`L`), from the tweak (`o = tO`) or from
  the second tweak (`o = zO`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64
open VG.Impl.AesXts.RISCV64Unit (tO zO wO)

theorem wrap_off (p : Addr) {d n k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d + n ≤ k) (hn : 0 < n := by decide) :
    (p + BitVec.ofNat 64 d).toNat + n ≤ 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [h, hd, hn]), Nat.mod_eq_of_lt (by omega_using [h, hd, hn])]
  omega_using [h, hd]

section
variable {s₀ s : State} (hp : UPre s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
include hp hrd hwr

theorem xpre_tweak (a0 : s.gpr .a0 = K s₀) (a1 : s.gpr .a1 = BitVec.ofNat 64 (R s₀))
    (a2 : s.gpr .a2 = S s₀ + BitVec.ofNat 64 zO) (a3 : s.gpr .a3 = S s₀ + BitVec.ofNat 64 tO)
    (a4 : s.gpr .a4 = BitVec.ofNat 64 1) (a5 : s.gpr .a5 = Wk s₀) :
    XPre s (K s₀) (S s₀ + BitVec.ofNat 64 zO) (S s₀ + BitVec.ofNat 64 tO) (Wk s₀) 1 (R s₀) where
  a0 := a0
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4
  a5 := a5
  rounds := hp.rounds
  n := by decide
  wt := hp.tsch_scr.sub_right (sub_trans z_sub tz_sub)
  wd := hp.tsch_scr.sub_right (sub_trans t_sub tz_sub)
  ws := hp.tsch_scr.sub_right wk_sub
  td := hp.t_z.symm
  ts := hp.z_wk
  ds := hp.t_wk
  wrapT := wrap_off _ hp.scr_wrap (by decide)
  wrapD := wrap_off _ hp.scr_wrap (by decide)
  wrapS := wrap_off _ hp.scr_wrap (by simp [wO])
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨tschR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨scrR s₀, by simp, wO, rfl, by simp [wO]⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨scrR s₀, by simp, wO, rfl, by simp [wO]⟩

theorem xpre_blocks {N : Nat} (hN : 16 * N ≤ Len s₀) (a0 : s.gpr .a0 = W s₀)
    (a1 : s.gpr .a1 = BitVec.ofNat 64 (R s₀)) (a2 : s.gpr .a2 = S s₀ + BitVec.ofNat 64 tO)
    (a3 : s.gpr .a3 = D s₀) (a4 : s.gpr .a4 = BitVec.ofNat 64 N) (a5 : s.gpr .a5 = Wk s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 64 tO) (D s₀) (Wk s₀) N (R s₀) where
  a0 := a0
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4
  a5 := a5
  rounds := hp.rounds
  n := by have := hp.len_hi; simp only [Spec.Xts.maxBlocks] at this; omega_using [hN, this]
  wt := hp.sch_scr.sub_right (sub_trans t_sub tz_sub)
  wd := hp.sch_data.sub_right (Region.sub_prefix hN)
  ws := hp.sch_scr.sub_right wk_sub
  td := (hp.data_scr.symm.sub_left (sub_trans t_sub tz_sub)).sub_right (Region.sub_prefix hN)
  ts := hp.t_wk
  ds := (hp.data_scr.sub_left (Region.sub_prefix hN)).sub_right wk_sub
  wrapT := wrap_off _ hp.scr_wrap (by decide)
  wrapD := by have := hp.data_wrap; omega_using [hN, this]
  wrapS := wrap_off _ hp.scr_wrap (by simp [wO])
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
    · exact ⟨scrR s₀, by simp, wO, rfl, by simp [wO]⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
    · exact ⟨scrR s₀, by simp, wO, rfl, by simp [wO]⟩

theorem xpre_last {o : Nat} (ho : o = tO ∨ o = zO) (a0 : s.gpr .a0 = W s₀)
    (a1 : s.gpr .a1 = BitVec.ofNat 64 (R s₀)) (a2 : s.gpr .a2 = S s₀ + BitVec.ofNat 64 o)
    (a3 : s.gpr .a3 = L s₀) (a4 : s.gpr .a4 = BitVec.ofNat 64 1) (a5 : s.gpr .a5 = Wk s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 64 o) (L s₀) (Wk s₀) 1 (R s₀) := by
  have oS : Region.Sub ⟨S s₀ + BitVec.ofNat 64 o, 16⟩ (tzR s₀) := by
    rcases ho with rfl | rfl
    · exact t_sub
    · exact z_sub
  have oW : (⟨S s₀ + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint (wkR s₀) := by
    rcases ho with rfl | rfl
    · exact hp.t_wk
    · exact hp.z_wk
  have ol : o + 16 ≤ 2432 := by rcases ho with rfl | rfl <;> decide
  have lS : Region.Sub ⟨L s₀, 16 * 1⟩ (dataR s₀) := hp.l_sub
  exact {
    a0 := a0
    a1 := a1
    a2 := a2
    a3 := a3
    a4 := a4
    a5 := a5
    rounds := hp.rounds
    n := by decide
    wt := hp.sch_scr.sub_right (sub_trans oS tz_sub)
    wd := hp.sch_data.sub_right lS
    ws := hp.sch_scr.sub_right wk_sub
    td := (hp.data_scr.symm.sub_left (sub_trans oS tz_sub)).sub_right lS
    ts := oW
    ds := (hp.data_scr.sub_left lS).sub_right wk_sub
    wrapT := wrap_off _ hp.scr_wrap ol
    wrapD := hp.l_wrap
    wrapS := wrap_off _ hp.scr_wrap (by simp [wO])
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scrR s₀, by simp, o, rfl, by simpa using ol⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega_using [this]⟩
      · exact ⟨scrR s₀, by simp, wO, rfl, by simp [wO]⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, o, rfl, by simpa using ol⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega_using [this]⟩
      · exact ⟨scrR s₀, by simp, wO, rfl, by simp [wO]⟩ }

end

end VG.Proof.AesXts.RISCV64.Unit

end

end

/-! ### `AesXts.RISCV64.Unit.Run`, which only this module used -/

section

/-!
# XTS-AES of data units on RISC-V: the tweak, and what every piece keeps

As on PPC64LE (`Proof/AesXts/PPC64LE/Unit/Run.lean`). `Inv`: between the
calls the code keeps its arguments in `s1`, `s2`, `s4`, `s5` and `s6`, its
caller's other callee-saved registers, the saved registers and its return
address in their slots at `sv`, the stack pointer, and changes memory only in
the data and the scratch buffer (`Inv.step`, for any code whose frame is in
the data, the tweaks or the working space). `tweak_wp`: the prologue and the
call enciphering the tweak value leave `T = AES-enc(Key2, i)` in the tweak
(`TwPost`). `fin_wp`: the epilogue restores the registers and the return
address.
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.AesXts.RISCV64Unit
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.RISCV64 (modeRISCV64)
open VG.Spec.Aes (bytesAt)

section
variable (s₀ : State)

/-- The tweak and the second tweak. -/
abbrev Tp : Addr := S s₀ + BitVec.ofNat 64 tO
abbrev Zp : Addr := S s₀ + BitVec.ofNat 64 zO

/-- `T = AES-enc(Key2, i)`. -/
abbrev t0 : List Byte :=
  Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1))) (bytesAt s₀.mem (I s₀) 16)

/-- `AES-enc(Key1, ·)` (`enc`) or `AES-dec(Key1, ·)`. -/
abbrev ciph (enc : Bool) : Spec.Cbc.Cipher := ciphOf enc (R s₀) (bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)))

/-- The slots of the return address and the registers, from `sv`. -/
abbrev saveL : List (Reg × Nat) := saved

/-- What the slots hold: the registers on entry (`t0` holds `sv`). -/
abbrev saveG : Reg → BitVec 64 := (s₀.write .t0 (sv s₀)).gpr

end

theorem save_eq : save = savePtr .a6 ++ Spill.saveCode .t0 saveL := rfl

theorem restore_eq : restore = savePtr .s6 ++ Spill.restoreCode .t0 saveL := rfl

theorem copyI_eq : copyI = Impl.AesCbc.RISCV64.copy .s6 .a3 := rfl

theorem tp_eq (s₀ : State) : Tp s₀ = S s₀ := by simp [Tp, tO]

/-- `t0 :=` the register `n`'s value plus 32, rounded up. -/
theorem savePtr_ok {s : State} (n : Reg) :
    WP isa (.block (savePtr n)) s (· = s.write .t0
      (s.gpr n + BitVec.ofNat 64 32 + BitVec.ofNat 64 (pad (s.gpr n + BitVec.ofNat 64 32)))) := by
  apply WP.of_runBlock
  simp only [savePtr, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 39 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write, Option.some.injEq,
    exists_eq_left']
  rw [align_off_eq _ (off := 32) (by decide) (by decide)]

/-- The registers holding our variables. -/
abbrev vars : List Reg := [.s1, .s2, .s3, .s4, .s5, .s6]

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  s1 : s.gpr .s1 = W s₀
  s2 : s.gpr .s2 = s₀.gpr .a2
  s4 : s.gpr .s4 = D s₀
  s5 : s.gpr .s5 = s₀.gpr .a5
  s6 : s.gpr .s6 = S s₀
  rest : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  saved : Spill.Saved (sv s₀) (saveG s₀) saveL s.mem

theorem saved_bound : ∀ p ∈ saveL, p.2 + 8 ≤ 56 := by decide

theorem a2_ofNat (s₀ : State) : BitVec.ofNat 64 (R s₀) = s₀.gpr .a2 := by
  rw [R, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cS (s₀ : State) (d n : Nat) (h : d + n ≤ 2432) : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by omega_using [h])

/-- A saved register's slot, within the scratch buffer. -/
theorem slot_contains (s₀ : State) (d : Nat) (h : d + 8 ≤ 56) :
    (scrR s₀).Contains (sv s₀ + BitVec.ofNat 64 d) 8 := by
  have := pad_lt (S s₀ + BitVec.ofNat 64 32)
  rw [align_add]; exact Offset.contains_base _ (by omega_using [h, this]) (by omega_using [h, this])

/-- The slots, within the slot region. -/
theorem slots_sub (s₀ : State) : Region.Sub ⟨sv s₀ + BitVec.ofNat 64 0, 56⟩ (slotR s₀) := by
  have := pad_lt (S s₀ + BitVec.ofNat 64 32)
  rw [align_add]; exact Offset.sub _ (by omega_using []) (by omega_using [this])

theorem in_rw {rs : List Region} {r : Region} {a : Addr} {n : Nat} (hr : r ∈ rs) (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

theorem ne_s3 {r : Reg} (hv : r ∉ vars) : r ≠ .s3 := fun e => hv (by simp [e])

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- `Inv` across code that keeps the callee-saved registers (but `s3`) and
writes only within `rs`, each in the data, the tweaks or the working space. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, ∃ r' ∈ Wr s₀, Region.Sub r r')
    (hf : Frame rs s.mem s'.mem) (hg : ∀ r ∈ preserved, r ≠ .s3 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' where
  s1 := by rw [hg _ (by decide) (by decide), h.s1]
  s2 := by rw [hg _ (by decide) (by decide), h.s2]
  s4 := by rw [hg _ (by decide) (by decide), h.s4]
  s5 := by rw [hg _ (by decide) (by decide), h.s5]
  s6 := by rw [hg _ (by decide) (by decide), h.s6]
  rest r hr hv := by rw [hg r hr (ne_s3 hv), h.rest r hr hv]
  sp := by rw [hsp, h.sp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    obtain ⟨r', hr', hs⟩ := hrs r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, hs⟩
    · exact ⟨scrR s₀, by simp, sub_trans hs tz_sub⟩
    · exact ⟨scrR s₀, by simp, sub_trans hs wk_sub⟩)
  saved := h.saved.frame hf fun p hp' r hr =>
    (hp.slots_disj (hrs r hr)).sub_left (sv_slot p.2 (saved_bound p hp'))

/-- `Inv` across code that keeps the registers it pins and memory. -/
theorem Inv.regs {s s' : State} (h : Inv s₀ s) (hg : ∀ r ∈ preserved, r ≠ .s3 → s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' :=
  Inv.step hp h (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hg hsp hrd hwr

/-- `Inv` across a call of a whole-block function. -/
theorem Inv.call {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk' T Dd : Addr} {N Rr : Nat}
    (hT : Region.Sub ⟨T, 16⟩ (tzR s₀))
    (hD : Region.Sub ⟨Dd, 16 * N⟩ (dataR s₀) ∨ Region.Sub ⟨Dd, 16 * N⟩ (tzR s₀))
    (hc : XPost enc s Wk' T Dd (Wk s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h (rs := [⟨T, 16⟩, ⟨Dd, 16 * N⟩, ⟨Wk s₀, 2176⟩]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨tzR s₀, by simp, hT⟩
      · rcases hD with hD | hD
        · exact ⟨dataR s₀, by simp, hD⟩
        · exact ⟨tzR s₀, by simp, hD⟩
      · exact ⟨wkR s₀, by simp, fun _ h => h⟩)
    hc.frame (fun r hr _ => hc.saved r hr) hc.sp hc.rd hc.wr

/-! ## The prologue -/

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zp s₀) (Tp s₀) (Wk s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem (I s₀) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem pro_wp : WP isa (.block pro) s₀ (ProPost s₀) := by
  rw [pro, save_eq]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (savePtr_ok .a6) fun s₁ e => ?_
  subst e
  obtain t₀ : (s₀.write .t0 (sv s₀)).gpr .t0 = sv s₀ := RegUpd.gpr_write_self _ _ _
  refine Spill.save_ok (b := .t0) (l := saveL) (by rw [t₀]; exact align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := saved_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (slot_contains s₀ _ this)
  generalize hs₂ : ({ (s₀.write .t0 (sv s₀)) with
    mem := Spill.saveMem (s₀.write .t0 (sv s₀)).mem ((s₀.write .t0 (sv s₀)).gpr .t0)
      (s₀.write .t0 (sv s₀)).gpr saveL } : State) = s₂
  have gpr₂ (r : Reg) (hr : r ≠ .t0) : s₂.gpr r = s₀.gpr r := by
    rw [← hs₂]; exact RegUpd.gpr_write_of_ne _ _ hr
  obtain rd₂ : s₂.rd = s₀.rd := by rw [← hs₂]; rfl
  obtain wr₂ : s₂.wr = s₀.wr := by rw [← hs₂]; rfl
  obtain sp₂ : s₂.sp = s₀.sp := by rw [← hs₂]; rfl
  obtain mem₂ : s₂.mem = Spill.saveMem s₀.mem (sv s₀) (saveG s₀) saveL := by
    rw [← hs₂]; show Spill.saveMem _ _ _ _ = _; rw [t₀]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (setup_wp s₂) fun s₃ ⟨s1₃, s2₃, s4₃, s5₃, s6₃, g₃, mem₃', rd₃', wr₃', sp₃'⟩ => ?_
  rw [gpr₂ _ (by decide)] at s1₃ s2₃ s4₃ s5₃ s6₃
  obtain k₃ : ∀ r, r ≠ .t0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s₃.gpr r = s₀.gpr r :=
    fun r h₀ h₁ h₂ h₃ h₄ h₅ => by rw [g₃ r h₁ h₂ h₃ h₄ h₅, gpr₂ r h₀]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [rd₃', rd₂]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [wr₃', wr₂]
  obtain wr₃'' : s₃.wr = [dataR s₀, scrR s₀] := by rw [wr₃]; exact hp.wr
  obtain rdwr₃ : s₃.rd ++ s₃.wr = [schR s₀, tschR s₀, iR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, hp.rd, hp.wr]; rfl
  obtain tS : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub tz_sub
  rw [copyI_eq]
  refine AesCbc.RISCV64.copy_wp (P := Tp s₀) (Q := I s₀) (by decide) (by decide)
    (by rw [tp_eq, s6₃]) (by rw [k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    ⟨iR s₀, by rw [rdwr₃]; simp, fun _ h => h⟩ ⟨scrR s₀, by rw [wr₃'']; simp, tS⟩
    (hp.i_scr.symm.sub_left tS) fun s₄ g₄ b₄ f₄ rd₄ wr₄ sp₄ => ?_
  rw [WP.block_append_iff]
  obtain wr₄' : s₄.wr = [dataR s₀, scrR s₀] := by rw [wr₄, wr₃'']
  refine WP.mono (zeroZ_wp s₄ (Z := Zp s₀) (by rw [g₄ _ (by decide), s6₃]) fun i hi => by
      rw [wr₄', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO]; omega_using [hi])))
    fun s₅ ⟨g₅, z₅, f₅, rd₅, wr₅, sp₅⟩ => ?_
  refine WP.mono (tArgs_wp s₅) fun s₆ ⟨a0₆, a1₆, a2₆, a3₆, a4₆, a5₆, cs₆, mem₆, rd₆, wr₆, sp₆⟩ => ?_
  -- The registers.
  obtain k₅ : ∀ r, r ≠ .t1 → r ≠ .t3 → s₅.gpr r = s₃.gpr r := fun r h₁ h₃ => by rw [g₅ r h₁, g₄ r h₃]
  obtain s6₅ : s₅.gpr .s6 = S s₀ := by rw [k₅ _ (by decide) (by decide), s6₃]
  have cs (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₃.gpr r := by
    rw [cs₆ r hr, k₅ r (pres_ne hr (by decide)) (pres_ne hr (by decide))]
  obtain rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  -- The memory.
  obtain f₂ : Frame [scrR s₀] s₀.mem s₂.mem := by
    rw [mem₂]
    refine (Spill.saveMem_frame (lo := 0) (n := 56) (fun p hp' => ⟨Nat.zero_le _, by
      have := saved_bound p hp'; omega_using [this]⟩) (by decide) s₀.mem (sv s₀) (saveG s₀)).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, sub_trans (slots_sub s₀) slot_scr⟩
  have m₃ : s₃.mem = s₂.mem := mem₃'
  obtain frame : Frame [scrR s₀] s₀.mem s₆.mem := by
    rw [mem₆]
    refine f₂.trans ((by rw [← m₃]; exact f₄ : Frame _ s₂.mem s₄.mem).sub (fun r hr => ?_) |>.trans
      (f₅.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, tS⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, sub_trans z_sub tz_sub⟩
  obtain sv₂ : Spill.Saved (sv s₀) (saveG s₀) saveL s₂.mem := by
    rw [mem₂]; exact Spill.saveMem_saved (by decide) _ _ _
  obtain sdisj : ∀ (r : Region), Region.Sub r (tzR s₀) → ∀ p ∈ saveL, ∀ r' ∈ [r],
      Region.Disjoint ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ r' := fun r hr p hp' r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.slots_disj ⟨tzR s₀, by simp, hr⟩).sub_left (sv_slot p.2 (saved_bound p hp'))
  obtain sv₆ : Spill.Saved (sv s₀) (saveG s₀) saveL s₆.mem := by
    rw [mem₆]
    exact ((by rw [m₃]; exact sv₂ : Spill.Saved _ _ _ s₃.mem).frame f₄ (sdisj _ t_sub)).frame f₅
      (sdisj _ z_sub)
  refine ⟨⟨by rw [cs _ (by decide), s1₃], by rw [cs _ (by decide), s2₃], by rw [cs _ (by decide), s4₃],
    by rw [cs _ (by decide), s5₃], by rw [cs _ (by decide), s6₃], fun r hr hv => ?_,
    by rw [sp₆, sp₅, sp₄, sp₃', sp₂], rd₆', wr₆',
    frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, sv₆⟩, ?_, frame, ?_, ?_⟩
  · simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    obtain ⟨h1, h2, -, h4, h5, h6⟩ := hv
    rw [cs r hr]
    exact k₃ r (pres_ne hr (by decide)) h1 h2 h4 h5 h6
  · refine xpre_tweak hp rd₆' wr₆' ?_ ?_ (by rw [a2₆, s6₅]) (by rw [a3₆, s6₅]) a4₆ (by rw [a5₆, s6₅])
    · rw [a0₆, k₅ _ (by decide) (by decide),
        k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [a1₆, k₅ _ (by decide) (by decide), s2₃, a2_ofNat]
  · rw [mem₆, Proof.Cmac.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), b₄, m₃,
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.i_scr) (by decide)]
  · rw [mem₆, z₅]

/-! ## The tweak -/

/-- After the call enciphering the tweak value. -/
structure TwPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  frame : Frame [scrR s₀] s₀.mem s.mem
  t : bytesAt s.mem (Tp s₀) 16 = t0 s₀

theorem UPre.sched_frame {s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, r = dataR s₀ ∨ r = scrR s₀ ∨ Region.Sub r (dataR s₀)) :
    bytesAt s.mem (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hRb])
  rcases hd r hr with rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- A whole-block function, verified. -/
abbrev XtsOk (enc : Bool) (c : Prog isa) : Prop :=
  ∀ s, (modeRISCV64 (AesXts.xtsMode enc)).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (AesXts.xtsMode enc)).post s s'

/-- The call enciphering the tweak value. -/
theorem tcall_wp {n : String} {c : Prog isa} (ok : XtsOk true c) (nf : c.noFrames = true) {s₂ : State}
    (h₂ : ProPost s₀ s₂) : WP isa (.call n c) s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true ok nf h₂.pre) fun s₃ c => ?_
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  obtain eK : bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.tsch_scr.sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])
  refine ⟨Inv.call hp h₂.inv z_sub (.inr t_sub) c, ?_, ?_⟩
  · refine (h₂.frame.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans z_sub tz_sub⟩
      · exact ⟨scrR s₀, by simp, sub_trans t_sub tz_sub⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
  · have := Proof.AesXts.Unit.tweak_of (R := R s₀) (w := bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1))) c.out h₂.z
    rw [this, h₂.ti, eK]

theorem tweak_wp (ok : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nf : Impl.AesXts.RISCV64.encrypt.noFrames = true) : WP isa tweak s₀ (TwPost s₀) :=
  WP.seq (WP.mono (pro_wp hp) fun _ h₂ => tcall_wp hp ok nf h₂)

/-! ## A call on whole blocks from the tweak -/

/-- After the call on the first `N` whole blocks from the tweak `T`. -/
structure AllPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  out : Spec.Cbc.blocksAt s.mem (D s₀) N =
    Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N)
  tw : bytesAt s.mem (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N
  frame : Frame [⟨D s₀, 16 * N⟩, scrR s₀] s₀.mem s.mem

theorem blocks_call (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c)
    (nf : c.noFrames = true) {N : Nat} (hN : 16 * N ≤ Len s₀) {s : State} (h : TwPost s₀ s)
    (hpre : XPre s (W s₀) (Tp s₀) (D s₀) (Wk s₀) N (R s₀)) :
    WP isa (.call n c) s (AllPost enc s₀ N) := by
  refine WP.mono (xts_call enc ok nf hpre) fun s' x => ?_
  obtain dS : Region.Sub ⟨D s₀, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  obtain eW := hp.sched_frame (h.inv.frame) (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  obtain eD : Spec.Cbc.blocksAt s.mem (D s₀) N = Spec.Cbc.blocksAt s₀.mem (D s₀) N :=
    blocksAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hp.data_scr.sub_left dS) (by have := hp.data_wrap; omega_using [hN, this])
  refine ⟨Inv.call hp h.inv t_sub (.inl dS) x, ?_, ?_, ?_⟩
  · rw [x.out, eW, h.t, eD]
  · rw [x.tw, h.t]
  · refine (h.frame.sub fun r hr => ?_).trans (x.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans t_sub tz_sub⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩

/-- `TwPost` across code that keeps the callee-saved registers and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.regs hp h.inv (fun r hr _ => hg r hr) hsp hm hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The epilogue -/

/-- The callee-saved registers and the return address restored. -/
def Restored (s₀ s' : State) : Prop := (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => Restored s₀ s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  rw [restore_eq, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s6) fun s₃ e => ?_
  subst e
  rw [h.s6]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := saveL) (B := sv s₀) (align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) h.saved) fun s₄ r₄ => ?_
  · show InRegions (s.rd ++ s.wr) _ 8
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (slot_contains s₀ _ (saved_bound p hp'))
  have g₀ (r : Reg) (hr : r ≠ .t0) : saveG s₀ r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨⟨fun r hr => ?_, ?_⟩, r₄.mem, r₄.rd, r₄.wr, r₄.sp⟩
  · have h0 : r ≠ .t0 := pres_ne hr (by decide)
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right
      rw [RegUpd.gpr_write_of_ne _ _ h0, h.rest r hr hv, g₀ r h0]
  · rw [r₄.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]

/-! ## Bytes of the data a call keeps -/

/-- The bytes of a part `X` of the data that a call on other blocks keeps. -/
theorem call_keeps {enc : Bool} {s s' : State} {Wk' T Dd : Addr} {N Rr : Nat} {X : Region}
    (hX : Region.Sub X (dataR s₀)) (hXD : X.Disjoint ⟨Dd, 16 * N⟩) (hT : Region.Sub ⟨T, 16⟩ (scrR s₀))
    (c : XPost enc s Wk' T Dd (Wk s₀) N Rr s') (hn : X.len ≤ 2 ^ 64) :
    bytesAt s'.mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.data_scr.sub_left hX).sub_right hT
    · exact hXD
    · exact (hp.data_scr.sub_left hX).sub_right wk_sub) hn

end

end VG.Proof.AesXts.RISCV64.Unit

end

end


/-!
# XTS-AES of data units on PPC64LE: encryption

As on PPC64LE (`Proof/AesXts/PPC64LE/Unit/Verified.lean`). `encrypt_wp`: the
tweak, the call on the whole blocks, and for a partial block the swap and
the call on the last whole block, then the epilogue. The data unit is
`encWith` of the cipher and the tweak, which is `aesXtsEncrypt` of any key
whose schedules are given (`unit_post`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesXts.RISCV64Unit
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- The data unit's result in a direction. -/
def withOf : Bool → Spec.Cbc.Cipher → List Byte → List Byte → List Byte
  | true => encWith
  | false => decWith

/-- What each branch leaves before the epilogue. -/
structure Fin (enc : Bool) (s₀ s : State) : Prop where
  inv : Inv s₀ s
  data : bytesAt s.mem (D s₀) (Len s₀) =
    withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))

/-- The memory of `AllPost`. -/
def AllMem (enc : Bool) (s₀ : State) (N : Nat) (m : Mem) : Prop :=
  Spec.Cbc.blocksAt m (D s₀) N = Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N) ∧
    bytesAt m (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N ∧ Frame [⟨D s₀, 16 * N⟩, scrR s₀] s₀.mem m

theorem AllPost.mem {enc : Bool} {s₀ : State} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    AllMem enc s₀ N s.mem :=
  ⟨h.out, h.tw, h.frame⟩

/-- Before a call on the first `N` whole blocks from the tweak. -/
structure BlocksReady (s₀ : State) (N : Nat) (s : State) : Prop where
  tw : TwPost s₀ s
  pre : XPre s (W s₀) (Tp s₀) (D s₀) (Wk s₀) N (R s₀)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem AllPost.keep {enc : Bool} {N : Nat} {s s' : State} (h : AllPost enc s₀ N s)
    (hg : ∀ r ∈ preserved, r ≠ .s3 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AllPost enc s₀ N s' where
  inv := Inv.regs hp h.inv hg hsp hm hrd hwr
  out := by rw [hm]; exact h.out
  tw := by rw [hm]; exact h.tw
  frame := by rw [hm]; exact h.frame

/-- After `split`, following the call on the whole blocks. -/
structure SplitPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  all : AllPost enc s₀ N s
  t1 : s.gpr .t1 = BitVec.ofNat 64 (16 * M s₀)
  t2 : s.gpr .t2 = BitVec.ofNat 64 (B s₀)

/-- `s4 + t1 − 16` is the last whole block. -/
theorem last_of {s : State} (h17 : s.gpr .s4 = D s₀) (h10 : s.gpr .t1 = BitVec.ofNat 64 (16 * M s₀)) :
    s.gpr .s4 + s.gpr .t1 - BitVec.ofNat 64 16 = L s₀ := by
  rw [h17, h10, last_eq _ hp.m_pos]

/-- Before the call on the last whole block, from the tweak at offset `o`:
the bytes after the whole blocks swapped with the last whole block's first. -/
structure LastReady (o : Nat) (s₀ s : State) (m : Mem) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (S s₀ + BitVec.ofNat 64 o) (L s₀) (Wk s₀) 1 (R s₀)
  mem : s.mem = swapMem m (L s₀) (B s₀)

/-- The swap, and the arguments of the call on the last whole block. -/
theorem steal_wp {o : Nat} (ho : o = tO ∨ o = zO) {s : State} (hi : Inv s₀ s)
    (h10 : s.gpr .t1 = BitVec.ofNat 64 (16 * M s₀)) (h11 : s.gpr .t2 = BitVec.ofNat 64 (B s₀))
    (h12 : s.gpr .t3 = L s₀) (hB : B s₀ ≠ 0) :
    WP isa (.seq swap (.block (argsL o))) s fun s' => LastReady o s₀ s' s.mem := by
  obtain hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain wr' : s.wr = [dataR s₀, scrR s₀] := by rw [hi.wr, hp.wr]
  refine WP.seq (WP.mono (swap_wp s (Nat.pos_of_ne_zero hB) hb h12 h11 (fun i hi' => by
      rw [wr']
      exact in_rw (r := dataR s₀) (by simp)
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega_using [hi']) (by omega_using [hb, hi'])))))
    fun s₂ ⟨mem₂, g₂, rd₂, wr₂, sp₂⟩ => ?_)
  refine WP.mono (argsL_wp' s₂ (o := o) (by rcases ho with rfl | rfl <;> decide))
    fun s₃ ⟨a0₃, a1₃, a2₃, a3₃, a4₃, a5₃, cs₃, mem₃, rd₃, wr₃, sp₃⟩ => ?_
  have k₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r :=
    g₂ r (pres_ne hr (by decide)) (pres_ne hr (by decide)) (pres_ne hr (by decide)) (pres_ne hr (by decide))
  obtain inv₂ : Inv s₀ s₂ := Inv.step hp hi (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, hp.lb_sub⟩)
    (by rw [mem₂]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) (fun r hr _ => k₂ r hr) sp₂ rd₂ wr₂
  obtain inv₃ : Inv s₀ s₃ := Inv.regs hp inv₂ (fun r hr _ => cs₃ r hr) sp₃ mem₃ rd₃ wr₃
  refine ⟨inv₃, xpre_last hp inv₃.rd inv₃.wr ho (by rw [a0₃, inv₂.s1])
    (by rw [a1₃, inv₂.s2, a2_ofNat]) (by rw [a2₃, inv₂.s6]) ?_ a4₃ (by rw [a5₃, inv₂.s6]),
    by rw [mem₃, mem₂]⟩
  rw [a3₃, g₂ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide)
    (by decide)]
  exact last_of hp hi.s4 h10

/-- The call on the last whole block, and the data unit's ciphertext. -/
theorem encLastCall_wp (ok : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nf : Impl.AesXts.RISCV64.encrypt.noFrames = true)
    {s : State} {m : Mem} (h : LastReady tO s₀ s m) (hm : AllMem true s₀ (M s₀) m) (hB : B s₀ ≠ 0) :
    WP isa encCall s (Fin true s₀) := by
  obtain hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨hout, htw, hfr⟩ := hm
  refine WP.mono (xts_call true ok nf h.pre) fun s₄ c => ?_
  obtain sw := Proof.AesXts.Unit.swapMem_frame m (L s₀) (B s₀)
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c, ?_⟩
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.enc_steal hp.m_pos (Nat.pos_of_ne_zero hB) hb hout ?_ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.tl_blocks
      · exact hp.data_scr.sub_left hp.tl_sub) (by omega_using [hb])
  · rw [Proof.AesXts.Unit.crypt_one_of c.out,
      hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp), h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left (sub_trans t_sub tz_sub)).sub_right hp.lb_sub) (by decide), htw]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) hp.hd_l
      (sub_trans t_sub tz_sub) c (by dsimp only; have := hp.wrapD; omega_using [this]), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l (sub_trans t_sub tz_sub) c
      (by dsimp only; omega_using [hb]), h.mem]

/-- The last whole block's address, after `split`. -/
theorem lastAddr_wp {s : State} (hi : Inv s₀ s) (h10 : s.gpr .t1 = BitVec.ofNat 64 (16 * M s₀)) :
    WP isa (.block lastAddr) s fun s' => s'.gpr .t3 = L s₀ ∧ (∀ r, r ≠ .t3 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (lastAddr_wp' s) fun _ ⟨t3, g, mem, rd, wr, sp⟩ =>
    ⟨by rw [t3]; exact last_of hp hi.s4 h10, g, sp, mem, rd, wr⟩

omit hp in
theorem keep_t3 {s s' : State} (hg : ∀ r, r ≠ .t3 → s'.gpr r = s.gpr r) :
    ∀ r ∈ preserved, r ≠ .s3 → s'.gpr r = s.gpr r :=
  fun r hr _ => hg r (pres_ne hr (by decide))

/-- Before the call on the last whole block of encryption: `Cₘ` and `PP`
swapped into place. -/
def EncLast (s₀ s : State) : Prop := ∃ m, AllMem true s₀ (M s₀) m ∧ LastReady tO s₀ s m

theorem encLast_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) s (EncLast s₀) := by
  refine WP.assoc' (WP.seq (WP.mono (lastAddr_wp hp h.all.inv h.t1) fun s₁ ⟨t3₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ => ?_))
  obtain h₁ := AllPost.keep hp h.all (keep_t3 g₁) sp₁ mem₁ rd₁ wr₁
  exact WP.mono (steal_wp hp (.inl rfl) h₁.inv (by rw [g₁ _ (by decide), h.t1])
    (by rw [g₁ _ (by decide), h.t2]) t3₁ hB) fun _ h₂ => ⟨_, h₁.mem, h₂⟩

/-- The steal of encryption: `Cₘ` and `PP` swapped into place, and `PP`
enciphered with the tweak of block `M`. -/
theorem encSteal_wp (ok : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nf : Impl.AesXts.RISCV64.encrypt.noFrames = true)
    {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa encSteal s (Fin true s₀) :=
  WP.assoc (WP.assoc (WP.seq (WP.mono (encLast_wp hp h hB) fun _ ⟨_, hm, h'⟩ =>
    encLastCall_wp hp ok nf h' hm hB)))

/-- The postcondition, from the bytes of the data unit. -/
theorem unit_post {enc : Bool} {s' : State}
    (hd : bytesAt s'.mem (D s₀) (Len s₀) = withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))) :
    (unitRISCV64 enc).post s₀ s' := by
  intro key hk
  obtain hk' := Proof.AesXts.Unit.keys_of (bytesAt s₀.mem (I s₀) 16) hk
  obtain hl : 16 ≤ (bytesAt s₀.mem (D s₀) (Len s₀)).length := by
    rw [Proof.AesXts.Unit.length_bytesAt]; exact hp.len_lo
  cases enc
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsDecrypt_eq hk' hl, hd]; rfl
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsEncrypt_eq hk' hl, hd]; rfl

omit hp in
/-- After `split`: the bytes of the whole blocks in `t1`, and the bytes
after them in `t2`. -/
theorem split_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block split) s fun s' => s'.gpr .t1 = BitVec.ofNat 64 (16 * M s₀) ∧
      s'.gpr .t2 = BitVec.ofNat 64 (B s₀) ∧ (∀ r, r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (split_wp' s) fun _ ⟨t1, t2, g, mem, rd, wr, sp⟩ =>
    ⟨by rw [t1, h.s5], by rw [t2, h.s5], g, sp, mem, rd, wr⟩

omit hp in
theorem keep_t1t2 {s s' : State} (hg : ∀ r, r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) :
    ∀ r ∈ preserved, r ≠ .s3 → s'.gpr r = s.gpr r :=
  fun r hr _ => hg r (pres_ne hr (by decide)) (pres_ne hr (by decide))

/-- The arguments of the call on the whole blocks. -/
theorem argsAll_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsAll) s (BlocksReady s₀ (M s₀)) :=
  WP.mono (argsAll_wp' s) fun s₂ ⟨r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, cs₂, mem₂, rd₂, wr₂, sp₂⟩ =>
    have h₂ := TwPost.keep hp h cs₂ sp₂ mem₂ rd₂ wr₂
    ⟨h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr (N := M s₀)
      (by rw [len_eq s₀]; omega_using []) (by rw [r3₂, h.inv.s1]) (by rw [r4₂, h.inv.s2, a2_ofNat])
      (by rw [r5₂, h.inv.s6]) (by rw [r6₂, h.inv.s4]) (by rw [r7₂, h.inv.s5]) (by rw [r8₂, h.inv.s6])⟩

theorem splitAll_wp {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    WP isa (.block split) s (SplitPost enc s₀ N) :=
  WP.mono (split_wp h.inv) fun _ ⟨t1, t2, g, sp, mem, rd, wr⟩ =>
    ⟨AllPost.keep hp h (keep_t1t2 g) sp mem rd wr, t1, t2⟩

omit hp in
/-- The data unit of whole blocks, after the call on all of them. -/
theorem whole_fin {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s := by
  refine ⟨h.inv, ?_⟩
  rw [show Len s₀ = 16 * M s₀ by rw [len_eq s₀, hb, Nat.add_zero]]
  cases enc
  · exact Proof.AesXts.Unit.dec_whole h.out
  · exact Proof.AesXts.Unit.enc_whole h.out

omit hp in
theorem eval_b {s : State} (h : s.gpr .t2 = BitVec.ofNat 64 (B s₀)) :
    isa.eval (.zero .t2) s = some (decide (B s₀ = 0)) :=
  eval_zero_ofNat s .t2 (by have : B s₀ < 16 := Nat.mod_lt _ (by decide); omega_using [this]) h

theorem encrypt_wp (ok : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nf : Impl.AesXts.RISCV64.encrypt.noFrames = true) :
    WP isa Impl.AesXts.RISCV64Unit.encrypt s₀ fun s' => Restored s₀ s' ∧ (unitRISCV64 true).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp ok nf) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (argsAll_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (blocks_call hp true ok nf (by rw [len_eq s₀]; omega_using []) h₂.tw h₂.pre) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (splitAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b h₄.t2)
    (fun hb => WP.block_nil (whole_fin h₄.all (by simpa using hb)))
    (fun hb => encSteal_wp hp ok nf h₄ (by simpa using hb))) fun s₅ h₅ => ?_)
  exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m, _⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.RISCV64.Unit

end

end

/-!
# XTS-AES of data units on PPC64LE: decryption

As on PPC64LE (`Proof/AesXts/PPC64LE/Unit/Verified.lean`). `decrypt_wp`: the
tweak, then without a partial block the call on the whole blocks; with one,
the call on all but the last whole block, the tweak of block `M` (`nextT`),
the call on the last whole block from it, the swap, and the call on the
last whole block from the tweak of block `M - 1`; then the epilogue.
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesXts.RISCV64Unit
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- A callee-saved register is none that `mulA` writes. -/
theorem pres_not_mul {r : Reg} (hr : r ∈ preserved) : r ∉ AesXts.RISCV64.mulRegs := by
  revert hr; cases r <;> decide

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- Before the call on the last whole block from the tweak of block `M`,
which is at `zO`. -/
structure DecL1 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Zp s₀) (L s₀) (Wk s₀) 1 (R s₀)
  mem : ∃ m, AllMem false s₀ (M s₀ - 1) m ∧ Frame [⟨Zp s₀, 16⟩] m s.mem ∧
    bytesAt s.mem (Zp s₀) 16 = Spec.Xts.mulAlpha (bytesAt m (Tp s₀) 16)

/-- The memory after the call on the last whole block from the tweak of
block `M`: `PP` there, from the memory `m` after the first `M - 1` blocks. -/
def DecMem (s₀ : State) (m₅ : Mem) : Prop :=
  ∃ m, AllMem false s₀ (M s₀ - 1) m ∧
    bytesAt m₅ (L s₀) 16 = Spec.Xts.block (ciph s₀ false) (Spec.Xts.next (t0 s₀) (M s₀)) (bytesAt m (L s₀) 16) ∧
    bytesAt m₅ (D s₀) (16 * (M s₀ - 1)) = bytesAt m (D s₀) (16 * (M s₀ - 1)) ∧
    bytesAt m₅ (L s₀ + 16) (B s₀) = bytesAt m (L s₀ + 16) (B s₀) ∧
    bytesAt m₅ (Tp s₀) 16 = Spec.Xts.next (t0 s₀) (M s₀ - 1)

/-- After the call on the last whole block from the tweak of block `M`. -/
structure DecL2 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  mem : DecMem s₀ s.mem

/-- The arguments of the call on all but the last whole block. -/
theorem argsHead_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsHead) s (BlocksReady s₀ (M s₀ - 1)) := by
  have hm := hp.m_pos
  refine WP.mono (argsHead_wp' s (by rw [h.inv.s5]; exact hm))
    fun s₁ ⟨r3₁, r4₁, r5₁, r6₁, r7₁, r8₁, cs₁, mem₁, rd₁, wr₁, sp₁⟩ => ?_
  have h₁ := TwPost.keep hp h cs₁ sp₁ mem₁ rd₁ wr₁
  exact ⟨h₁, xpre_blocks hp h₁.inv.rd h₁.inv.wr (N := M s₀ - 1)
    (by rw [len_eq s₀]; omega_using []) (by rw [r3₁, h.inv.s1]) (by rw [r4₁, h.inv.s2, a2_ofNat])
    (by rw [r5₁, h.inv.s6]) (by rw [r6₁, h.inv.s4]) (by rw [r7₁, h.inv.s5]) (by rw [r8₁, h.inv.s6])⟩

/-- The tweak of block `M`, at `zO`, and the arguments of the call on the
last whole block from it. -/
theorem decL1_wp {s₂ : State} (h₂ : AllPost false s₀ (M s₀ - 1) s₂) :
    WP isa (.block (nextT ++ split ++ argsL zO)) s₂ (DecL1 s₀) := by
  have wr₂ : s₂.wr = [dataR s₀, scrR s₀] := by rw [h₂.inv.wr, hp.wr]
  have rdwr₂ : s₂.rd ++ s₂.wr = [schR s₀, tschR s₀, iR s₀, dataR s₀, scrR s₀] := by
    rw [h₂.inv.rd, h₂.inv.wr, hp.rd, hp.wr]; rfl
  have inS (d n : Nat) (i : Nat) (h : d + i + n ≤ 2432) :
      (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 d + BitVec.ofNat 64 i) n := by
    rw [Offset.add_add]; exact cS s₀ _ _ h
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (nextT_wp s₂ (T := Tp s₀) (Z := Zp s₀) (by rw [h₂.inv.s6]) (by rw [h₂.inv.s6])
    hp.t_z.symm
    (fun i hi => by rw [rdwr₂]; exact in_rw (r := scrR s₀) (by simp) (inS _ _ _ (by simp [tO]; omega_using [hi])))
    (fun i hi => by rw [wr₂]; exact in_rw (r := scrR s₀) (by simp) (inS _ _ _ (by simp [zO]; omega_using [hi])))
    (fun d hd => by rw [rdwr₂]; exact in_rw (r := scrR s₀) (by simp) (inS _ _ _ (by simp [zO]; omega_using [hd])))
    (fun d hd => by rw [wr₂]; exact in_rw (r := scrR s₀) (by simp) (inS _ _ _ (by simp [zO]; omega_using [hd]))))
    fun s₃ ⟨g₃, _, f₃, z₃, rd₃, wr₃, sp₃⟩ => ?_
  have inv₃ : Inv s₀ s₃ := Inv.step hp h₂.inv (rs := [⟨Zp s₀, 16⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨tzR s₀, by simp, z_sub⟩) f₃
    (fun r hr h3 => g₃ r (pres_not_mul hr) h3) sp₃ rd₃ wr₃
  rw [WP.block_append_iff]
  refine WP.mono (split_wp inv₃) fun s₄ ⟨t1₄, _, g₄, sp₄, mem₄, rd₄, wr₄⟩ => ?_
  refine WP.mono (argsL_wp' s₄ (o := zO) (by decide))
    fun s₆ ⟨r3₆, r4₆, r5₆, r6₆, r7₆, r8₆, cs₆, mem₆, rd₆, wr₆, sp₆⟩ => ?_
  have inv₄ : Inv s₀ s₄ := Inv.regs hp inv₃ (keep_t1t2 g₄) sp₄ mem₄ rd₄ wr₄
  have inv₆ : Inv s₀ s₆ := Inv.regs hp inv₄ (fun r hr _ => cs₆ r hr) sp₆ mem₆ rd₆ wr₆
  have m₆ : s₆.mem = s₃.mem := by rw [mem₆, mem₄]
  refine ⟨inv₆, xpre_last hp inv₆.rd inv₆.wr (.inr rfl) (by rw [r3₆, inv₄.s1])
    (by rw [r4₆, inv₄.s2, a2_ofNat]) (by rw [r5₆, inv₄.s6]) (by rw [r6₆]; exact last_of hp inv₄.s4 t1₄) r7₆
    (by rw [r8₆, inv₄.s6]),
    ⟨s₂.mem, h₂.mem, by rw [m₆]; exact f₃, by rw [m₆]; exact z₃⟩⟩

/-- The call on the last whole block from the tweak of block `M`. -/
theorem decL2_wp (ok : XtsOk false Impl.AesXts.RISCV64.decrypt)
    (nf : Impl.AesXts.RISCV64.decrypt.noFrames = true) {s : State} (h : DecL1 s₀ s) :
    WP isa decCall s (DecL2 s₀) := by
  have hm := hp.m_pos
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨m, ⟨hout, htw, hfr⟩, f₃, z₃⟩ := h.mem
  refine WP.mono (xts_call false ok nf h.pre) fun s₇ c₇ => ?_
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub tz_sub
  have zL : Region.Sub ⟨Zp s₀, 16⟩ (scrR s₀) := sub_trans z_sub tz_sub
  have eW := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  refine ⟨Inv.call hp h.inv z_sub (.inl hp.l_sub) c₇, m, ⟨hout, htw, hfr⟩, ?_, ?_, ?_, ?_⟩
  · rw [Proof.AesXts.Unit.crypt_one_of c₇.out, eW, z₃, htw, ← Proof.AesXts.next_succ,
      Nat.sub_add_cancel hm,
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.sub_left hp.l_sub).sub_right zL) (by decide)]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) hp.hd_l zL c₇
      (by dsimp only; have := hp.wrapD; omega_using [this])]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (blocks_sub (by omega_using []))).sub_right zL) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l zL c₇ (by dsimp only; omega_using [hb])]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left hp.tl_sub).sub_right zL) (by dsimp only; omega_using [hb])
  · rw [Proof.Cmac.bytesAt_frame c₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.t_z
        · exact (hp.data_scr.symm.sub_left tL).sub_right hp.l_sub
        · exact hp.t_wk) (by decide),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), htw]

/-- The call on the last whole block from the tweak of block `M - 1`, and
the data unit's plaintext. -/
theorem decLast_wp (ok : XtsOk false Impl.AesXts.RISCV64.decrypt)
    (nf : Impl.AesXts.RISCV64.decrypt.noFrames = true)
    {s : State} {m₅ : Mem} (h : LastReady tO s₀ s m₅) (hm₅ : DecMem s₀ m₅) (hB : B s₀ ≠ 0) :
    WP isa decCall s (Fin false s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have hm := hp.m_pos
  obtain ⟨m, ⟨hout, htw, hfr⟩, h5L, h5H, h5T, tw₅⟩ := hm₅
  refine WP.mono (xts_call false ok nf h.pre) fun s₁₂ c₁₂ => ?_
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c₁₂, ?_⟩
  have sw := Proof.AesXts.Unit.swapMem_frame m₅ (L s₀) (B s₀)
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub tz_sub
  have eW' := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.dec_steal (m₃ := m) (m₅ := m₅) hm (Nat.pos_of_ne_zero hB) hb hout
    ⟨?_, ?_⟩ ⟨h5L, h5H, h5T⟩ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.l_hd
      · exact hp.data_scr.sub_left hp.l_sub) (by decide)
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.hd_tl.symm
      · exact hp.data_scr.sub_left hp.tl_sub) (by omega_using [hb])
  · rw [Proof.AesXts.Unit.crypt_one_of c₁₂.out, eW', h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left tL).sub_right hp.lb_sub) (by decide), tw₅]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) hp.hd_l tL c₁₂
      (by dsimp only; have := hp.wrapD; omega_using [this]), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l tL c₁₂ (by dsimp only; omega_using [hb]), h.mem]

/-- Before the call on the last whole block from the tweak of block `M - 1`:
`Pₘ` and `CC` swapped into place. -/
def DecL3 (s₀ s : State) : Prop := ∃ m₅, DecMem s₀ m₅ ∧ LastReady tO s₀ s m₅

/-- The swap, after the call from the tweak of block `M`. -/
theorem decL3_wp {s : State} (h : DecL2 s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block (split ++ lastAddr)) swap) (.block (argsL tO))) s (DecL3 s₀) := by
  refine WP.assoc' (WP.seq ?_)
  rw [WP.block_append_iff]
  refine WP.mono (split_wp h.inv) fun s₈ ⟨t1₈, t2₈, g₈, sp₈, mem₈, rd₈, wr₈⟩ => ?_
  have inv₈ : Inv s₀ s₈ := Inv.regs hp h.inv (keep_t1t2 g₈) sp₈ mem₈ rd₈ wr₈
  refine WP.mono (lastAddr_wp hp inv₈ t1₈) fun s₉ ⟨t3₉, g₉, sp₉, mem₉, rd₉, wr₉⟩ => ?_
  have inv₉ : Inv s₀ s₉ := Inv.regs hp inv₈ (keep_t3 g₉) sp₉ mem₉ rd₉ wr₉
  exact WP.mono (steal_wp hp (.inl rfl) inv₉ (by rw [g₉ _ (by decide), t1₈])
    (by rw [g₉ _ (by decide), t2₈]) t3₉ hB) fun _ h₂ => ⟨_, by rw [mem₉, mem₈]; exact h.mem, h₂⟩

/-- The steal of decryption, after the tweak. -/
theorem decSteal_wp (ok : XtsOk false Impl.AesXts.RISCV64.decrypt)
    (nf : Impl.AesXts.RISCV64.decrypt.noFrames = true)
    {s : State} (h : TwPost s₀ s) (hB : B s₀ ≠ 0) :
    WP isa decSteal s (Fin false s₀) := by
  refine WP.seq (WP.mono (argsHead_wp hp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blocks_call hp false ok nf (by rw [len_eq s₀]; omega_using []) h₁.tw h₁.pre) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (decL1_wp hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (decL2_wp hp ok nf h₃) fun s₄ h₄ => ?_)
  exact WP.assoc (WP.assoc (WP.seq (WP.mono (decL3_wp hp h₄ hB) fun _ ⟨_, hm, h'⟩ => decLast_wp hp ok nf h' hm hB)))

theorem split_tw_wp {s : State} (h : TwPost s₀ s) :
    WP isa (.block split) s fun s' => TwPost s₀ s' ∧ s'.gpr .t2 = BitVec.ofNat 64 (B s₀) :=
  WP.mono (split_wp h.inv) fun _ ⟨_, t2₂, g₂, sp₂, mem₂, rd₂, wr₂⟩ =>
    ⟨TwPost.keep hp h (fun r hr => g₂ r (pres_ne hr (by decide)) (pres_ne hr (by decide))) sp₂ mem₂ rd₂ wr₂,
      t2₂⟩

theorem decrypt_wp (okE : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nfE : Impl.AesXts.RISCV64.encrypt.noFrames = true)
    (okD : XtsOk false Impl.AesXts.RISCV64.decrypt) (nfD : Impl.AesXts.RISCV64.decrypt.noFrames = true) :
    WP isa Impl.AesXts.RISCV64Unit.decrypt s₀ fun s' => Restored s₀ s' ∧ (unitRISCV64 false).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp okE nfE) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (split_tw_wp hp h₁) fun s₂ ⟨h₂, t2₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b t2₂) (fun hb => ?_)
    (fun hb => decSteal_wp hp okD nfD h₂ (by simpa using hb))) fun s₅ h₅ => ?_)
  · refine WP.seq (WP.mono (argsAll_wp hp h₂) fun s₃ h₃ => ?_)
    exact WP.mono (blocks_call hp false okD nfD (by rw [len_eq s₀]; omega_using []) h₃.tw h₃.pre)
      fun s₄ h₄ => whole_fin h₄ (by simpa using hb)
  · exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m, _⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.RISCV64.Unit

end

end

/-!
# XTS-AES of data units on PPC64LE: constant time

As on PPC64LE (`Proof/AesXts/PPC64LE/Unit/Verified.lean`): two runs from states
that agree on the public arguments are related piece by piece (`RelCT`),
from the correctness proof's states between the pieces: the taint analysis
covers the code between the calls (the swap's loop with them), from the
registers the states pin to public values (`Inv.agree`), each call is
constant time by its callee's proof (`xcall_rel`), and the one branch, on
whether there is a partial block, agrees in both runs.
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.Impl.AesXts.RISCV64Unit
open VG.Proof.AesCbc.RISCV64 (modeRISCV64)

/-- A piece of code the taint analysis checks from the registers `rs`, which
agree in two runs (as do the stack pointers), with what each run reaches. -/
theorem taint_rel {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop} (rs : List Reg)
    (ht : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true)
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp) (ha : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ F₁ ∧ WP isa c s₂ F₂) :
    RelCT isa P c fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ := by
  obtain ⟨_, ht⟩ := ht
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun x y hp => ⟨hsp x y hp, fun r h' => ha x y hp r (Taint.mem_ofRegs.mp h')⟩) ht).wp hw).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- A whole-block function, constant time. -/
abbrev XtsCt (enc : Bool) (c : Prog isa) : Prop :=
  ConstantTime isa (modeRISCV64 (AesXts.xtsMode enc)).pre (modeRISCV64 (AesXts.xtsMode enc)).pub c

/-- A call of a whole-block function, with the same arguments in both runs,
and what each run leaves. -/
theorem xcall_rel (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c) (ct : XtsCt enc c)
    {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hx : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : Addr, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.sp = s₂.sp)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa (.call n c) s₁ F₁ ∧ WP isa (.call n c) s₂ F₂) :
    RelCT isa P (.call n c) fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ :=
  ((xts_rel enc ok ct hx).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The registers the states pin to public values. -/
abbrev pubRegs : List Reg := [.s1, .s2, .s4, .s5, .s6]

section
variable {s₀ s₀' : State} (hq : unitPub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_K : K s₀ = K s₀' := hq.2.1
theorem pub_a2 : s₀.gpr .a2 = s₀'.gpr .a2 := hq.2.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_a2 hq]
theorem pub_D : D s₀ = D s₀' := hq.2.2.2.2.1
theorem pub_a5 : s₀.gpr .a5 = s₀'.gpr .a5 := hq.2.2.2.2.2.1
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2.2
theorem pub_M : M s₀ = M s₀' := by rw [M, M, Len, Len, pub_a5 hq]
theorem pub_B : B s₀ = B s₀' := by rw [B, B, Len, Len, pub_a5 hq]
theorem pub_L : L s₀ = L s₀' := by rw [L, L, pub_D hq, pub_M hq]
theorem pub_Tp : Tp s₀ = Tp s₀' := by simp only [Tp, pub_S hq]
theorem pub_Zp : Zp s₀ = Zp s₀' := by simp only [Zp, pub_S hq]
theorem pub_Wk : Wk s₀ = Wk s₀' := by simp only [Wk, pub_S hq]

theorem Inv.agree {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : ∀ r ∈ pubRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.s1, h₂.s1, pub_W hq]
  · rw [h₁.s2, h₂.s2, pub_a2 hq]
  · rw [h₁.s4, h₂.s4, pub_D hq]
  · rw [h₁.s5, h₂.s5, pub_a5 hq]
  · rw [h₁.s6, h₂.s6, pub_S hq]

theorem Inv.sp_eq {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : s₁.sp = s₂.sp := by
  rw [h₁.sp, h₂.sp, pub_sp hq]

omit hq in
/-- Agreement on the public registers and more. -/
theorem agree_cons {s₁ s₂ : State} {rs : List Reg} (h : ∀ r ∈ pubRegs, s₁.gpr r = s₂.gpr r)
    (h' : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : ∀ r ∈ rs ++ pubRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h' r hr
  · exact h r hr

end

/-! ## Taint checks -/

theorem pro_taint : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6])
    (.block pro) h).isSome = true := ⟨_, by taint_decide⟩

theorem argsAll_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block argsAll) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem argsHead_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block argsHead) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem split_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block split) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encLast_taint : ∃ h, (taint.check (Taint.ofRegs (([.t1, .t2] : List Reg) ++ pubRegs))
    (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL1_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs)
    (.block (nextT ++ split ++ argsL zO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL3_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs)
    (.seq (.seq (.block (split ++ lastAddr)) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.s6]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## The two runs -/

section
variable {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : unitPub s₀ s₀')
include hp hp' hq

theorem tweak_rel (ok : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nf : Impl.AesXts.RISCV64.encrypt.noFrames = true) (ct : XtsCt true Impl.AesXts.RISCV64.encrypt) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') tweak fun a b => TwPost s₀ a ∧ TwPost s₀' b := by
  have p := taint_rel [.a0, .a1, .a2, .a3, .a4, .a5, .a6] pro_taint (P := fun a b => a = s₀ ∧ b = s₀')
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact pub_sp hq)
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      have hq' := hq
      obtain ⟨h3, h4, h5, h6, h7, h8, h9, _⟩ := hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7
      · exact h8
      · exact h9)
    (F₁ := ProPost s₀) (F₂ := ProPost s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨pro_wp hp, pro_wp hp'⟩
  have c := xcall_rel true ok ct (n := "vg_aes_xts_encrypt") (P := fun a b => ProPost s₀ a ∧ ProPost s₀' b)
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_K hq, pub_Zp hq, pub_Tp hq, pub_Wk hq, pub_R hq]; exact h.2.pre, Inv.sp_eq hq h.1.inv h.2.inv⟩)
    (F₁ := TwPost s₀) (F₂ := TwPost s₀')
    (fun a b h => ⟨tcall_wp hp ok nf h.1, tcall_wp hp' ok nf h.2⟩)
  exact p.seq c

theorem blocks_rel (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c) (ct : XtsCt enc c)
    (nf : c.noFrames = true) {N N' : Nat} (hN : 16 * N ≤ Len s₀) (hN' : 16 * N' ≤ Len s₀')
    (hNN : N = N') :
    RelCT isa (fun a b => BlocksReady s₀ N a ∧ BlocksReady s₀' N' b) (.call n c)
      fun a b => AllPost enc s₀ N a ∧ AllPost enc s₀' N' b :=
  xcall_rel enc ok ct
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_W hq, pub_Tp hq, pub_D hq, pub_Wk hq, hNN, pub_R hq]; exact h.2.pre,
      Inv.sp_eq hq h.1.tw.inv h.2.tw.inv⟩)
    fun a b h => ⟨blocks_call hp enc ok nf hN h.1.tw h.1.pre, blocks_call hp' enc ok nf hN' h.2.tw h.2.pre⟩

theorem restore_rel {enc : Bool} :
    RelCT isa (fun a b => Fin enc s₀ a ∧ Fin enc s₀' b) (.block restore) fun _ _ => True :=
  (taint_rel [.s6] restore_taint (P := fun a b => Fin enc s₀ a ∧ Fin enc s₀' b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.inv.s6, h.2.inv.s6, pub_S hq])
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    fun a b h => ⟨WP.mono (fin_wp hp h.1.inv) fun _ _ => trivial, WP.mono (fin_wp hp' h.2.inv) fun _ _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

omit hp hp' in
theorem eval_eq {s₁ s₂ : State} (h₁ : s₁.gpr .t2 = BitVec.ofNat 64 (B s₀))
    (h₂ : s₂.gpr .t2 = BitVec.ofNat 64 (B s₀')) : isa.eval (.zero .t2) s₁ = isa.eval (.zero .t2) s₂ := by
  rw [eval_b h₁, eval_b h₂, pub_B hq]

theorem encrypt_rel (ok : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nf : Impl.AesXts.RISCV64.encrypt.noFrames = true) (ct : XtsCt true Impl.AesXts.RISCV64.encrypt) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') Impl.AesXts.RISCV64Unit.encrypt fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq ok nf ct
  have a := taint_rel pubRegs argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀)) (F₂ := BlocksReady s₀' (M s₀'))
    fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
  have c := blocks_rel hp hp' hq true ok ct nf (by rw [len_eq s₀]; omega_using []) (by rw [len_eq s₀']; omega_using []) hM
    (n := "vg_aes_xts_encrypt")
  have sp := taint_rel pubRegs split_taint (P := fun a b => AllPost true s₀ (M s₀) a ∧ AllPost true s₀' (M s₀') b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := SplitPost true s₀ (M s₀))
    (F₂ := SplitPost true s₀' (M s₀')) fun a b h => ⟨splitAll_wp hp h.1, splitAll_wp hp' h.2⟩
  have br : RelCT isa (fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
      (.ite (.zero .t2) (.block []) encSteal) fun a b => Fin true s₀ a ∧ Fin true s₀' b := by
    refine RelCT.ite (fun a b h => eval_eq hq h.1.t2 h.2.t2) ?_ ?_
    · refine RelCT.block_nil fun a b h => ?_
      have hb : B s₀ = 0 := by
        have := h.2; rw [eval_b h.1.1.t2] at this; simpa using this
      exact ⟨whole_fin h.1.1.all hb, whole_fin h.1.2.all (by rw [← pub_B hq]; exact hb)⟩
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b =>
          SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.t2] at this; simpa using this, h.1⟩)
        fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      refine RelCT.assoc (RelCT.assoc ?_)
      have l := taint_rel ([.t1, .t2] ++ pubRegs) encLast_taint
        (P := fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
        (fun a b h => Inv.sp_eq hq h.1.all.inv h.2.all.inv)
        (fun a b h => agree_cons (Inv.agree hq h.1.all.inv h.2.all.inv) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.t1, h.2.t1, hM]
          · rw [h.1.t2, h.2.t2, pub_B hq])
        (F₁ := EncLast s₀) (F₂ := EncLast s₀') fun a b h => ⟨encLast_wp hp h.1 hB, encLast_wp hp' h.2 hB'⟩
      have c := xcall_rel true ok ct (n := "vg_aes_xts_encrypt") (P := fun a b => EncLast s₀ a ∧ EncLast s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.choose_spec.2.pre, by
          rw [pub_W hq, pub_L hq, pub_Wk hq, pub_R hq, pub_S hq]; exact h.2.choose_spec.2.pre,
          Inv.sp_eq hq h.1.choose_spec.2.inv h.2.choose_spec.2.inv⟩)
        (F₁ := Fin true s₀) (F₂ := Fin true s₀')
        fun a b h => ⟨encLastCall_wp hp ok nf h.1.choose_spec.2 h.1.choose_spec.1 hB,
          encLastCall_wp hp' ok nf h.2.choose_spec.2 h.2.choose_spec.1 hB'⟩
      exact l.seq c
  exact t.seq (a.seq (c.seq (sp.seq (br.seq (restore_rel hp hp' hq)))))

theorem decrypt_rel (okE : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nfE : Impl.AesXts.RISCV64.encrypt.noFrames = true) (ctE : XtsCt true Impl.AesXts.RISCV64.encrypt)
    (okD : XtsOk false Impl.AesXts.RISCV64.decrypt) (nfD : Impl.AesXts.RISCV64.decrypt.noFrames = true)
    (ctD : XtsCt false Impl.AesXts.RISCV64.decrypt) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') Impl.AesXts.RISCV64Unit.decrypt fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq okE nfE ctE
  have sp := taint_rel pubRegs split_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv)
    (F₁ := fun s => TwPost s₀ s ∧ s.gpr .t2 = BitVec.ofNat 64 (B s₀))
    (F₂ := fun s => TwPost s₀' s ∧ s.gpr .t2 = BitVec.ofNat 64 (B s₀'))
    fun a b h => ⟨split_tw_wp hp h.1, split_tw_wp hp' h.2⟩
  have br : RelCT isa (fun a b => (TwPost s₀ a ∧ a.gpr .t2 = BitVec.ofNat 64 (B s₀)) ∧
      (TwPost s₀' b ∧ b.gpr .t2 = BitVec.ofNat 64 (B s₀')))
      (.ite (.zero .t2) (.seq (.block argsAll) decCall) decSteal)
      fun a b => Fin false s₀ a ∧ Fin false s₀' b := by
    refine RelCT.ite (fun a b h => eval_eq hq h.1.2 h.2.2) ?_ ?_
    · refine (RelCT.exists_ (P := fun (_ : B s₀ = 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hb => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hb' : B s₀' = 0 := by rw [← pub_B hq]; exact hb
      have a := taint_rel pubRegs argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀))
        (F₂ := BlocksReady s₀' (M s₀')) fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
      have c := blocks_rel hp hp' hq false okD ctD nfD (by rw [len_eq s₀]; omega_using [])
        (by rw [len_eq s₀']; omega_using []) hM (n := "vg_aes_xts_decrypt")
      exact a.seq (c.mono (fun _ _ h => h) fun _ _ h => ⟨whole_fin h.1 hb, whole_fin h.2 hb'⟩)
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      have a := taint_rel pubRegs argsHead_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀ - 1))
        (F₂ := BlocksReady s₀' (M s₀' - 1)) fun a b h => ⟨argsHead_wp hp h.1, argsHead_wp hp' h.2⟩
      have c₁ := blocks_rel hp hp' hq false okD ctD nfD (N := M s₀ - 1)
        (N' := M s₀' - 1) (by rw [len_eq s₀]; omega_using []) (by rw [len_eq s₀']; omega_using []) (by rw [hM])
        (n := "vg_aes_xts_decrypt")
      have l₁ := taint_rel pubRegs decL1_taint
        (P := fun a b => AllPost false s₀ (M s₀ - 1) a ∧ AllPost false s₀' (M s₀' - 1) b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL1 s₀) (F₂ := DecL1 s₀')
        fun a b h => ⟨decL1_wp hp h.1, decL1_wp hp' h.2⟩
      have c₂ := xcall_rel false okD ctD (n := "vg_aes_xts_decrypt") (P := fun a b => DecL1 s₀ a ∧ DecL1 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Zp hq, pub_L hq, pub_Wk hq, pub_R hq]; exact h.2.pre,
          Inv.sp_eq hq h.1.inv h.2.inv⟩)
        (F₁ := DecL2 s₀) (F₂ := DecL2 s₀') fun a b h => ⟨decL2_wp hp okD nfD h.1, decL2_wp hp' okD nfD h.2⟩
      have l₃ := taint_rel pubRegs decL3_taint (P := fun a b => DecL2 s₀ a ∧ DecL2 s₀' b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL3 s₀) (F₂ := DecL3 s₀')
        fun a b h => ⟨decL3_wp hp h.1 hB, decL3_wp hp' h.2 hB'⟩
      have c₃ := xcall_rel false okD ctD (n := "vg_aes_xts_decrypt") (P := fun a b => DecL3 s₀ a ∧ DecL3 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.choose_spec.2.pre, by
          rw [pub_W hq, pub_L hq, pub_Wk hq, pub_R hq, pub_S hq]; exact h.2.choose_spec.2.pre,
          Inv.sp_eq hq h.1.choose_spec.2.inv h.2.choose_spec.2.inv⟩)
        (F₁ := Fin false s₀) (F₂ := Fin false s₀')
        fun a b h => ⟨decLast_wp hp okD nfD h.1.choose_spec.2 h.1.choose_spec.1 hB,
          decLast_wp hp' okD nfD h.2.choose_spec.2 h.2.choose_spec.1 hB'⟩
      exact a.seq (c₁.seq (l₁.seq (c₂.seq (RelCT.assoc (RelCT.assoc (l₃.seq c₃))))))
  exact t.seq (sp.seq (br.seq (restore_rel hp hp' hq)))

end

theorem encrypt_ct (ok : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nf : Impl.AesXts.RISCV64.encrypt.noFrames = true) (ct : XtsCt true Impl.AesXts.RISCV64.encrypt) :
    ConstantTime isa (unitRISCV64 true).pre (unitRISCV64 true).pub Impl.AesXts.RISCV64Unit.encrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel (UPre.of h₁) (UPre.of h₂) hq ok nf ct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decrypt_ct (okE : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nfE : Impl.AesXts.RISCV64.encrypt.noFrames = true) (ctE : XtsCt true Impl.AesXts.RISCV64.encrypt)
    (okD : XtsOk false Impl.AesXts.RISCV64.decrypt) (nfD : Impl.AesXts.RISCV64.decrypt.noFrames = true)
    (ctD : XtsCt false Impl.AesXts.RISCV64.decrypt) :
    ConstantTime isa (unitRISCV64 false).pre (unitRISCV64 false).pub Impl.AesXts.RISCV64Unit.decrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel (UPre.of h₁) (UPre.of h₂) hq okE nfE ctE okD nfD ctD _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.RISCV64.Unit

end

end

/-!
# XTS-AES of data units on RISC-V: `Verified`

`vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit` meet `unitRISCV64`
(`encrypt_wp`, `decrypt_wp`, `encrypt_ct`, `decrypt_ct`), from the
whole-block functions' proofs (`Proof/AesXts/RISCV64/Verified.lean`), and
so the shared contracts of `Spec/Xts/Contract.lean`, as on PPC64LE
(`Proof/AesXts/PPC64LE/Unit/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.Impl.AesXts.RISCV64Unit

theorem encrypt_correct (s : State) (hs : (unitRISCV64 true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (unitRISCV64 true).post s s' := by
  obtain ⟨t, s', he, ⟨hg, hra⟩, hp⟩ := encrypt_wp (UPre.of hs) Proof.AesXts.RISCV64.encrypt_correct
    Proof.AesXts.RISCV64.encrypt_noFrames
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (unitRISCV64 false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (unitRISCV64 false).post s s' := by
  obtain ⟨t, s', he, ⟨hg, hra⟩, hp⟩ := decrypt_wp (UPre.of hs) Proof.AesXts.RISCV64.encrypt_correct
    Proof.AesXts.RISCV64.encrypt_noFrames Proof.AesXts.RISCV64.decrypt_correct
    Proof.AesXts.RISCV64.decrypt_noFrames
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

/-- A state satisfying the precondition: AES-128, a data unit of one block
at `0x4000`, and the scratch buffer at `0x5000`. -/
def unitSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 10 | .a3 => 0x3000 | .a4 => 0x4000 | .a5 => 16 | .a6 => 0x5000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x4000, 16⟩, ⟨0x5000, 2432⟩]

theorem encrypt_verified : Verified RISCV64.target encrypt (Spec.Xts.aesEncryptUnitContract RISCV64.abi) :=
  Verified.of_correct encrypt_correct
    (encrypt_ct Proof.AesXts.RISCV64.encrypt_correct Proof.AesXts.RISCV64.encrypt_noFrames
      Proof.AesXts.RISCV64.encrypt_ct) (by
    sig_implies [Spec.Xts.aesEncryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesEncryptUnitPost, unitRISCV64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, RISCV64.abi, RISCV64.argRegs] [unitSat] using unitSat)

theorem decrypt_verified : Verified RISCV64.target decrypt (Spec.Xts.aesDecryptUnitContract RISCV64.abi) :=
  Verified.of_correct decrypt_correct
    (decrypt_ct Proof.AesXts.RISCV64.encrypt_correct Proof.AesXts.RISCV64.encrypt_noFrames
      Proof.AesXts.RISCV64.encrypt_ct Proof.AesXts.RISCV64.decrypt_correct Proof.AesXts.RISCV64.decrypt_noFrames
      Proof.AesXts.RISCV64.decrypt_ct) (by
    sig_implies [Spec.Xts.aesDecryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesDecryptUnitPost, unitRISCV64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, RISCV64.abi, RISCV64.argRegs] [unitSat] using unitSat)

end VG.Proof.AesXts.RISCV64.Unit
