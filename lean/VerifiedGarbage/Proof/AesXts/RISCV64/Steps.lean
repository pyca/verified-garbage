module

public import VerifiedGarbage.Impl.AesXts.RISCV64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Xts
import VerifiedGarbage.Proof.AesXts.Alpha
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop

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
  rw [Nat.mod_eq_of_lt (a := w.toNat) (by omega), Nat.mod_mod_of_dvd _ (by decide)]

/-- The top bit of a zero-extended word, as a bit. -/
theorem ushr31 (w : BitVec 32) : (w.setWidth 64) >>> 31 = if w.msb then (1 : BitVec 64) else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, BitVec.msb_eq_decide]
  have := w.isLt
  rw [Nat.mod_eq_of_lt (by omega)]
  by_cases h : 2 ^ 31 ≤ w.toNat
  · rw [decide_eq_true h]; show _ = 1; omega
  · rw [decide_eq_false h]; show _ = 0; omega

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
  have v₃ : s₃.gpr .a6 = ((x.setWidth 64) <<< 1) ||| ((y.setWidth 64) >>> 31) := by
    rw [u₃.gpr, u₂.other .a6 (by decide), u₁.gpr, u₂.gpr, u₁.other _ hp6, hx, hy]
  have g₃ (r : Reg) (h6 : r ≠ .a6) (ht : r ≠ .t6) : s₃.gpr r = s.gpr r := by
    rw [u₃.other _ h6, u₂.other _ ht, u₁.other _ h6]
  refine storeW_wp ho (by rw [g₃ _ (by decide) (by decide), h3, u₃.wr, u₂.wr, u₁.wr]; exact wq)
    fun s₄ g₄ m₄ rd₄ wr₄ sp₄ => k s₄ (fun r h6 ht h2 => by rw [g₄ r h2, g₃ r h6 ht]) ?_
      (by rw [rd₄, u₃.rd, u₂.rd, u₁.rd]) (by rw [wr₄, u₃.wr, u₂.wr, u₁.wr])
      (by rw [sp₄, u₃.sp, u₂.sp, u₁.sp])
  rw [m₄, g₃ _ (by decide) (by decide), h3, v₃, word_val, u₃.mem, u₂.mem, u₁.mem]

/-- The words of a block in a region the block is. -/
theorem in_words {rs : List Region} {Q : Addr} (h : (⟨Q, 16⟩ : Region) ∈ rs) :
    ∀ d, d + 4 ≤ 16 → InRegions rs (Q + BitVec.ofNat 64 d) 4 :=
  fun _ hd => ⟨_, h, Offset.contains_base Q hd (by omega)⟩

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
  have q₁ : s₁.gpr .s3 = Q := by rw [g₁ _ (by decide) (by decide), h3]
  refine loadW_wp (by decide) (by decide) (by decide) (by decide)
    (by rw [q₁, rd₁, wr₁]; exact inR 4 (by decide)) fun s₂ v₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  have q₂ : s₂.gpr .s3 = Q := by rw [g₂ _ (by decide) (by decide), q₁]
  refine loadW_wp (by decide) (by decide) (by decide) (by decide)
    (by rw [q₂, rd₂, wr₂, rd₁, wr₁]; exact inR 8 (by decide)) fun s₃ v₃ g₃ m₃ rd₃ wr₃ sp₃ => ?_
  have q₃ : s₃.gpr .s3 = Q := by rw [g₃ _ (by decide) (by decide), q₂]
  refine loadW_wp (by decide) (by decide) (by decide) (by decide)
    (by rw [q₃, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact inR 12 (by decide)) fun s₄ v₄ g₄ m₄ rd₄ wr₄ sp₄ => ?_
  -- The words, zero-extended.
  have e1 : s₄.gpr .t1 = (w 0).setWidth 64 := by
    rw [g₄ _ (by decide) (by decide), g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), v₁, h3, hwd]
  have e3 : s₄.gpr .t3 = (w 4).setWidth 64 := by
    rw [g₄ _ (by decide) (by decide), g₃ _ (by decide) (by decide), v₂, q₁, m₁, hwd]
  have e4 : s₄.gpr .t4 = (w 8).setWidth 64 := by
    rw [g₄ _ (by decide) (by decide), v₃, q₂, m₂, m₁, hwd]
  have e5 : s₄.gpr .t5 = (w 12).setWidth 64 := by rw [v₄, q₃, m₃, m₂, m₁, hwd]
  have q₄ : s₄.gpr .s3 = Q := by rw [g₄ _ (by decide) (by decide), q₃]
  have m₄' : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  have g₄' (r : Reg) (hr : r ∉ mulRegs) : s₄.gpr r = s.gpr r := by
    simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3', h4', h5, -, -⟩ := hr
    rw [g₄ r h5 h2, g₃ r h4' h2, g₂ r h3' h2, g₁ r h1 h2]
  -- Word 0, with the mask.
  simp only [List.cons_append, List.nil_append]
  refine wp_srl (by decide) fun s₅ u₅ => wp_li (imm := 0) (by decide) fun s₆ u₆ => wp_sub fun s₇ u₇ => ?_
  refine wp_li (imm := 0x87) (by decide) fun s₈ u₈ => wp_and fun s₉ u₉ => ?_
  refine wp_sll (by decide) fun s₁₀ u₁₀ => wp_xor fun s₁₁ u₁₁ => ?_
  have v₁₁ : s₁₁.gpr .a6 = ((w 0).setWidth 64 <<< 1) ^^^
      ((BitVec.ofNat 64 0 - (w 12).setWidth 64 >>> 31) &&& BitVec.ofNat 64 0x87) := by
    rw [u₁₁.gpr, u₁₀.gpr, u₁₀.other .t6 (by decide), u₉.gpr, u₉.other .t1 (by decide), u₈.gpr,
      u₈.other .t6 (by decide), u₈.other .t1 (by decide), u₇.gpr, u₇.other .t1 (by decide), u₆.gpr,
      u₆.other .t6 (by decide), u₆.other .t1 (by decide), u₅.gpr, u₅.other .t1 (by decide), e1, e5]
  have g₁₁ (r : Reg) (h6 : r ≠ .t6) (h2 : r ≠ .t2) (ha : r ≠ .a6) : s₁₁.gpr r = s₄.gpr r := by
    rw [u₁₁.other _ ha, u₁₀.other _ ha, u₉.other _ h6, u₈.other _ h2, u₇.other _ h6, u₆.other _ h2,
      u₅.other _ h6]
  have m₁₁ : s₁₁.mem = s.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄']
  have wr₁₁ : s₁₁.wr = s.wr := by
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
  have mem₁₅ : s₁₅.mem = (((s.mem.writeW Q ((w 0 <<< 1) ^^^ (if (w 12).msb then (0x87 : BitVec 32) else 0))).writeW
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
