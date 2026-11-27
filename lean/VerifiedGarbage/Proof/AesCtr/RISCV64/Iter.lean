module

import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.AesCtr.RISCV64.Words
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
public import VerifiedGarbage.Proof.AesCtr.Ctr32
public import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
public import VerifiedGarbage.Impl.AesCtr.RISCV64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ctr
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad

/-! ### `AesCtr.RISCV64.Body`, which this module and modules that import it used -/

section

/-! ### `AesCtr.RISCV64.Steps`, which this module and modules that import it used -/

section

/-!
# AES-CTR on RISC-V: the code between the calls

The straight-line pieces of an iteration, each run in continuation-passing
style, as on PPC64LE (`Proof/AesCtr/PPC64LE/Iter.lean`): the number of
blocks of the call (`count`, `min left (2³² − c)`, selected by a mask made
from `sltu`: `sel_min`), the advance past them with the last 32 bits of the
counter block in `t1` (`adv`), and the carry into the first 96 bits
(`carry`: the second half plus `2³²`, whose carry out is `1` iff the sum is
below `2³²`, `carry_bit`; the block is then `t + 2³²`, `add_halves`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.RISCV64.ByteLoad VG.WriteBytes
  VG.Impl.AesCtr.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (toNat ofNat)

/-- `scratch + 2048`, rounded up to a multiple of 8: where the call's number
of blocks is kept. -/
abbrev svOf (S : Addr) : Addr := S + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (pad (S + BitVec.ofNat 64 2048))

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

end

/-- The smaller of `a` and `b`, selected by a mask made from `a < b`. -/
theorem sel_min (a b : BitVec 64) :
    b ^^^ ((a ^^^ b) &&& (BitVec.ofNat 64 0 - (if a < b then 1 else 0))) = if a < b then a else b := by
  by_cases h : a < b
  · simp only [h, ↓reduceIte]
    rw [show BitVec.ofNat 64 0 - (1 : BitVec 64) = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp only [h, ↓reduceIte]
    rw [show BitVec.ofNat 64 0 - (0 : BitVec 64) = 0#64 by decide, BitVec.and_zero, BitVec.xor_zero]

/-- `2³² − c`, for a 32-bit `c`. -/
theorem rem_toNat (c : BitVec 32) :
    (BitVec.ofNat 64 1 <<< 32 - c.setWidth 64).toNat = 2 ^ 32 - c.toNat := by
  have hc := c.isLt
  obtain h1 : (c.setWidth 64).toNat = c.toNat := by simp [BitVec.toNat_setWidth]; omega_using []
  obtain h2 : (BitVec.ofNat 64 1 <<< 32).toNat = 2 ^ 32 := by decide
  rw [BitVec.toNat_sub, h1, h2]
  omega_using []

/-- The carry out of `L + 2³²`: `1` iff the sum is below `2³²`. -/
theorem carry_bit (L : BitVec 64) :
    (if L + BitVec.ofNat 64 1 <<< 32 < BitVec.ofNat 64 1 <<< 32 then (1 : BitVec 64) else 0).toNat =
      (L.toNat + 2 ^ 32) / 2 ^ 64 := by
  have hL := L.isLt
  obtain h2 : (BitVec.ofNat 64 1 <<< 32).toNat = 2 ^ 32 := by decide
  obtain hs : (L + BitVec.ofNat 64 1 <<< 32).toNat = (L.toNat + 2 ^ 32) % 2 ^ 64 := by
    rw [BitVec.toNat_add, h2]
  by_cases h : 2 ^ 64 ≤ L.toNat + 2 ^ 32
  · have : L + BitVec.ofNat 64 1 <<< 32 < BitVec.ofNat 64 1 <<< 32 := by
      rw [BitVec.lt_def, hs, h2]; omega_using [h]
    simp only [this, ↓reduceIte]
    rw [show (1 : BitVec 64).toNat = 1 from rfl]; omega_using [h]
  · have : ¬ L + BitVec.ofNat 64 1 <<< 32 < BitVec.ofNat 64 1 <<< 32 := by
      rw [BitVec.lt_def, hs, h2]; omega_using [h]
    simp only [this, ↓reduceIte]
    rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega_using [h]

theorem svOf_al (S : Addr) : (svOf S).toNat % 8 = 0 := align_al _

theorem t0_svOf (s : State) {S : Addr} (h : s.gpr .s6 = S) :
    (s.write .t0 (s.gpr .s6 + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (pad (s.gpr .s6 + BitVec.ofNat 64 2048)))).gpr
      .t0 + BitVec.ofNat 64 0 = svOf S := by
  rw [RegUpd.gpr_write_self, h]; simp

/-- The blocks of the call: `min left (2³² − c)`, with `c` the last 32 bits
of the counter block, in `t2` and in the slot at `sv`. -/
theorem count_wp {s : State} {Q S : Addr} {left : Nat} {rest : List Instr} {Φ : State → Prop}
    (h3 : s.gpr .s3 = Q) (h5 : s.gpr .s5 = BitVec.ofNat 64 left) (hl : left < 2 ^ 64)
    (h6 : s.gpr .s6 = S) (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4)
    (ws : InRegions s.wr (svOf S) 8)
    (k : ∀ s', s'.gpr .t2 = BitVec.ofNat 64 (min left (2 ^ 32 - (beWord s.mem Q 12).toNat)) →
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW (svOf S) (s'.gpr .t2) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block rest) s' Φ) :
    WP isa (.block (count ++ rest)) s Φ := by
  unfold count
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadBE32_ok (d := .t1) (tmp := .t2) (n := .s3) (off := 12) (by decide) (by decide)
    (by decide) (by decide) (by rw [h3]; exact rq)) fun s₁ e₁ => ?_
  subst e₁
  simp only [List.cons_append, List.nil_append]
  refine wp_li (imm := 1) (by decide) fun s₂ u₂ => wp_sll (by decide) fun s₃ u₃ => wp_sub fun s₄ u₄ => ?_
  refine wp_sltu fun s₅ u₅ => wp_li (imm := 0) (by decide) fun s₆ u₆ => wp_sub fun s₇ u₇ => ?_
  refine wp_xor fun s₈ u₈ => wp_and fun s₉ u₉ => wp_xor fun s₁₀ u₁₀ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (AesCbc.RISCV64.savePtr_ok .s6) fun s₁₁ e₁₁ => ?_
  subst e₁₁
  -- The registers.
  generalize hc : beWord s.mem Q 12 = c
  have g₁ (r : Reg) (h1 : r ≠ .t1) (h2 : r ≠ .t2) :
      ((s.write .t2 ((s.mem (s.gpr .s3 + BitVec.ofNat 64 (12 + 3))).setWidth 64)).write .t1
        ((beWord s.mem (s.gpr .s3) 12).setWidth 64)).gpr r = s.gpr r := by
    rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  have g₁₀ (r : Reg) (h1 : r ≠ .t1) (h2 : r ≠ .t2) (h3 : r ≠ .t3) (h4 : r ≠ .t4) :
      s₁₀.gpr r = s.gpr r := by
    rw [u₁₀.other _ h2, u₉.other _ h4, u₈.other _ h4, u₇.other _ h3, u₆.other _ h4, u₅.other _ h3,
      u₄.other _ h2, u₃.other _ h2, u₂.other _ h2, g₁ r h1 h2]
  obtain hr1 : s₂.gpr .t1 = c.setWidth 64 := by
    rw [u₂.other _ (by decide), RegUpd.gpr_write_self, h3, hc]
  obtain hrem : s₄.gpr .t2 = BitVec.ofNat 64 1 <<< 32 - c.setWidth 64 := by
    rw [u₄.gpr, u₃.gpr, u₃.other .t1 (by decide), u₂.gpr, hr1]
  obtain h5₄ : s₄.gpr .s5 = BitVec.ofNat 64 left := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide) (by decide), h5]
  obtain hmask : s₇.gpr .t3 = BitVec.ofNat 64 0 -
      (if BitVec.ofNat 64 left < BitVec.ofNat 64 1 <<< 32 - c.setWidth 64 then 1 else 0) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .t3 (by decide), u₅.gpr, h5₄, hrem]
  obtain hval : s₁₀.gpr .t2 = BitVec.ofNat 64 (min left (2 ^ 32 - c.toNat)) := by
    rw [u₁₀.gpr, u₉.gpr, u₉.other .t2 (by decide), u₈.gpr, u₈.other .t2 (by decide),
      u₈.other .t3 (by decide), u₇.other .s5 (by decide), u₇.other .t2 (by decide), hmask,
      u₆.other .s5 (by decide), u₆.other .t2 (by decide), u₅.other .s5 (by decide), u₅.other .t2 (by decide),
      h5₄, hrem, sel_min]
    obtain hl' : (BitVec.ofNat 64 left).toNat = left := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl
    obtain hr := rem_toNat c
    by_cases h : left < 2 ^ 32 - c.toNat
    · have hlt : BitVec.ofNat 64 left < BitVec.ofNat 64 1 <<< 32 - c.setWidth 64 := by
        rw [BitVec.lt_def, hl', hr]; exact h
      simp only [hlt, ↓reduceIte]
      rw [Nat.min_eq_left (Nat.le_of_lt h)]
    · have hlt : ¬ BitVec.ofNat 64 left < BitVec.ofNat 64 1 <<< 32 - c.setWidth 64 := by
        rw [BitVec.lt_def, hl', hr]; exact h
      simp only [hlt, ↓reduceIte]
      rw [Nat.min_eq_right (by omega_using [h])]
      apply BitVec.eq_of_toNat_eq
      rw [hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := c.isLt; omega_using [])]
  obtain wr₁₀ : s₁₀.wr = s.wr := by
    rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; rfl
  refine wp_sd (a := svOf S) (by decide) (t0_svOf _ (by rw [g₁₀ .s6 (by decide) (by decide) (by decide)
      (by decide), h6])) (svOf_al S) (by rw [RegUpd.wr_write, wr₁₀]; exact ws) fun s₁₂ u₁₂ => ?_
  refine k s₁₂ ?_ (fun r h0 h1 h2 h3 h4 => ?_) ?_ ?_ ?_ ?_
  · rw [u₁₂.gpr, RegUpd.gpr_write_of_ne _ _ (by decide), hval, hc]
  · rw [u₁₂.gpr, RegUpd.gpr_write_of_ne _ _ h0, g₁₀ r h1 h2 h3 h4]
  · rw [u₁₂.mem, u₁₂.gpr, RegUpd.mem_write, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem,
      u₃.mem, u₂.mem]; rfl
  · rw [u₁₂.rd, RegUpd.rd_write, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; rfl
  · rw [u₁₂.wr, RegUpd.wr_write, wr₁₀]
  · rw [u₁₂.sp, RegUpd.sp_write, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; rfl

theorem shl4 {m : Nat} (h : 16 * m < 2 ^ 64) : BitVec.ofNat 64 m <<< 4 = BitVec.ofNat 64 (16 * m) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.shiftLeft_eq]
  omega_using [h]

/-- On past the call's `m` blocks, with the last 32 bits of the counter
block in `t1`. -/
theorem adv_wp {s : State} {Q S P : Addr} {left m : Nat} {Φ : State → Prop}
    (h3 : s.gpr .s3 = Q) (h4 : s.gpr .s4 = P) (h5 : s.gpr .s5 = BitVec.ofNat 64 left)
    (h6 : s.gpr .s6 = S) (hm : s.mem.readW (svOf S) 64 = BitVec.ofNat 64 m)
    (hml : m ≤ left) (h16m : 16 * m < 2 ^ 64)
    (rs : InRegions (s.rd ++ s.wr) (svOf S) 8)
    (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4)
    (k : ∀ s', s'.gpr .s5 = BitVec.ofNat 64 (left - m) → s'.gpr .s4 = P + BitVec.ofNat 64 (16 * m) →
      s'.gpr .t1 = (beWord s.mem Q 12).setWidth 64 →
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .s4 → r ≠ .s5 → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Φ s') :
    WP isa (.block adv) s Φ := by
  unfold adv
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (AesCbc.RISCV64.savePtr_ok .s6) fun s₁ e₁ => ?_
  subst e₁
  simp only [List.cons_append, List.nil_append]
  refine wp_ld (a := svOf S) (by decide) (t0_svOf _ h6) (svOf_al S)
    (by rw [RegUpd.rd_write, RegUpd.wr_write]; exact rs) fun s₂ u₂ => ?_
  refine wp_sub fun s₃ u₃ => wp_sll (by decide) fun s₄ u₄ => wp_add fun s₅ u₅ => ?_
  have g₁ (r : Reg) (h0 : r ≠ .t0) : (s.write .t0 (s.gpr .s6 + BitVec.ofNat 64 2048 +
      BitVec.ofNat 64 (pad (s.gpr .s6 + BitVec.ofNat 64 2048)))).gpr r = s.gpr r :=
    RegUpd.gpr_write_of_ne _ _ h0
  have g₅ (r : Reg) (h0 : r ≠ .t0) (h1 : r ≠ .t1) (h4 : r ≠ .s4) (h5 : r ≠ .s5) : s₅.gpr r = s.gpr r := by
    rw [u₅.other _ h4, u₄.other _ h1, u₃.other _ h5, u₂.other _ h1, g₁ r h0]
  obtain m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]; rfl
  obtain t1₂ : s₂.gpr .t1 = BitVec.ofNat 64 m := by rw [u₂.gpr, RegUpd.mem_write, hm]
  refine WP.mono (loadBE32_ok (d := .t1) (tmp := .t2) (n := .s3) (off := 12) (by decide) (by decide)
    (by decide) (by decide) (by
      rw [g₅ .s3 (by decide) (by decide) (by decide) (by decide), h3, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd,
        u₃.wr, u₂.rd, u₂.wr, RegUpd.rd_write, RegUpd.wr_write]; exact rq)) fun s₆ e₆ => ?_
  subst e₆
  refine k _ ?_ ?_ ?_ (fun r h0 h1 h2 h4 h5 => ?_) ?_ ?_ ?_ ?_
  · rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁ _ (by decide), h5,
      t1₂, Offset.ofNat_sub_ofNat hml]
  · rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      g₁ _ (by decide), h4, t1₂, shl4 h16m]
  · rw [RegUpd.gpr_write_self, m₅, g₅ .s3 (by decide) (by decide) (by decide) (by decide), h3]
  · rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2, g₅ r h0 h1 h4 h5]
  · rw [RegUpd.mem_write, RegUpd.mem_write, m₅]
  · rw [RegUpd.rd_write, RegUpd.rd_write, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; rfl
  · rw [RegUpd.wr_write, RegUpd.wr_write, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; rfl
  · rw [RegUpd.sp_write, RegUpd.sp_write, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; rfl

/-- The counter block plus `2³²`: a carry into its first 96 bits. -/
theorem carry_wp {s : State} {Q : Addr} {Φ : State → Prop} (h3 : s.gpr .s3 = Q)
    (hw : (⟨Q, 16⟩ : Region) ∈ s.wr)
    (k : ∀ s', (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → s'.gpr r = s.gpr r) →
      bytesAt s'.mem Q 16 = ofNat (toNat (bytesAt s.mem Q 16) + 2 ^ 32) 16 →
      Frame [⟨Q, 16⟩] s.mem s'.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Φ s') :
    WP isa (.block carry) s Φ := by
  obtain inW : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n := fun d n h =>
    ⟨_, hw, Offset.contains_base Q h (by omega_using [h])⟩
  obtain inR : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n := fun d n h =>
    ⟨_, List.mem_append_right _ hw, Offset.contains_base Q h (by omega_using [h])⟩
  unfold carry
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadBE64_ok (d := .t1) (tmp := .t2) (n := .s3) (off := 8) (by decide) (by decide)
    (by decide) (by decide) (by rw [h3]; exact inR 8 8 (by decide))) fun s₁ e₁ => ?_
  subst e₁
  simp only [List.cons_append, List.nil_append]
  refine wp_li (imm := 1) (by decide) fun s₂ u₂ => wp_sll (by decide) fun s₃ u₃ => wp_add fun s₄ u₄ => ?_
  generalize hL : be64 s.mem (s.gpr .s3) 8 = L
  have g₄ (r : Reg) (h1 : r ≠ .t1) (h2 : r ≠ .t2) : s₄.gpr r = s.gpr r := by
    rw [u₄.other _ h1, u₃.other _ h2, u₂.other _ h2, RegUpd.gpr_write_of_ne _ _ h1,
      RegUpd.gpr_write_of_ne _ _ h2]
  obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem]; rfl
  obtain wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr]; rfl
  obtain t2₄ : s₄.gpr .t2 = BitVec.ofNat 64 1 <<< 32 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr]
  obtain t1₄ : s₄.gpr .t1 = L + BitVec.ofNat 64 1 <<< 32 := by
    rw [u₄.gpr, u₃.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₂.gpr, RegUpd.gpr_write_self, hL]
  obtain q₄ : s₄.gpr .s3 = Q := by rw [g₄ _ (by decide) (by decide), h3]
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok (v := .t1) (tmp := .t3) (n := .s3) (off := 8) (w := 8) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun j hj => by
      rw [q₄, wr₄]; exact inW (8 + j) 1 (by omega_using [hj])) fun s₅ e₅ => ?_
  subst e₅
  refine wp_sltu fun s₆ u₆ => ?_
  generalize hm₁ : writeBytes s₄.mem (s₄.gpr .s3 + BitVec.ofNat 64 8) (beBytes 8 (s₄.gpr .t1)) = m₁ at u₆
  obtain m₆ : s₆.mem = m₁ := by rw [u₆.mem, RegUpd.mem_write]
  have g₆ (r : Reg) (h1 : r ≠ .t1) (h2 : r ≠ .t2) (h3' : r ≠ .t3) : s₆.gpr r = s.gpr r := by
    rw [u₆.other _ h3', RegUpd.gpr_write_of_ne _ _ h3']; exact g₄ r h1 h2
  obtain c₆ : s₆.gpr .t3 = if L + BitVec.ofNat 64 1 <<< 32 < BitVec.ofNat 64 1 <<< 32 then 1 else 0 := by
    rw [u₆.gpr, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), t1₄, t2₄]
  obtain q₆ : s₆.gpr .s3 = Q := by rw [g₆ _ (by decide) (by decide) (by decide), h3]
  obtain wr₆ : s₆.wr = s.wr := by rw [u₆.wr, RegUpd.wr_write]; exact wr₄
  obtain rd₆ : s₆.rd = s.rd := by rw [u₆.rd, RegUpd.rd_write, u₄.rd, u₃.rd, u₂.rd]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (loadBE64_ok (d := .t1) (tmp := .t2) (n := .s3) (off := 0) (by decide) (by decide)
    (by decide) (by decide) (by rw [q₆, rd₆, wr₆]; exact inR 0 8 (by decide))) fun s₇ e₇ => ?_
  subst e₇
  refine wp_add fun s₈ u₈ => ?_
  generalize hH : be64 s₆.mem (s₆.gpr .s3) 0 = H at u₈
  obtain t1₈ : s₈.gpr .t1 = H + s₆.gpr .t3 := by
    rw [u₈.gpr, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide)]
  have g₈ (r : Reg) (h1 : r ≠ .t1) (h2 : r ≠ .t2) : s₈.gpr r = s₆.gpr r := by
    rw [u₈.other _ h1, RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  obtain q₈ : s₈.gpr .s3 = Q := by rw [g₈ _ (by decide) (by decide), q₆]
  obtain wr₈ : s₈.wr = s.wr := by rw [u₈.wr, RegUpd.wr_write, RegUpd.wr_write, wr₆]
  refine WP.mono (storeBE_ok (v := .t1) (tmp := .t2) (n := .s3) (off := 0) (w := 8) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun j hj => by
      rw [q₈, wr₈]; exact inW (0 + j) 1 (by omega_using [hj])) fun s₉ e₉ => ?_
  subst e₉
  -- The memory.
  obtain m₈ : s₈.mem = m₁ := by rw [u₈.mem, RegUpd.mem_write, RegUpd.mem_write, m₆]
  obtain hm₁' : m₁ = writeBytes s.mem (Q + BitVec.ofNat 64 8) (beBytes 8 (L + BitVec.ofNat 64 1 <<< 32)) := by
    rw [← hm₁, m₄, q₄, t1₄]
  obtain hH' : H.toNat = toNat (bytesAt s.mem Q 8) := by
    rw [← hH, q₆, m₆, toNat_be64, hm₁', bytesAt_lo_write]
  obtain hL' : L.toNat = toNat (bytesAt s.mem (Q + BitVec.ofNat 64 8) 8) := by
    rw [← hL, h3, toNat_be64]
  obtain hc := carry_bit L
  obtain h2 : (BitVec.ofNat 64 1 <<< 32).toNat = 2 ^ 32 := by decide
  refine k _ (fun r h1 h2 h3' => ?_) ?_ ?_ ?_ ?_ ?_
  · rw [RegUpd.gpr_write_of_ne _ _ h2]
    show s₈.gpr r = _
    rw [g₈ r h1 h2, g₆ r h1 h2 h3']
  · simp only [RegUpd.mem_write]
    show bytesAt (writeBytes s₈.mem (s₈.gpr .s3 + BitVec.ofNat 64 0) (beBytes 8 (s₈.gpr .t1))) Q 16 = _
    rw [m₈, q₈, hm₁', bytesAt_halves, ← add_halves s.mem Q H L (2 ^ 32) hH' hL', t1₈, c₆,
      BitVec.toNat_add, hc, BitVec.toNat_add, h2]
  · simp only [RegUpd.mem_write]
    show Frame _ s.mem (writeBytes s₈.mem (s₈.gpr .s3 + BitVec.ofNat 64 0) (beBytes 8 (s₈.gpr .t1)))
    rw [m₈, q₈, hm₁']
    exact (writeBytes_frame _ _ _ (by rw [beBytes_length]; exact Offset.contains_base Q (by decide) (by decide))).trans
      (writeBytes_frame _ _ _ (by rw [beBytes_length]; exact Offset.contains_base Q (by decide) (by decide)))
  · rw [RegUpd.rd_write]
    show s₈.rd = _
    rw [u₈.rd, RegUpd.rd_write, RegUpd.rd_write, rd₆]
  · rw [RegUpd.wr_write]; exact wr₈
  · rw [RegUpd.sp_write]
    show s₈.sp = _
    rw [u₈.sp, RegUpd.sp_write, RegUpd.sp_write, u₆.sp, RegUpd.sp_write, u₄.sp, u₃.sp, u₂.sp]; rfl

end VG.Proof.AesCtr.RISCV64

end

end

/-!
# AES-CTR on RISC-V: the code before the call

As on PPC64LE (`Proof/AesCtr/PPC64LE/Iter.lean`): the blocks of the call
after `k` blocks (`mOf`), what is left but no further than where the last
32 bits of the counter block wrap around, and `pre_wp`: the code before the
call sets up a call of `vg_aes_ctr32` on them (`CtrCall`), with their
number in the scratch buffer at `sv`, from AES-CBC's loop invariant for
`ctrMode` (`Proof/AesCbc/RISCV64/Loop.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCtr.RISCV64
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)

/-- The blocks of the call after `k` blocks: what is left, but no further
than where the last 32 bits of the counter block wrap around. -/
def mOf (s₀ : State) (k : Nat) : Nat := min (N s₀ - k) (2 ^ 32 - (toNat (iv0 s₀) + k) % 2 ^ 32)

theorem length_iv0 (s₀ : State) : (iv0 s₀).length = 16 := Proof.Cmac.bytesAt_length _ _ _

theorem mOf_pos {s₀ : State} {k : Nat} (hk : k < N s₀) : 0 < mOf s₀ k := by
  unfold mOf; have := Nat.mod_lt (toNat (iv0 s₀) + k) (show 0 < 2 ^ 32 by decide); omega_using [hk]

theorem mOf_le (s₀ : State) (k : Nat) : mOf s₀ k ≤ N s₀ - k := Nat.min_le_left _ _

theorem lo32_mOf (s₀ : State) (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k ≤ 2 ^ 32 := by
  rw [AesCtr.lo32_next (length_iv0 s₀)]; unfold mOf; omega_using []

theorem chainK_ctr (s₀ : State) {k : Nat} (hk : k ≤ N s₀) : chainK AesCtr.ctrMode s₀ k = next (iv0 s₀) k := by
  rw [chainK, AesCtr.ctrMode_chain, List.length_take, Proof.AesCbc.length_blocksAt, Nat.min_eq_left hk]

/-- The slot of the call's number of blocks, within the scratch buffer. -/
theorem cSv (s₀ : State) : (scrR s₀).Contains (sv s₀) 8 := by
  have := q_lt s₀
  rw [sv_eq]; exact Offset.contains_base _ (by omega_using [this]) (by omega_using [this])

theorem cIv (s₀ : State) {d n : Nat} (h : d + n ≤ 16) : (ivR s₀).Contains (Iv s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by omega_using [h])

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.N_le : N s₀ ≤ 2 ^ 60 := by
  have := hp.data_wrap; omega_using [this]

theorem UPre.seg_wrap {k m : Nat} (hk : k < N s₀) (hkm : k + m ≤ N s₀) : (blk s₀ k).toNat + 16 * m ≤ 2 ^ 64 := by
  have := hp.data_wrap
  have : (blk s₀ k).toNat = (Dp s₀).toNat + 16 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega_using [hk, this]),
      Nat.mod_eq_of_lt (by omega_using [hk, this])]
  omega_arith

omit hp in
theorem UPre.seg_sub {k m : Nat} (hkm : k + m ≤ N s₀) : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hkm])

/-- The arguments of the call after `k` blocks. -/
theorem UPre.ctrCall {k : Nat} (hk : k < N s₀) {s : State}
    (a0 : s.gpr .a0 = W s₀) (a1 : s.gpr .a1 = s₀.gpr .a1) (a2 : s.gpr .a2 = Iv s₀)
    (a3 : s.gpr .a3 = blk s₀ k) (a4 : s.gpr .a4 = BitVec.ofNat 64 (mOf s₀ k)) (a5 : s.gpr .a5 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CtrCall s (W s₀) (Iv s₀) (blk s₀ k) (S s₀) (R s₀) (mOf s₀ k) where
  a0 := a0
  a1 := by rw [a1, a1_ofNat]
  a2 := a2
  a3 := a3
  a4 := a4
  a5 := a5
  rounds := hp.rounds
  wrap := UPre.seg_wrap hp hk (by have := mOf_le s₀ k; omega_using [hk, this])
  kc := hp.sch_iv
  kd := hp.sch_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega_using [hk, this]))
  ks := hp.sch_scr.sub_right wsR_sub
  cd := hp.iv_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega_using [hk, this]))
  cs := hp.iv_scr.sub_right wsR_sub
  ds := (hp.data_scr.sub_left (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega_using [hk, this]))).sub_right wsR_sub
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; have := mOf_le s₀ k; omega_using [hk, this]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; have := mOf_le s₀ k; omega_using [hk, this]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- What the code before the call leaves. -/
structure Pre (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  call : CtrCall s₁ (W s₀) (Iv s₀) (blk s₀ k) (S s₀) (R s₀) (mOf s₀ k)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  mem : s₁.mem = s.mem.writeW (sv s₀) (BitVec.ofNat 64 (mOf s₀ k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp

omit hp in
theorem preserved_ne' {r : Reg} (hr : r ∈ preserved) :
    r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 ∧ r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧
      r ≠ .t3 ∧ r ≠ .t4 := by
  revert hr; cases r <;> decide

theorem pre_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.block (count ++ args)) s (Pre s₀ k s) := by
  have hNl := UPre.N_le hp
  refine count_wp (Q := Iv s₀) (S := S s₀) (left := N s₀ - k) h.s3 h.s5 (by omega_using [hNl]) h.s6
    (by rw [h.regs hp]; exact in_rw (r := ivR s₀) (by simp) (cIv s₀ (by decide)))
    (by rw [h.wrs hp]; exact in_rw (r := scrR s₀) (by simp) (cSv s₀)) fun s₁ t2₁ g₁ mem₁ rd₁ wr₁ sp₁ => ?_
  -- The number of blocks.
  have hiv : bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) k := by rw [h.iv, chainK_ctr s₀ (by omega_using [hk])]
  have hlo := lo32_beWord s.mem (Iv s₀)
  rw [hiv, AesCtr.lo32_next (length_iv0 s₀)] at hlo
  have hm : s₁.gpr .t2 = BitVec.ofNat 64 (mOf s₀ k) := by rw [t2₁, ← hlo]; rfl
  unfold args mov
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => ?_
  refine wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => WP.block_nil ?_
  have g₁' (r : Reg) (hr : r ∈ preserved) : s₁.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, -, h0, h1, h2, h3, h4⟩ := preserved_ne' hr
    exact g₁ r h0 h1 h2 h3 h4
  have g (r : Reg) (hr : r ∈ preserved) : s₇.gpr r = s.gpr r := by
    obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := preserved_ne' hr
    rw [u₇.other _ h5, u₆.other _ h4, u₅.other _ h3, u₄.other _ h2, u₃.other _ h1, u₂.other _ h0, g₁' r hr]
  refine ⟨UPre.ctrCall hp hk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, g, ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁' .s1 (by decide), h.s1]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁' .s2 (by decide), h.s2]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁' .s3 (by decide), h.s3]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁' .s4 (by decide), h.s4]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), hm]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁' .s6 (by decide), h.s6]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, mem₁, hm]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]

end

end VG.Proof.AesCtr.RISCV64

end

end

/-!
# AES-CTR on RISC-V: one iteration, and the loop

As on PPC64LE (`Proof/AesCtr/PPC64LE/Iter.lean`): `iter_wp`, one run of
`body` takes AES-CBC's loop invariant for `ctrMode` from `k` blocks to
`k + mOf s₀ k`. The call gives CTR's output on its blocks
(`AesCtr.ctr32_crypt`), and the counter block it leaves, with the carry into
the first 96 bits if its last 32 bits wrapped around, is CTR's
(`AesCtr.ctr32_next`, `AesCtr.ctr32_wrap`, `AesCtr.carry_next`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.ByteLoad VG.Impl.AesCtr.RISCV64
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)

/-- The slot of the call's number of blocks. -/
abbrev slotR (s₀ : State) : Region := ⟨sv s₀, 8⟩

/-- What the call leaves, after `k` blocks. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = W s₀
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = Iv s₀
  s4 : s.gpr .s4 = blk s₀ k
  s5 : s.gpr .s5 = BitVec.ofNat 64 (N s₀ - k)
  s6 : s.gpr .s6 = S s₀
  keep : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (Mut s₀) (savedMem s₀) s.mem
  slot : s.mem.readW (sv s₀) 64 = BitVec.ofNat 64 (mOf s₀ k)
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) =
    outK AesCtr.ctrMode s₀ (k + mOf s₀ k) ++ (blks s₀).drop (k + mOf s₀ k)
  /-- The counter block: `t + k + m`, less `2³²` if its last 32 bits
  wrapped around. -/
  iv : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k < 2 ^ 32 →
    bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) (k + mOf s₀ k)
  ivw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32 →
    bytesAt s.mem (Iv s₀) 16 = ofNat (toNat (next (iv0 s₀) k) + mOf s₀ k - 2 ^ 32) 16

theorem slot_sub (s₀ : State) : Region.Sub (slotR s₀) (cR s₀) := Region.sub_prefix (by decide)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- The call, after the code before it. -/
theorem mid_wp {k : Nat} (hk : k < N s₀) {s s₁ : State} (h : LInv AesCtr.ctrMode s₀ k s)
    (a : Pre s₀ k s s₁) : WP isa ctrCall s₁ (Mid s₀ k) := by
  refine WP.mono (ctr_call a.call) fun s₂ c => ?_
  have g (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  have hdw := hp.data_wrap
  have hsw := hp.scr_wrap
  generalize hmd : mOf s₀ k = m at hm0 hle a c
  obtain slotScr : Region.Sub (slotR s₀) (scrR s₀) := fun _ h => cR_sub _ (slot_sub s₀ _ h)
  -- The memory before the call: the slot written.
  obtain f₁ : Frame [slotR s₀] s.mem s₁.mem := by
    rw [a.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain segSub : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) := UPre.seg_sub (by omega_arith)
  have fc : Frame [ivR s₀, ⟨blk s₀ k, 16 * m⟩, wsR s₀] s₁.mem s₂.mem := c.frame
  obtain fAll : Frame (Mut s₀) s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨cR s₀, by simp, slot_sub s₀⟩).trans
    (fc.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, segSub⟩
      · exact ⟨wsR s₀, by simp, fun _ h => h⟩)
  -- The slot after the call.
  obtain dSlot : ∀ r ∈ [ivR s₀, ⟨blk s₀ k, 16 * m⟩, wsR s₀], (slotR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_scr.symm.sub_left slotScr
    · exact (hp.data_scr.symm.sub_left slotScr).sub_right segSub
    · exact hp.cR_wsR.sub_left (slot_sub s₀)
  obtain slot : s₂.mem.readW (sv s₀) 64 = BitVec.ofNat 64 m := by
    rw [fc.readW (r := slotR s₀) (Region.contains_self _ _) dSlot (by decide),
      a.mem, Mem.readW_writeW_self64, hmd]
  -- The data and the counter block before the call.
  obtain hiv : bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) k := by rw [h.iv, chainK_ctr s₀ (by omega_arith)]
  obtain ivIn : bytesAt s₁.mem (Iv s₀) 16 = next (iv0 s₀) k := by
    rw [Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_scr.sub_right slotScr) (by decide), hiv]
  obtain big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, slotScr⟩)
  obtain sched : bytesAt s₁.mem (W s₀) (16 * (R s₀ + 1)) = wK s₀ := UPre.sched_bytes hp big₁
  obtain hlen : (blks s₀).length = N s₀ := Proof.AesCbc.length_blocksAt _ _ _
  -- Blocks outside the call's.
  have outside (j : Nat) (hj : j < N s₀) (ho : j < k ∨ k + m ≤ j) :
      ∀ r ∈ [slotR s₀, ivR s₀, ⟨blk s₀ k, 16 * m⟩, wsR s₀],
        (⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r := by
    intro r hr
    obtain dj : Region.Sub ⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ (dataR s₀) := Offset.sub_base _ (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.data_scr.sub_left dj).sub_right slotScr
    · exact (hp.iv_data.symm.sub_left dj)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (hp.data_scr.sub_left dj).sub_right wsR_sub
  have keepBlocks {p : Addr} {a n : Nat} (hp' : p = Dp s₀ + BitVec.ofNat 64 (16 * a)) (hn : a + n ≤ N s₀)
      (ho : a + n ≤ k ∨ k + m ≤ a) : Spec.Cbc.blocksAt s₂.mem p n = Spec.Cbc.blocksAt s.mem p n := by
    subst hp'
    obtain hd : ∀ j < n, ∀ r ∈ [slotR s₀, ivR s₀, ⟨blk s₀ k, 16 * m⟩, wsR s₀],
        (⟨Dp s₀ + BitVec.ofNat 64 (16 * a) + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r :=
      fun j hj => by
        rw [Offset.add_add, show 16 * a + 16 * j = 16 * (a + j) by omega_arith]
        exact outside (a + j) (by omega_arith) (by omega_arith)
    rw [AesCtr.blocksAt_frame fc (fun j hj r hr => hd j hj r (List.mem_cons_of_mem _ hr)),
      AesCtr.blocksAt_frame f₁ (fun j hj r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd j hj _ (by simp))]
  have dataS := h.data
  rw [outK, AesCtr.ctrMode_out] at dataS
  -- The call's blocks.
  obtain segIn : Spec.Cbc.blocksAt s₁.mem (blk s₀ k) m = ((blks s₀).drop k).take m := by
    rw [AesCtr.blocksAt_frame f₁ (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Offset.add_add, show 16 * k + 16 * j = 16 * (k + j) by omega_arith]
      exact (hp.data_scr.sub_left (Offset.sub_base _ (by omega_arith))).sub_right slotScr),
      ← AesCtr.blocksAt_take _ _ (show m ≤ N s₀ - k by omega_arith), ← AesCtr.blocksAt_drop _ _ (by omega_arith), dataS,
      List.drop_left' (by rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_arith)])]
  obtain seg := AesCtr.ctr32_crypt (k := m) (by rw [ivIn, ← hmd]; exact lo32_mOf s₀ k) c.out
  rw [sched, ivIn, segIn] at seg
  refine ⟨by rw [g .s1 (by decide), h.s1], by rw [g .s2 (by decide), h.s2],
    by rw [g .s3 (by decide), h.s3], by rw [g .s4 (by decide), h.s4],
    by rw [g .s5 (by decide), h.s5], by rw [g .s6 (by decide), h.s6],
    fun r hr hv => by rw [g r hr, h.keep r hr hv], by rw [c.rd, a.rd, h.rd], by rw [c.wr, a.wr, h.wr],
    by rw [c.sp, a.sp, h.sp], h.frame.trans fAll, by rw [hmd]; exact slot, ?_, ?_, ?_⟩
  · -- The data: the first `k` blocks and those after the call's as they were, and the call's.
    obtain hlc : (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k)).length = k := by
      rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_arith)]
    obtain hA : Spec.Cbc.blocksAt s.mem (Dp s₀) k =
        Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k) := by
      rw [← AesCtr.blocksAt_take _ _ (show k ≤ N s₀ by omega_arith), dataS, List.take_left' hlc]
    obtain hC : Spec.Cbc.blocksAt s.mem (Dp s₀ + BitVec.ofNat 64 (16 * (k + m))) (N s₀ - (k + m)) =
        (blks s₀).drop (k + m) := by
      rw [← AesCtr.blocksAt_drop _ _ (show k + m ≤ N s₀ by omega_arith), dataS]
      conv => lhs; rw [show k + m = (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀)
        ((blks s₀).take k)).length + m by rw [hlc]]
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega_arith), List.nil_append, hlc, Nat.add_sub_cancel_left]
      exact List.drop_drop
    rw [hmd, AesCtr.blocksAt_three s₂.mem (Dp s₀) (a := k) (b := m) (by omega_arith),
      keepBlocks (a := 0) (by simp) (by omega_arith) (by omega_arith), keepBlocks (a := k + m) rfl (by omega_arith) (by omega_arith),
      show Dp s₀ + BitVec.ofNat 64 (16 * k) = blk s₀ k from rfl, seg, hA, hC, outK, AesCtr.ctrMode_out]
    exact AesCtr.crypt_step _ _ _ (by omega_arith)
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_next (by rw [ivIn]; omega_arith) c.ctr, ivIn, AesCtr.next_add]
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_wrap (by rw [ivIn]; omega_arith) c.ctr, ivIn]

/-- The invariant after `k + m` blocks, from the facts the iteration ends with. -/
theorem finish {k m : Nat} (hkm : k + m ≤ N s₀) {s s' : State} (h : Mid s₀ k s) (hmd : mOf s₀ k = m)
    (g : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .s4 → r ≠ .s5 → s'.gpr r = s.gpr r)
    (s4 : s'.gpr .s4 = blk s₀ (k + m)) (s5 : s'.gpr .s5 = BitVec.ofNat 64 (N s₀ - (k + m)))
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hf : Frame [ivR s₀] s.mem s'.mem)
    (hiv : bytesAt s'.mem (Iv s₀) 16 = next (iv0 s₀) (k + m)) :
    LInv AesCtr.ctrMode s₀ (k + m) s' where
  s1 := by rw [g .s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.s1]
  s2 := by rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.s2]
  s3 := by rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.s3]
  s4 := s4
  s5 := s5
  s6 := by rw [g .s6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.s6]
  keep r hr hv := by
    obtain ⟨-, -, -, -, -, -, h0, h1, h2, h3, -⟩ := preserved_ne' hr
    rw [g r h0 h1 h2 h3 (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  sp := by rw [hsp, h.sp]
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
  data := by
    rw [AesCtr.blocksAt_frame hf (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_data.symm.sub_left (Offset.sub_base _ (by omega_arith))), h.data, hmd]
  iv := by rw [hiv, chainK_ctr s₀ hkm]

omit hp in
theorem setWidth_beq_zero (y : BitVec 32) : (y.setWidth 64 == 0) = (y == 0) := by
  by_cases h : y = 0
  · subst h; rfl
  · have h' : y.setWidth 64 ≠ 0 := fun e => h (by
      obtain e' := congrArg BitVec.toNat e
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans y.isLt (by decide))] at e'
      exact BitVec.eq_of_toNat_eq e')
    rw [beq_eq_false_iff_ne.mpr h', beq_eq_false_iff_ne.mpr h]

/-- What `adv` leaves. -/
structure After (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  gpr : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .s4 → r ≠ .s5 → s₂.gpr r = s.gpr r
  s4 : s₂.gpr .s4 = blk s₀ (k + mOf s₀ k)
  s5 : s₂.gpr .s5 = BitVec.ofNat 64 (N s₀ - (k + mOf s₀ k))
  mem : s₂.mem = s.mem
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  sp : s₂.sp = s.sp
  ev : isa.eval (.zero .t1) s₂ = some (decide (AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32))

/-- On past the call's blocks, with the wrap of the counter in `t1`. -/
theorem adv_wp' {k : Nat} (hk : k < N s₀) {s : State} (h : Mid s₀ k s) : WP isa (.block adv) s (After s₀ k s) := by
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  obtain hlo := lo32_mOf s₀ k
  have hdw := hp.data_wrap
  obtain hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine adv_wp (Q := Iv s₀) (S := S s₀) (P := blk s₀ k) (left := N s₀ - k) (m := mOf s₀ k)
    h.s3 h.s4 h.s5 h.s6 h.slot hle (by omega_arith) (by rw [hR]; exact in_rw (r := scrR s₀) (by simp) (cSv s₀))
    (by rw [hR]; exact in_rw (r := ivR s₀) (by simp) (cIv s₀ (by decide)))
    fun s₂ s5₂ s4₂ t1₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  refine ⟨g₂, ?_, by rw [s5₂, Nat.sub_sub], m₂, rd₂, wr₂, sp₂, ?_⟩
  · rw [s4₂, Offset.add_add, show 16 * k + 16 * mOf s₀ k = 16 * (k + mOf s₀ k) by omega_arith]
  obtain hlo2 := lo32_beWord s.mem (Iv s₀)
  rw [eval_zero, t1₂, setWidth_beq_zero]
  by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
  · have e := h.ivw hw
    rw [e, AesCtr.lo32, AesCtr.toNat_ofNat] at hlo2
    have hw' := hw
    unfold AesCtr.lo32 at hw'
    have : (beWord s.mem (Iv s₀) 12).toNat = 0 := by rw [← hlo2]; omega_arith
    obtain h0 := BitVec.eq_of_toNat_eq (y := (0 : BitVec 32)) this
    simp [h0, hw]
  · have e := h.iv (by omega_arith)
    rw [e, AesCtr.lo32_next (length_iv0 s₀)] at hlo2
    rw [AesCtr.lo32_next (length_iv0 s₀)] at hw hlo
    have : (beWord s.mem (Iv s₀) 12).toNat ≠ 0 := by rw [← hlo2]; omega_arith
    obtain h0 : beWord s.mem (Iv s₀) 12 ≠ 0 := fun h0 => this (by rw [h0]; rfl)
    rw [AesCtr.lo32_next (length_iv0 s₀)]
    simp only [hw, decide_false, Option.some.injEq, beq_eq_false_iff_ne]
    exact h0

/-- The carry if the counter wrapped around. -/
theorem fin_wp {k : Nat} (hk : k < N s₀) {s s₂ : State} (h : Mid s₀ k s) (a : After s₀ k s s₂) :
    WP isa (.ite (.zero .t1) (.block carry) (.block [])) s₂ (LInv AesCtr.ctrMode s₀ (k + mOf s₀ k)) := by
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  obtain s3₂ : s₂.gpr .s3 = Iv s₀ := by
    rw [a.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), h.s3]
  by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
  · refine WP.ite true (by rw [a.ev]; simp [hw]) (fun _ => ?_) (fun h => by cases h)
    refine carry_wp s3₂ (by rw [a.wr, h.wr, hp.wr]; simp) fun s₃ g₃ bytes₃ f₃ rd₃ wr₃ sp₃ => ?_
    refine finish hp (by omega_arith) h rfl
      (fun r h0 h1 h2 h3 h4 h5 => by rw [g₃ r h1 h2 h3, a.gpr r h0 h1 h2 h4 h5])
      (by rw [g₃ _ (by decide) (by decide) (by decide), a.s4])
      (by rw [g₃ _ (by decide) (by decide) (by decide), a.s5])
      (by rw [rd₃, a.rd]) (by rw [wr₃, a.wr]) (by rw [sp₃, a.sp]) (by rw [← a.mem]; exact f₃) ?_
    rw [bytes₃, a.mem, h.ivw hw]
    exact AesCtr.carry_next (length_iv0 s₀) hw
  · refine WP.ite false (by rw [a.ev]; simp [hw]) (fun h => by cases h) (fun _ => WP.block_nil ?_)
    exact finish hp (by omega_arith) h rfl (fun r h0 h1 h2 _ h4 h5 => a.gpr r h0 h1 h2 h4 h5) a.s4 a.s5
      a.rd a.wr a.sp (by rw [a.mem]; exact Frame.refl _ _)
      (by rw [a.mem, h.iv (by have := lo32_mOf s₀ k; omega_arith)])

/-- One iteration. -/
theorem iter_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa body s (LInv AesCtr.ctrMode s₀ (k + mOf s₀ k)) :=
  WP.seq (WP.mono (pre_wp hp hk h) fun _ a =>
    WP.seq (WP.mono (mid_wp hp hk h a) fun _ hm =>
      WP.seq (WP.mono (adv_wp' hp hk hm) fun _ a => fin_wp hp hk hm a)))

/-- The loop, from `k` blocks to all of them. -/
theorem loop_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.loop body (.nonzero .s5)) s (LInv AesCtr.ctrMode s₀ (N s₀)) := by
  obtain hN := (s₀.gpr .a4).isLt
  refine WP.loop (M := isa) (body := body) (c := .nonzero .s5) (Q := LInv AesCtr.ctrMode s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv AesCtr.ctrMode s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine WP.mono (iter_wp hp hj h) fun s' h' => ?_
  obtain hm0 := mOf_pos hj
  obtain hle := mOf_le s₀ j
  obtain ev := eval_nonzero_ofNat s' .s5 (k := N s₀ - (j + mOf s₀ j))
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN) h'.s5
  by_cases hz' : j + mOf s₀ j = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp; omega_arith, N s₀ - (j + mOf s₀ j), by omega_arith, j + mOf s₀ j, rfl, by omega_arith, h'⟩

end

/-- The whole function. -/
theorem crypt_wp {s₀ : State} (h0 : (modeRISCV64 AesCtr.ctrMode).pre s₀) :
    WP isa crypt s₀ (Done AesCtr.ctrMode s₀) :=
  ends_wp h0 fun hp hN _ h => loop_wp hp hN h

end VG.Proof.AesCtr.RISCV64
