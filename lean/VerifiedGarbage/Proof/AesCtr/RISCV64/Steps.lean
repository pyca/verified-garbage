module

public import VerifiedGarbage.Impl.AesCtr.RISCV64
import VerifiedGarbage.Proof.AesCtr.RISCV64.Words
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Spec.Ctr

/-!
# AES-CTR on RISC-V: the code between the calls

The straight-line pieces of an iteration, each run in continuation-passing
style, as on PPC64LE (`Proof/AesCtr/PPC64LE/Steps.lean`): the number of
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
  have h1 : (c.setWidth 64).toNat = c.toNat := by simp [BitVec.toNat_setWidth]; omega
  have h2 : (BitVec.ofNat 64 1 <<< 32).toNat = 2 ^ 32 := by decide
  rw [BitVec.toNat_sub, h1, h2]
  omega

/-- The carry out of `L + 2³²`: `1` iff the sum is below `2³²`. -/
theorem carry_bit (L : BitVec 64) :
    (if L + BitVec.ofNat 64 1 <<< 32 < BitVec.ofNat 64 1 <<< 32 then (1 : BitVec 64) else 0).toNat =
      (L.toNat + 2 ^ 32) / 2 ^ 64 := by
  have hL := L.isLt
  have h2 : (BitVec.ofNat 64 1 <<< 32).toNat = 2 ^ 32 := by decide
  have hs : (L + BitVec.ofNat 64 1 <<< 32).toNat = (L.toNat + 2 ^ 32) % 2 ^ 64 := by
    rw [BitVec.toNat_add, h2]
  by_cases h : 2 ^ 64 ≤ L.toNat + 2 ^ 32
  · have : L + BitVec.ofNat 64 1 <<< 32 < BitVec.ofNat 64 1 <<< 32 := by
      rw [BitVec.lt_def, hs, h2]; omega
    simp only [this, ↓reduceIte]
    rw [show (1 : BitVec 64).toNat = 1 from rfl]; omega
  · have : ¬ L + BitVec.ofNat 64 1 <<< 32 < BitVec.ofNat 64 1 <<< 32 := by
      rw [BitVec.lt_def, hs, h2]; omega
    simp only [this, ↓reduceIte]
    rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega

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
  have hr1 : s₂.gpr .t1 = c.setWidth 64 := by
    rw [u₂.other _ (by decide), RegUpd.gpr_write_self, h3, hc]
  have hrem : s₄.gpr .t2 = BitVec.ofNat 64 1 <<< 32 - c.setWidth 64 := by
    rw [u₄.gpr, u₃.gpr, u₃.other .t1 (by decide), u₂.gpr, hr1]
  have h5₄ : s₄.gpr .s5 = BitVec.ofNat 64 left := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide) (by decide), h5]
  have hmask : s₇.gpr .t3 = BitVec.ofNat 64 0 -
      (if BitVec.ofNat 64 left < BitVec.ofNat 64 1 <<< 32 - c.setWidth 64 then 1 else 0) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .t3 (by decide), u₅.gpr, h5₄, hrem]
  have hval : s₁₀.gpr .t2 = BitVec.ofNat 64 (min left (2 ^ 32 - c.toNat)) := by
    rw [u₁₀.gpr, u₉.gpr, u₉.other .t2 (by decide), u₈.gpr, u₈.other .t2 (by decide),
      u₈.other .t3 (by decide), u₇.other .s5 (by decide), u₇.other .t2 (by decide), hmask,
      u₆.other .s5 (by decide), u₆.other .t2 (by decide), u₅.other .s5 (by decide), u₅.other .t2 (by decide),
      h5₄, hrem, sel_min]
    have hl' : (BitVec.ofNat 64 left).toNat = left := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl
    have hr := rem_toNat c
    by_cases h : left < 2 ^ 32 - c.toNat
    · have hlt : BitVec.ofNat 64 left < BitVec.ofNat 64 1 <<< 32 - c.setWidth 64 := by
        rw [BitVec.lt_def, hl', hr]; exact h
      simp only [hlt, ↓reduceIte]
      rw [Nat.min_eq_left (Nat.le_of_lt h)]
    · have hlt : ¬ BitVec.ofNat 64 left < BitVec.ofNat 64 1 <<< 32 - c.setWidth 64 := by
        rw [BitVec.lt_def, hl', hr]; exact h
      simp only [hlt, ↓reduceIte]
      rw [Nat.min_eq_right (by omega)]
      apply BitVec.eq_of_toNat_eq
      rw [hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := c.isLt; omega)]
  have wr₁₀ : s₁₀.wr = s.wr := by
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
  omega

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
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]; rfl
  have t1₂ : s₂.gpr .t1 = BitVec.ofNat 64 m := by rw [u₂.gpr, RegUpd.mem_write, hm]
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
  have inW : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n := fun d n h =>
    ⟨_, hw, Offset.contains_base Q h (by omega)⟩
  have inR : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n := fun d n h =>
    ⟨_, List.mem_append_right _ hw, Offset.contains_base Q h (by omega)⟩
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
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem]; rfl
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr]; rfl
  have t2₄ : s₄.gpr .t2 = BitVec.ofNat 64 1 <<< 32 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr]
  have t1₄ : s₄.gpr .t1 = L + BitVec.ofNat 64 1 <<< 32 := by
    rw [u₄.gpr, u₃.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₂.gpr, RegUpd.gpr_write_self, hL]
  have q₄ : s₄.gpr .s3 = Q := by rw [g₄ _ (by decide) (by decide), h3]
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok (v := .t1) (tmp := .t3) (n := .s3) (off := 8) (w := 8) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun j hj => by
      rw [q₄, wr₄]; exact inW (8 + j) 1 (by omega)) fun s₅ e₅ => ?_
  subst e₅
  refine wp_sltu fun s₆ u₆ => ?_
  generalize hm₁ : writeBytes s₄.mem (s₄.gpr .s3 + BitVec.ofNat 64 8) (beBytes 8 (s₄.gpr .t1)) = m₁ at u₆
  have m₆ : s₆.mem = m₁ := by rw [u₆.mem, RegUpd.mem_write]
  have g₆ (r : Reg) (h1 : r ≠ .t1) (h2 : r ≠ .t2) (h3' : r ≠ .t3) : s₆.gpr r = s.gpr r := by
    rw [u₆.other _ h3', RegUpd.gpr_write_of_ne _ _ h3']; exact g₄ r h1 h2
  have c₆ : s₆.gpr .t3 = if L + BitVec.ofNat 64 1 <<< 32 < BitVec.ofNat 64 1 <<< 32 then 1 else 0 := by
    rw [u₆.gpr, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), t1₄, t2₄]
  have q₆ : s₆.gpr .s3 = Q := by rw [g₆ _ (by decide) (by decide) (by decide), h3]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, RegUpd.wr_write]; exact wr₄
  have rd₆ : s₆.rd = s.rd := by rw [u₆.rd, RegUpd.rd_write, u₄.rd, u₃.rd, u₂.rd]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (loadBE64_ok (d := .t1) (tmp := .t2) (n := .s3) (off := 0) (by decide) (by decide)
    (by decide) (by decide) (by rw [q₆, rd₆, wr₆]; exact inR 0 8 (by decide))) fun s₇ e₇ => ?_
  subst e₇
  refine wp_add fun s₈ u₈ => ?_
  generalize hH : be64 s₆.mem (s₆.gpr .s3) 0 = H at u₈
  have t1₈ : s₈.gpr .t1 = H + s₆.gpr .t3 := by
    rw [u₈.gpr, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide)]
  have g₈ (r : Reg) (h1 : r ≠ .t1) (h2 : r ≠ .t2) : s₈.gpr r = s₆.gpr r := by
    rw [u₈.other _ h1, RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  have q₈ : s₈.gpr .s3 = Q := by rw [g₈ _ (by decide) (by decide), q₆]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, RegUpd.wr_write, RegUpd.wr_write, wr₆]
  refine WP.mono (storeBE_ok (v := .t1) (tmp := .t2) (n := .s3) (off := 0) (w := 8) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun j hj => by
      rw [q₈, wr₈]; exact inW (0 + j) 1 (by omega)) fun s₉ e₉ => ?_
  subst e₉
  -- The memory.
  have m₈ : s₈.mem = m₁ := by rw [u₈.mem, RegUpd.mem_write, RegUpd.mem_write, m₆]
  have hm₁' : m₁ = writeBytes s.mem (Q + BitVec.ofNat 64 8) (beBytes 8 (L + BitVec.ofNat 64 1 <<< 32)) := by
    rw [← hm₁, m₄, q₄, t1₄]
  have hH' : H.toNat = toNat (bytesAt s.mem Q 8) := by
    rw [← hH, q₆, m₆, toNat_be64, hm₁', bytesAt_lo_write]
  have hL' : L.toNat = toNat (bytesAt s.mem (Q + BitVec.ofNat 64 8) 8) := by
    rw [← hL, h3, toNat_be64]
  have hc := carry_bit L
  have h2 : (BitVec.ofNat 64 1 <<< 32).toNat = 2 ^ 32 := by decide
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
