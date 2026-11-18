module

public import VerifiedGarbage.Impl.AesCtr.RISCV64.Final
public import VerifiedGarbage.Proof.AesCtr.Final
public import VerifiedGarbage.Proof.AesCfb.RISCV64.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
import VerifiedGarbage.Proof.AesCtr.RISCV64.Lit
public import VerifiedGarbage.Proof.AesCtr.Ctr32
public import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.Modes.Words
import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.AesCtr.RISCV64.Final
meta import VerifiedGarbage.Proof.AesCtr.Final
meta import VerifiedGarbage.Proof.AesCfb.RISCV64.Final
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Lit
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.Modes.Words
meta import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesCtr.Rounds
public import VerifiedGarbage.Impl.AesCtr.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
public import VerifiedGarbage.Spec.Ctr.Contract
import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.AesCtr.RISCV64.Words
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ctr
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Words
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
meta import VerifiedGarbage.Impl.AesCtr.RISCV64
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Spec.Ctr
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.Proof.Framework.RISCV64.Align
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.AesCtr.Rounds
meta import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
meta import VerifiedGarbage.Proof.Framework.RelCT

/-! ### `AesCtr.RISCV64.Verified`, which this module and modules that import it used -/

section

/-! ### `AesCtr.RISCV64.CT`, which this module and modules that import it used -/

section

/-! ### `AesCtr.RISCV64.Iter`, which this module and modules that import it used -/

section

/-! ### `AesCtr.RISCV64.Body`, which this module and modules that import it used -/

section

/-! ### `AesCtr.RISCV64.Steps`, which this module and modules that import it used -/

section

/-!
# AES-CTR on RISC-V: the code between the calls

The straight-line pieces of an iteration, each run in continuation-passing
style, as on PPC64LE (`Proof/AesCtr/PPC64LE/Verified.lean`): the number of
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

As on PPC64LE (`Proof/AesCtr/PPC64LE/Verified.lean`): the blocks of the call
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

As on PPC64LE (`Proof/AesCtr/PPC64LE/Verified.lean`): `iter_wp`, one run of
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

end

end

/-!
# AES-CTR on RISC-V: constant time

As on PPC64LE (`Proof/AesCtr/PPC64LE/Verified.lean`): two runs from states that
agree on the public arguments and on the last 32 bits of the counter block
(`ctrPub`, which the contract's `leak` declares) are related piece by piece
(`RelCT`): the taint analysis covers the code between the call and the
branches, from the registers the correctness proof pins to the public
arguments and the stack pointer; the call is constant time by its own proof
(`ctr_rel`), with the same arguments in both runs, since the number of blocks
it takes depends only on the public data (`mOf_eq`); and the branches (the
carry, the loop) are on facts the correctness proof gives in terms of the
public data (`After.ev`, `iter_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.RISCV64

open VG VG.RISCV64 VG.Impl.AesCtr.RISCV64
open VG.Proof.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat)

/-- What two runs agree on: the public arguments, and the last 32 bits of the
counter block. -/
def ctrPub (s₀ s₀' : State) : Prop :=
  (modeRISCV64 AesCtr.ctrMode).pub s₀ s₀' ∧ AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀')

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block (count ++ args)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem adv_taint : ∃ h, (taint.check (Taint.ofRegs [.s3, .s4, .s5, .s6]) (.block adv) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem carry_taint : ∃ h, (taint.check (Taint.ofRegs [.s3]) (.block carry) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {s₀ s₀' : State} (hq : (modeRISCV64 AesCtr.ctrMode).pub s₀ s₀')
  (hl : AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀'))
include hq hl

omit hq in
theorem lo32_next_eq (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) = AesCtr.lo32 (next (iv0 s₀') k) := by
  rw [AesCtr.lo32_next (length_iv0 _), AesCtr.lo32_next (length_iv0 _)]
  unfold AesCtr.lo32 at hl
  omega_using [hl]

theorem mOf_eq (k : Nat) : mOf s₀ k = mOf s₀' k := by
  have e := lo32_next_eq hl k
  rw [AesCtr.lo32_next (length_iv0 _), AesCtr.lo32_next (length_iv0 _)] at e
  unfold mOf
  rw [e, pub_N hq]

/-- One iteration, in two runs. -/
theorem body_rel (hp : UPre s₀) (hp' : UPre s₀') {k : Nat} (hk : k < N s₀) :
    RelCT isa (fun a b => LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b) body
      fun a b => LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) a ∧ LInv AesCtr.ctrMode s₀' (k + mOf s₀' k) b := by
  have hk' : k < N s₀' := by rw [← pub_N hq]; exact hk
  obtain ⟨_, t1⟩ := pre_taint
  obtain ⟨_, t3⟩ := adv_taint
  obtain ⟨_, tc⟩ := carry_taint
  obtain ⟨_, tn⟩ := nil_taint
  -- The code before the call.
  have p1 := (taintRegs (P := fun a b => LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b) vars
    (fun _ _ h => ⟨by rw [h.1.sp, h.2.sp, pub_sp hq], LInv.agree hq h.1 h.2⟩) t1).wp
    (F₁ := fun (s₁ : State) => ∃ s, LInv AesCtr.ctrMode s₀ k s ∧ Pre s₀ k s s₁)
    (F₂ := fun (s₁ : State) => ∃ s, LInv AesCtr.ctrMode s₀' k s ∧ Pre s₀' k s s₁)
    fun a b h => ⟨WP.mono (pre_wp hp hk h.1) fun _ x => ⟨a, h.1, x⟩,
      WP.mono (pre_wp hp' hk' h.2) fun _ x => ⟨b, h.2, x⟩⟩
  -- The call, with the same arguments in both runs.
  have p2 := (ctr_rel (K := W s₀) (C := Iv s₀) (D := blk s₀ k) (S := S s₀) (R := R s₀) (n := mOf s₀ k)
    (P := fun a b => (∃ s, LInv AesCtr.ctrMode s₀ k s ∧ Pre s₀ k s a) ∧
      (∃ s, LInv AesCtr.ctrMode s₀' k s ∧ Pre s₀' k s b)) fun a b h => by
    obtain ⟨⟨s, hs, pa⟩, ⟨t, ht, pb⟩⟩ := h
    refine ⟨pa.call, ?_, by rw [pa.sp, pb.sp, hs.sp, ht.sp, pub_sp hq]⟩
    rw [pub_W hq, pub_Iv hq, pub_blk hq, pub_S hq, pub_R hq, mOf_eq hq hl]; exact pb.call).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun a b h => by
      obtain ⟨⟨s, hs, pa⟩, ⟨t, ht, pb⟩⟩ := h
      exact ⟨mid_wp hp hk hs pa, mid_wp hp' hk' ht pb⟩
  -- On past the call's blocks.
  have p3 := (taintRegs (P := fun a b => Mid s₀ k a ∧ Mid s₀' k b)
    [.s3, .s4, .s5, .s6] (fun a b h => ⟨by rw [h.1.sp, h.2.sp, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.s3, h.2.s3, pub_Iv hq]
      · rw [h.1.s4, h.2.s4, pub_blk hq]
      · rw [h.1.s5, h.2.s5, pub_N hq]
      · rw [h.1.s6, h.2.s6, pub_S hq]⟩) t3).wp
    (F₁ := fun (s₂ : State) => ∃ s, Mid s₀ k s ∧ After s₀ k s s₂)
    (F₂ := fun (s₂ : State) => ∃ s, Mid s₀' k s ∧ After s₀' k s s₂)
    fun a b h => ⟨WP.mono (adv_wp' hp hk h.1) fun _ x => ⟨a, h.1, x⟩,
      WP.mono (adv_wp' hp' hk' h.2) fun _ x => ⟨b, h.2, x⟩⟩
  -- The carry if the counter wrapped around in both runs.
  have p4 : RelCT isa (fun a b => (∃ s, Mid s₀ k s ∧ After s₀ k s a) ∧ (∃ s, Mid s₀' k s ∧ After s₀' k s b))
      (.ite (.zero .t1) (.block carry) (.block [])) fun _ _ => True := by
    refine RelCT.ite (fun a b h => ?_) (taintRegs [.s3] (fun a b h => ?_) tc)
      (taintRegs [] (fun a b h => ?_) tn)
    · obtain ⟨⟨s, hs, xa⟩, ⟨t, ht, xb⟩⟩ := h
      rw [xa.ev, xb.ev, lo32_next_eq hl, mOf_eq hq hl]
    · obtain ⟨⟨⟨s, hs, xa⟩, ⟨t, ht, xb⟩⟩, _⟩ := h
      refine ⟨by rw [xa.sp, xb.sp, hs.sp, ht.sp, pub_sp hq], fun r hr => ?_⟩
      simp only [List.mem_singleton] at hr; subst hr
      rw [xa.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide),
        xb.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), hs.s3, ht.s3, pub_Iv hq]
    · obtain ⟨⟨⟨s, hs, xa⟩, ⟨t, ht, xb⟩⟩, _⟩ := h
      exact ⟨by rw [xa.sp, xb.sp, hs.sp, ht.sp, pub_sp hq], fun r hr => by simp at hr⟩
  have p5 := p4.wp (F₁ := LInv AesCtr.ctrMode s₀ (k + mOf s₀ k))
    (F₂ := LInv AesCtr.ctrMode s₀' (k + mOf s₀' k)) fun a b h => by
      obtain ⟨⟨s, hs, xa⟩, ⟨t, ht, xb⟩⟩ := h
      exact ⟨fin_wp hp hk hs xa, fin_wp hp' hk' ht xb⟩
  exact (p1.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((p2.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((p3.mono (fun _ _ h => h) fun _ _ h => h.2).seq (p5.mono (fun _ _ h => h) fun _ _ h => h.2)))

/-- The loop's relation, with the number of blocks left. -/
def CRel (s₀ s₀' : State) (n : Nat) (a b : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b

theorem loop_rel (hp : UPre s₀) (hp' : UPre s₀') (n : Nat) :
    RelCT isa (CRel s₀ s₀' n) (.loop body (.nonzero .s5))
      fun a b => LInv AesCtr.ctrMode s₀ (N s₀) a ∧ LInv AesCtr.ctrMode s₀' (N s₀') b := by
  refine RelCT.loop (M := isa) (CRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  have hb₀ := (s₀.gpr .a4).isLt
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : CRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have hm := mOf_eq hq hl k
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  refine (body_rel hq hl hp hp' hk).mono (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩) fun s₁ s₂ ⟨l₁, l₂⟩ => ?_
  rw [← hm] at l₂
  have bd : N s₀ - (k + mOf s₀ k) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb₀
  have e₁ := Steps.eval_nonzero_ofNat s₁ .s5 bd l₁.s5
  have e₂ := Steps.eval_nonzero_ofNat s₂ .s5 (k := N s₀ - (k + mOf s₀ k)) bd (by rw [l₂.s5, hN])
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + mOf s₀ k = N s₀ := by
      have : N s₀ - (k + mOf s₀ k) = 0 := by simpa using hf
      omega_using [hk, hle, this]
    exact ⟨h0 ▸ l₁, by rw [← hN, ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + mOf s₀ k) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + mOf s₀ k), by omega_using [hk, hm0], k + mOf s₀ k, rfl, by omega_using [h0], l₁, l₂⟩

end

/-- The whole function, in two runs that agree on the public data. -/
theorem crypt_rel {s₀ s₀' : State} (h0 : (modeRISCV64 AesCtr.ctrMode).pre s₀)
    (h0' : (modeRISCV64 AesCtr.ctrMode).pre s₀') (hq : ctrPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') crypt fun _ _ => True :=
  ends_rel h0 h0' hq.1 fun hp hp' hN =>
    (loop_rel hq.1 hq.2 hp hp' (N s₀ - 0)).mono (fun _ _ h => ⟨0, rfl, hN, h.1, h.2⟩) fun _ _ h => h

theorem crypt_ct : ConstantTime isa (modeRISCV64 AesCtr.ctrMode).pre ctrPub crypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (crypt_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCtr.RISCV64

end

end

/-!
# AES-CTR on RISC-V: `Verified`

Correctness and constant time, from `crypt_wp` and `crypt_ct`, a state
satisfying the precondition, and the shared contract of
`Spec/Ctr/Contract.lean` (with no stack: a call stores nothing in memory, and
the return address is saved in the scratch buffer), whose `leak` (the counter
block's last four bytes) gives the agreement on the last 32 bits of the
counter block `crypt_ct` assumes (`ctrPub`), as on PPC64LE
(`Proof/AesCtr/PPC64LE/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.RISCV64

open VG VG.RISCV64 VG.Impl.AesCtr.RISCV64
open VG.Proof.AesCbc.RISCV64

theorem crypt_correct (s : State) (hs : (modeRISCV64 AesCtr.ctrMode).pre s) :
    ∃ t s', Exec isa crypt s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 AesCtr.ctrMode).post s s' := by
  obtain ⟨t, s', he, hg, hra, hp⟩ := crypt_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

theorem crypt_verified : Verified RISCV64.target crypt (Proof.AesCtr.roundsContract RISCV64.abi) :=
  Verified.of_correct (k := { modeRISCV64 AesCtr.ctrMode with pub := ctrPub }) crypt_correct crypt_ct
    { pre := by sig_implies_pre [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeRISCV64, RISCV64.abi,
        RISCV64.argRegs]
      -- `ctrMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeRISCV64, AesCtr.ctrMode, RISCV64.abi,
          RISCV64.argRegs]
        sig_reduce [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeRISCV64, AesCtr.ctrMode, RISCV64.abi,
          RISCV64.argRegs] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by
        have hm : ∀ s₁ s₂, (Proof.AesCtr.roundsContract RISCV64.abi).pre s₁ → (Proof.AesCtr.roundsContract RISCV64.abi).pre s₂ →
            (Proof.AesCtr.roundsContract RISCV64.abi).pub s₁ s₂ → (modeRISCV64 AesCtr.ctrMode).pub s₁ s₂ := by
          sig_implies_pub [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeRISCV64, RISCV64.abi, RISCV64.argRegs]
        intro s₁ s₂ h₁ h₂ h
        refine ⟨hm s₁ s₂ h₁ h₂ h, ?_⟩
        sig_pub [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, Spec.Ctr.ctrLeak, RISCV64.abi, RISCV64.argRegs] at h
        sig_split h
        exact AesCtr.lo32_of_leak (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)
          (by assumption)
      sat := by sig_implies_sat [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeRISCV64, RISCV64.abi,
        RISCV64.argRegs] [sat] using sat }

end VG.Proof.AesCtr.RISCV64

end

end

/-!
# AES-CTR of a message's last piece on RISC-V

`cryptFinal_framed`: `vg_aes_ctr_final` (`Impl/AesCtr/RISCV64/Final.lean`)
meets `Proof.AesCtr.finalRoundsContract`, from which the shared contract
follows (`Proof.AesCtr.final_keyed`).

The code is proven against `ctrFinalRISCV64`, with a seventh argument `save`
(`a6`) of 80 bytes, for its return address and its caller's registers and a
block of its own (`final_implies`: the shared contract with it,
`finalScratchContract`), as a caller of the whole-block function, through its
contract (`modeRISCV64 ctrMode`, with `ctrPub`). It shares AES-CFB's final
functions' setup (`Proof/AesCfb/RISCV64/Final.lean`: `Setup`, `Whole`):

* `final_setup_wp`, `whole_wp`: the registers saved, and the whole-block
  function on the `n = len / 16` whole blocks (`Whole`);
* `final_mid_wp`: if `u = len % 16` bytes are left, the block after the
  registers in `save` zeroed and the whole-block function on it
  (`tail_args_wp`, `tail_call_wp`), which leaves `CIPH_K(Tₙ₊₁)` there and
  `Tₙ₊₂` in `ctr`, and its first `u` bytes XORed into them
  (`Modes.RISCV64.xorLoop_wp`, `tail_xor_wp`); what is left before the
  registers are restored is `Done`;
* `final_end_wp`: the registers restored;
* `final_post`: `Done` gives `Spec.Ctr.CryptFinal`
  (`Proof.Modes.CtrFinal.cryptFinal_of`).

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
the whole-block function's constant time, whose public data, the last 32
bits of the counter block, agree in both runs at both calls: they do on
entry (the contract's leak), and after `n` blocks they are those on entry
plus `n` modulo `2³²`.
-/

@[expose] public section

namespace VG.Proof.AesCtr.RISCV64.Final

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesCtr.RISCV64 (tailArgs tailMoves tailKey zeroSlots finalTail cryptFinal crypt)
open VG.Impl.AesCfb.RISCV64 (finalSaved finalMoves finalSetup finalRestore)
open VG.Proof.AesCfb.RISCV64.Final (fW fR fIv fD fL fS fV fN fU fT fSch fIvR fData fBlk fTail fScr fSv
  fWk fIv0 fBlks svMem Setup Whole Kept finalSat finalFrameSat shr4 shr4_shl4 sub_shl4 cs_of callEntry
  toNat_n eval_u bytesAt_getD blocksAt_frame' svMem_frame saved_slots saved_fits blk_sub tail_sub fN_eq
  fU_eq n_lt u_lt agree_of upd_gpr a1_ofNat)
open VG.Proof.AesCbc (Mode)
open VG.RISCV64.Steps
open VG.Proof.AesCbc.RISCV64 (modeRISCV64 one_toNat)

/-! ## The contract -/

/-- The code's contract, with the arguments `(schedule = a0, rounds = a1,
ctr = a2, data = a3, len = a4, scratch = a5, save = a6)`, `save` of 80
bytes: the data and the counter block as `Spec.Ctr.CryptFinal` says, by AES
with the key schedule it is given; the counter block's last four bytes are
public. -/
def ctrFinalRISCV64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let iv : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2176⟩
    let sv : Region := ⟨s.gpr .a6, 80⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr, sv] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ sched.Disjoint sv ∧
      iv.Disjoint data ∧ iv.Disjoint scr ∧ iv.Disjoint sv ∧
      data.Disjoint scr ∧ data.Disjoint sv ∧ scr.Disjoint sv ∧
      (s.gpr .a0).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + 2176 ≤ 2 ^ 64 ∧
      (s.gpr .a6).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat % 8 = 0 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    Spec.Ctr.CryptFinal (ciphAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) s.mem s'.mem (s.gpr .a2) (s.gpr .a3)
      (s.gpr .a4).toNat
  pub s₁ s₂ :=
    (s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.sp = s₂.sp) ∧
      Spec.Ctr.ctrLeak s₁.mem (s₁.gpr .a2) = Spec.Ctr.ctrLeak s₂.mem (s₂.gpr .a2)

/-- The contract the frame needs: the shared one, with `save`, 80 bytes, as
a seventh argument, and no stack (a call keeps its return address in
`ra`). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract RISCV64.abi Spec.Ctr.aesFinalSig "save" .u64 10 (finalPre RISCV64.abi.ptrBits)
    (finalPost RISCV64.abi.ptrBits) false 0 (some (finalLeak RISCV64.abi.ptrBits))

/-- A state satisfying the precondition. -/
def ctrSat : State := { finalSat with wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x6000, 80⟩] }

theorem final_implies : ctrFinalRISCV64.Implies finalScratchContract := by
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Ctr.aesFinalSig, finalPre, finalPost, finalLeak, Spec.Ctr.ctrLeak, ctrFinalRISCV64, RISCV64.abi,
    RISCV64.argRegs] [ctrSat, finalSat] using ctrSat

/-! ## The arguments, by name -/

section
variable (s₀ : State)

/-- `save`, the registers then the block. -/
abbrev cSv : Region := ⟨fV s₀, 80⟩
/-- The block after the registers in `save`. -/
abbrev cBk : Addr := fV s₀ + BitVec.ofNat 64 64
abbrev cBlk : Region := ⟨cBk s₀, 16⟩

end

/-- The precondition, by name. -/
structure CPre (s₀ : State) : Prop where
  rd : s₀.rd = [fSch s₀]
  wr : s₀.wr = [fIvR s₀, fData s₀, fScr s₀, cSv s₀]
  sch_iv : (fSch s₀).Disjoint (fIvR s₀)
  sch_data : (fSch s₀).Disjoint (fData s₀)
  sch_scr : (fSch s₀).Disjoint (fScr s₀)
  sch_sv : (fSch s₀).Disjoint (cSv s₀)
  iv_data : (fIvR s₀).Disjoint (fData s₀)
  iv_scr : (fIvR s₀).Disjoint (fScr s₀)
  iv_sv : (fIvR s₀).Disjoint (cSv s₀)
  data_scr : (fData s₀).Disjoint (fScr s₀)
  data_sv : (fData s₀).Disjoint (cSv s₀)
  scr_sv : (fScr s₀).Disjoint (cSv s₀)
  iv_wrap : (fIv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (fD s₀).toNat + fL s₀ ≤ 2 ^ 64
  scr_wrap : (fS s₀).toNat + 2176 ≤ 2 ^ 64
  sv_wrap : (fV s₀).toNat + 80 ≤ 2 ^ 64
  sv_al : (fV s₀).toNat % 8 = 0
  rounds : fR s₀ = 10 ∨ fR s₀ = 12 ∨ fR s₀ = 14

theorem CPre.of {s₀ : State} (h : ctrFinalRISCV64.pre s₀) : CPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, _, a14, a15, a16, a17, a18, a19⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a14, a15, a16, a17, a18, a19⟩

/-! ## Regions -/

theorem sv64_sub (s₀ : State) : Region.Sub (fSv s₀) (cSv s₀) := Region.sub_prefix (by decide)
theorem blk_sv_sub (s₀ : State) : Region.Sub (cBlk s₀) (cSv s₀) := Offset.sub_base _ (by decide)

section
variable {s₀ : State} (hp : CPre s₀)
include hp

theorem CPre.blk_tail : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  exact Offset.base_disjoint _ (Nat.le_refl _) (by rw [fN_eq, fU_eq]; omega_arith)

theorem CPre.blk_wrap : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := Nat.mul_div_le (fL s₀) 16; rw [fN_eq]; omega_arith

theorem CPre.sched_sub : Region.Sub ⟨fW s₀, 16 * (fR s₀ + 1)⟩ (fSch s₀) :=
  Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega_using [h])

theorem CPre.sched_len : 16 * (fR s₀ + 1) ≤ 2 ^ 64 := by
  rcases hp.rounds with h | h | h <;> omega_using [h]

end

/-- The save changes only `save`. -/
theorem svMem_frame' (s₀ : State) : Frame [cSv s₀] s₀.mem (svMem s₀) :=
  (svMem_frame s₀).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨cSv s₀, by simp, sv64_sub s₀⟩

/-- The slots of the registers miss the block. -/
theorem slot_blk (s₀ : State) :
    ∀ p ∈ finalSaved, Region.Disjoint ⟨fV s₀ + BitVec.ofNat 64 p.2, 8⟩ (cBlk s₀) := by
  intro p hp'
  have := saved_slots p hp'
  exact Offset.disjoint _ (.inl (by omega_using [this])) (by omega_using [this]) (by decide)

/-! ## Saving the registers, and the whole blocks -/

set_option linter.unusedSimpArgs false in
theorem final_setup_wp {s₀ : State} (hp : CPre s₀) : WP isa (.block finalSetup) s₀ (Setup s₀) := by
  obtain hw : ∀ p ∈ finalSaved, InRegions s₀.wr (s₀.gpr .a6 + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    rw [hp.wr]
    have := saved_slots p hp'
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega_using [this]) (by omega_using [this])⟩
  show WP isa (.block (Spill.saveCode .a6 finalSaved ++ finalMoves)) _ _
  refine Spill.save_ok hp.sv_al saved_fits hw ?_
  unfold finalMoves Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_srl (by decide) fun s₆ u₆ => wp_sll (by decide) fun s₇ u₇ => wp_add fun s₈ u₈ =>
    wp_sub fun s₉ u₉ => wp_mv fun s₁₀ u₁₀ => WP.block_nil ?_
  exact {
    s1 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    s4 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    s5 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    s2 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; rw [shr4_shl4]
    s3 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; rw [shr4_shl4, sub_shl4]
    s6 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    s7 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a0 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a1 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a2 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a3 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a4 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; rw [shr4]
    a5 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    kept := fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    sp := by rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
    mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    rd := by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr] }

theorem crypt_noFrames : crypt.noFrames = true := by
  simp only [crypt, Impl.AesCbc.RISCV64.whole, Impl.AesCtr.RISCV64.body, Impl.AesCtr.RISCV64.ctrCall,
    Code.noFrames, Bool.and_self, Bool.and_true, Bool.true_and]
  exact ctr32_noFrames

/-- The whole-block function's contract: `modeRISCV64 ctrMode`, with the
last 32 bits of the counter block public. -/
abbrev wholeK : Contract isa := { modeRISCV64 AesCtr.ctrMode with pub := ctrPub }

theorem whole_pre {s₀ : State} (hp : CPre s₀) {s : State} (h : Setup s₀ s) :
    wholeK.pre (s.callEntry.withRegions [fSch s₀] [fIvR s₀, fBlk s₀, fScr s₀]) ∧
      Covers ([fSch s₀] ++ [fIvR s₀, fBlk s₀, fScr s₀]) (s.rd ++ s.wr) ∧
      Covers [fIvR s₀, fBlk s₀, fScr s₀] s.wr := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      callEntry s (by decide : Reg.a0 ∉ linkRegs), callEntry s (by decide : Reg.a1 ∉ linkRegs),
      callEntry s (by decide : Reg.a2 ∉ linkRegs), callEntry s (by decide : Reg.a3 ∉ linkRegs),
      callEntry s (by decide : Reg.a4 ∉ linkRegs), callEntry s (by decide : Reg.a5 ∉ linkRegs),
      h.a0, h.a1, h.a2, h.a3, h.a4, h.a5, toNat_n]
    exact ⟨trivial, trivial, hp.sch_iv, hp.sch_data.sub_right (blk_sub s₀), hp.sch_scr,
      hp.iv_data.sub_right (blk_sub s₀), hp.iv_scr, hp.data_scr.sub_left (blk_sub s₀),
      hp.iv_wrap, hp.blk_wrap, hp.scr_wrap, hp.rounds⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fData s₀, by simp, 0, by simp, by simpa using Nat.mul_div_le (fL s₀) 16⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fData s₀, by simp, 0, by simp, by simpa using Nat.mul_div_le (fL s₀) 16⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩

/-- The schedule, the counter block and the whole blocks once the registers
are saved, as on entry. -/
theorem sv_bytes {s₀ : State} (hp : CPre s₀) :
    bytesAt (svMem s₀) (fW s₀) (16 * (fR s₀ + 1)) = fWk s₀ ∧ bytesAt (svMem s₀) (fIv s₀) 16 = fIv0 s₀ ∧
      Spec.Cbc.blocksAt (svMem s₀) (fD s₀) (fN s₀) = fBlks s₀ := by
  obtain ef := svMem_frame' s₀
  exact ⟨Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.sch_sv.sub_left hp.sched_sub) hp.sched_len,
    Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv) (by decide),
    blocksAt_frame' ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.data_sv.sub_left (blk_sub s₀))⟩

theorem whole_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Setup s₀ s) :
    WP isa (.call "vg_aes_ctr_core" crypt) s (Whole AesCtr.ctrMode s₀) := by
  obtain ⟨eW, eIv, eB⟩ := sv_bytes hp
  obtain ⟨hpre, hc, hw⟩ := whole_pre hp h
  refine WP.call (k := wholeK) crypt_correct (rd := [fSch s₀]) (wr := [fIvR s₀, fBlk s₀, fScr s₀]) hpre
    hc hw ?_ crypt_noFrames
  intro s' rd' wr' sp' fr' cs' _ post₂
  rw [h.mem] at fr'
  simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry s (by decide : Reg.a0 ∉ linkRegs), callEntry s (by decide : Reg.a1 ∉ linkRegs),
    callEntry s (by decide : Reg.a2 ∉ linkRegs), callEntry s (by decide : Reg.a3 ∉ linkRegs),
    callEntry s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4,
    toNat_n, h.mem, eW, eIv, eB] at post₂
  exact ⟨by rw [cs_of cs' .s1 (by simp), h.s1], by rw [cs_of cs' .s4 (by simp), h.s4],
    by rw [cs_of cs' .s5 (by simp), h.s5], by rw [cs_of cs' .s2 (by simp), h.s2],
    by rw [cs_of cs' .s3 (by simp), h.s3], by rw [cs_of cs' .s6 (by simp), h.s6],
    by rw [cs_of cs' .s7 (by simp), h.s7],
    fun r hr => by rw [cs_of cs' r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp', h.sp], by rw [rd', h.rd], by rw [wr', h.wr], fr', post₂.1, post₂.2⟩

/-! ## The partial last block: its arguments -/

/-- Two zeroed doublewords make 16 zero bytes. -/
theorem zero_bytes (m : Mem) (B : Addr) :
    bytesAt ((m.writeW B (0 : BitVec 64)).writeW (B + BitVec.ofNat 64 8) (0 : BitVec 64)) B 16 =
      List.replicate 16 0 := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ _
  obtain hi : i < 16 := by simpa [bytesAt] using h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate, Mem.writeW, Mem.write,
    Mem.sub_ofNat_toNat B (show i < 2 ^ 64 by omega_using [hi]), Offset.sub_toNat' B (show 8 < 2 ^ 64 by decide)
      (show i < 2 ^ 64 by omega_using [hi])]
  by_cases h8 : 8 ≤ i
  · rw [ite_eq_left h8, ite_eq_left (by omega_using [hi])]; simp
  · rw [ite_eq_right h8, ite_eq_right (by omega_using []), ite_eq_left (by omega_using [h8])]; simp

/-! ## Frames -/

section
variable (s₀ : State)

/-- What the function writes after saving the registers, with the whole
blocks rather than the data. -/
abbrev cW1 : List Region := [fIvR s₀, fBlk s₀, fScr s₀, cBlk s₀]
/-- What the function writes after saving the registers. -/
abbrev cW : List Region := [fIvR s₀, fData s₀, fScr s₀, cBlk s₀]
/-- What the function writes. -/
abbrev cBig : List Region := [fIvR s₀, fData s₀, fScr s₀, cSv s₀]

end

theorem cW1_cW {s₀ : State} {m : Mem} (hf : Frame (cW1 s₀) (svMem s₀) m) : Frame (cW s₀) (svMem s₀) m :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨fData s₀, by simp, blk_sub s₀⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem whole_cW1 {M : Mode} {s₀ s : State} (h : Whole M s₀ s) : Frame (cW1 s₀) (svMem s₀) s.mem :=
  h.frame.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp [h]

theorem big_of {s₀ : State} {m : Mem} (hf : Frame (cW s₀) (svMem s₀) m) : Frame (cBig s₀) s₀.mem m :=
  ((svMem_frame' s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
    (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨cSv s₀, by simp, blk_sv_sub s₀⟩)

theorem CPre.sched_big {s₀ : State} (hp : CPre s₀) :
    ∀ r ∈ cBig s₀, (⟨fW s₀, 16 * (fR s₀ + 1)⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left hp.sched_sub
  · exact hp.sch_data.sub_left hp.sched_sub
  · exact hp.sch_scr.sub_left hp.sched_sub
  · exact hp.sch_sv.sub_left hp.sched_sub

/-! ## The partial last block -/

/-- What zeroing the block and setting up the arguments leaves. -/
structure TArgs (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = fW s₀
  a1 : s.gpr .a1 = s₀.gpr .a1
  a2 : s.gpr .a2 = fIv s₀
  a3 : s.gpr .a3 = cBk s₀
  a4 : s.gpr .a4 = BitVec.ofNat 64 1
  a5 : s.gpr .a5 = fS s₀
  s2 : s.gpr .s2 = fT s₀
  s3 : s.gpr .s3 = BitVec.ofNat 64 (fU s₀)
  s7 : s.gpr .s7 = fV s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀)
  zero : bytesAt s.mem (cBk s₀) 16 = List.replicate 16 0

theorem zero_frame (s₀ : State) (m : Mem) (g : Reg → BitVec 64) :
    Frame [cBlk s₀] m (Spill.saveMem m (fV s₀) g zeroSlots) :=
  Spill.saveMem_frame (lo := 64) (n := 16) (fun p hp' => by
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> decide) (by decide) m _ g

set_option linter.unusedSimpArgs false in
theorem tail_args_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole AesCtr.ctrMode s₀ s) :
    WP isa (.block tailArgs) s (TArgs s₀) := by
  obtain f₁ := whole_cW1 h
  show WP isa (.block (.li .t0 0 :: (Spill.saveCode .s7 zeroSlots ++ tailMoves))) _ _
  refine wp_li (imm := 0) (by decide) fun s₁ z => ?_
  obtain h7 : s₁.gpr .s7 = fV s₀ := by rw [z.other _ (by decide), h.s7]
  obtain hw : ∀ p ∈ zeroSlots, InRegions s₁.wr (s₁.gpr .s7 + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    rw [z.wr, h.wr, hp.wr, h7]
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact ⟨cSv s₀, by simp, Offset.contains_base _ (by decide) (by have := hp.sv_wrap; omega_using [])⟩
    · exact ⟨cSv s₀, by simp, Offset.contains_base _ (by decide) (by have := hp.sv_wrap; omega_using [])⟩
  refine Spill.save_ok (by rw [h7]; exact hp.sv_al) (by decide) hw ?_
  unfold tailMoves Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_addi (imm := 64) (by decide) fun s₅ u₅ =>
    wp_li (imm := 1) (by decide) fun s₆ u₆ => wp_mv fun s₇ u₇ => WP.block_nil ?_
  have c (r : Reg) (hr : r = .s0 ∨ r = .s1 ∨ r = .s2 ∨ r = .s3 ∨ r = .s4 ∨ r = .s5 ∨ r = .s6 ∨ r = .s7 ∨
      r = .s8 ∨ r = .s9 ∨ r = .s10 ∨ r = .s11) : s₇.gpr r = s.gpr r := by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq,
        ↓reduceIte] <;> exact z.other _ (by decide)
  obtain sp : s₇.sp = s.sp := by
    rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, show ({ s₁ with mem := _ } : State).sp = s₁.sp from rfl, z.sp]
  obtain rd : s₇.rd = s.rd := by
    rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, show ({ s₁ with mem := _ } : State).rd = s₁.rd from rfl, z.rd]
  obtain wr : s₇.wr = s.wr := by
    rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, show ({ s₁ with mem := _ } : State).wr = s₁.wr from rfl, z.wr]
  obtain hm : s₇.mem = Spill.saveMem s.mem (fV s₀) s₁.gpr zeroSlots := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, h7]
    show Spill.saveMem s₁.mem _ _ _ = _
    rw [z.mem]
  obtain fz : Frame [cBlk s₀] s.mem s₇.mem := by rw [hm]; exact zero_frame s₀ _ _
  obtain ivZ : ∀ r ∈ [cBlk s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv.sub_right (blk_sv_sub s₀)
  obtain blkZ : ∀ r ∈ [cBlk s₀], (fBlk s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
  obtain g7 : ({ s₁ with mem := Spill.saveMem s₁.mem (s₁.gpr .s7) s₁.gpr zeroSlots } : State).gpr = s₁.gpr := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [c .s2 (by simp), h.s2], by rw [c .s3 (by simp), h.s3],
    by rw [c .s7 (by simp), h.s7],
    fun r hr => by rw [c r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp, h.sp], by rw [rd, h.rd], by rw [wr, h.wr], ?_, ?_, ?_, ?_⟩
  · simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte,
      g7]
    rw [z.other _ (by decide), h.s1]
  · simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte,
      g7]
    rw [z.other _ (by decide), h.s4]
  · simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte,
      g7]
    rw [z.other _ (by decide), h.s5]
  · simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte,
      g7]
    rw [h7]
  · simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte]
  · simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte,
      g7]
    rw [z.other _ (by decide), h.s6]
  · exact f₁.trans (fz.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [blocksAt_frame' fz blkZ]; exact h.blocks
  · rw [Proof.Cmac.bytesAt_frame fz ivZ (by decide), h.iv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]
  · rw [hm, show Spill.saveMem s.mem (fV s₀) s₁.gpr zeroSlots =
        ((s.mem.writeW (cBk s₀) (s₁.gpr .t0)).writeW (cBk s₀ + BitVec.ofNat 64 8) (s₁.gpr .t0)) by
      simp only [Spill.saveMem, zeroSlots, Offset.add_add], z.gpr]
    exact zero_bytes _ _

theorem cBk_toNat {s₀ : State} (hp : CPre s₀) : (cBk s₀).toNat = (fV s₀).toNat + 64 := by
  have := hp.sv_wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide), Nat.mod_eq_of_lt (by omega_using [this])]

theorem tail_pre {s₀ : State} (hp : CPre s₀) {s : State} (h : TArgs s₀ s) :
    wholeK.pre (s.callEntry.withRegions [fSch s₀] [fIvR s₀, cBlk s₀, fScr s₀]) ∧
      Covers ([fSch s₀] ++ [fIvR s₀, cBlk s₀, fScr s₀]) (s.rd ++ s.wr) ∧
      Covers [fIvR s₀, cBlk s₀, fScr s₀] s.wr := by
  obtain bs := blk_sv_sub s₀
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      callEntry s (by decide : Reg.a0 ∉ linkRegs), callEntry s (by decide : Reg.a1 ∉ linkRegs),
      callEntry s (by decide : Reg.a2 ∉ linkRegs), callEntry s (by decide : Reg.a3 ∉ linkRegs),
      callEntry s (by decide : Reg.a4 ∉ linkRegs), callEntry s (by decide : Reg.a5 ∉ linkRegs),
      h.a0, h.a1, h.a2, h.a3, h.a4, h.a5, one_toNat, Nat.mul_one]
    have := hp.sv_wrap
    exact ⟨trivial, trivial, hp.sch_iv, hp.sch_sv.sub_right bs, hp.sch_scr, hp.iv_sv.sub_right bs, hp.iv_scr,
      (hp.scr_sv.sub_right bs).symm, hp.iv_wrap, by rw [cBk_toNat hp]; omega_using [this], hp.scr_wrap, hp.rounds⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨cSv s₀, by simp, 64, by simp, by simp⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨cSv s₀, by simp, 64, by simp, by simp⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩

/-- What the call on the block leaves. -/
structure TCall (s₀ s : State) : Prop where
  s2 : s.gpr .s2 = fT s₀
  s3 : s.gpr .s3 = BitVec.ofNat 64 (fU s₀)
  s7 : s.gpr .s7 = fV s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (Spec.Ctr.next (fIv0 s₀) (fN s₀)) 1
  out : bytesAt s.mem (cBk s₀) 16 = Spec.Cbc.aesWith (fR s₀) (fWk s₀) (Spec.Ctr.next (fIv0 s₀) (fN s₀))

theorem tail_call_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : TArgs s₀ s) :
    WP isa (.call "vg_aes_ctr_core" crypt) s (TCall s₀) := by
  obtain ⟨hpre, hc, hw⟩ := tail_pre hp h
  obtain big := big_of (cW1_cW h.frame)
  obtain eW : bytesAt s.mem (fW s₀) (16 * (fR s₀ + 1)) = fWk s₀ :=
    Proof.Cmac.bytesAt_frame big hp.sched_big hp.sched_len
  refine WP.call (k := wholeK) crypt_correct (rd := [fSch s₀]) (wr := [fIvR s₀, cBlk s₀, fScr s₀]) hpre
    hc hw ?_ crypt_noFrames
  intro s' rd' wr' sp' fr' cs' _ post₂
  simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry s (by decide : Reg.a0 ∉ linkRegs), callEntry s (by decide : Reg.a1 ∉ linkRegs),
    callEntry s (by decide : Reg.a2 ∉ linkRegs), callEntry s (by decide : Reg.a3 ∉ linkRegs),
    callEntry s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4,
    one_toNat, eW, h.ctr, AesCtr.ctrMode_out, AesCtr.ctrMode_chain, AesCbc.length_blocksAt] at post₂
  obtain fc : Frame (cW1 s₀) s.mem s'.mem := fr'.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨by rw [cs_of cs' .s2 (by simp), h.s2], by rw [cs_of cs' .s3 (by simp), h.s3],
    by rw [cs_of cs' .s7 (by simp), h.s7],
    fun r hr => by rw [cs_of cs' r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp', h.sp], by rw [rd', h.rd], by rw [wr', h.wr], h.frame.trans fc, ?_, post₂.2, ?_⟩
  · rw [blocksAt_frame' fr' fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.iv_data.symm.sub_left (blk_sub s₀)
      · exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
      · exact hp.data_scr.sub_left (blk_sub s₀)]
    exact h.blocks
  · exact Modes.CtrFinal.bytesAt_of_blocksAt_one (aesWith_length _ _) h.zero post₂.1

/-- What the function leaves before restoring the registers. -/
structure Done (s₀ s : State) : Prop where
  s7 : s.gpr .s7 = fV s₀
  kept : Kept s₀ s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q) ^^^
    (Spec.Cbc.aesWith (fR s₀) (fWk s₀) (Spec.Ctr.next (fIv0 s₀) (fN s₀))).getD q 0
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (if fU s₀ = 0 then fN s₀ else fN s₀ + 1)

theorem done_of_zero {s₀ s : State} (h : Whole AesCtr.ctrMode s₀ s) (hu : fU s₀ = 0) : Done s₀ s :=
  ⟨h.s7, h.kept, h.rd, h.wr, cW1_cW (whole_cW1 h), h.blocks, fun q hq => absurd hq (by omega_using [hu]), by
    rw [ite_eq_left hu, h.iv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]⟩

theorem toNat_tail {s₀ : State} (hp : CPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  obtain eN := fN_eq s₀
  obtain eU := fU_eq s₀
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

open VG.Proof.Modes.RISCV64 (XPre XInv xorLoop_wp xf)

theorem tail_xor_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : TCall s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block tailKey) (.loop (.block Impl.Modes.RISCV64.xorStep) (.nonzero .s3))) s (Done s₀) := by
  refine WP.seq (wp_addi (imm := 64) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain hU := u_lt s₀
  obtain hT := toNat_tail hp hu
  obtain hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_wrap
  have hVw := hp.sv_wrap
  obtain hB := cBk_toNat hp
  obtain eN := fN_eq s₀
  obtain eU := fU_eq s₀
  obtain xp : XPre s₁ (cBk s₀) (fT s₀) (fU s₀) := {
    fK := by omega_using [hU, hVw, hB]
    fR := by omega_using [hT, hDw, eN, eU]
    disj := (((hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)).sub_right
      (Region.sub_prefix (by omega_using [hU]))).symm
    rdK := fun q hq => by
      rw [u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]
      refine ⟨cSv s₀, by simp, ?_⟩
      rw [Offset.add_add]
      exact Offset.contains_base _ (by omega_using [hU, hq]) (by omega_using [hU, hq])
    wrR := fun q hq => by
      rw [u₁.wr, h.wr, hp.wr]
      refine ⟨fData s₀, by simp, ?_⟩
      rw [show fT s₀ + BitVec.ofNat 64 q = fD s₀ + BitVec.ofNat 64 (16 * fN s₀ + q) from Offset.add_add _ _ _]
      exact Offset.contains_base _ (by omega_using [eN, eU, hq]) (by omega_using [hU, hT, hq]) }
  obtain x0 : XInv s₁ (cBk s₀) (fT s₀) (fU s₀) 0 s₁ := {
    t2 := by rw [u₁.gpr, h.s7]; exact (BitVec.add_zero _).symm
    s2 := by rw [u₁.other _ (by decide), h.s2]; exact (BitVec.add_zero _).symm
    s3 := by rw [u₁.other _ (by decide), h.s3, Nat.sub_zero]
    lt := by omega_using [hu]
    mem := (Proof.Modes.over_zero _ _ _).symm
    rd := rfl
    wr := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (xorLoop_wp xp x0) fun s' d => ?_
  obtain tailD : ∀ r ∈ cW1 s₀, (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.iv_data.sub_right (tail_sub s₀)).symm
    · exact hp.blk_tail.symm
    · exact hp.data_scr.sub_left (tail_sub s₀)
    · exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)
  obtain tailS : ∀ r ∈ [fSv s₀], (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (sv64_sub s₀)
  obtain hlen : (fTail s₀).len ≤ 2 ^ 64 := by show fU s₀ ≤ 2 ^ 64; omega_using [hU]
  obtain ivT : ∀ r ∈ [fTail s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.iv_data.sub_right (tail_sub s₀)
  have g (r : Reg) (hr : r = .s7 ∨ r = .s0 ∨ r = .s8 ∨ r = .s9 ∨ r = .s10 ∨ r = .s11) : s'.gpr r = s.gpr r := by
    rw [d.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      u₁.other _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  obtain fr : Frame [fTail s₀] s.mem s'.mem := by
    rw [d.mem, u₁.mem]; exact Proof.Modes.over_frame _ _ _ _
  refine ⟨by rw [g .s7 (by simp), h.s7], fun r hr => by
      rw [g r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [d.rd, u₁.rd, h.rd], by rw [d.wr, u₁.wr, h.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · exact (cW1_cW h.frame).trans (fr.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [blocksAt_frame' fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail]
    exact h.blocks
  · rw [d.mem, Proof.Modes.over_at hq (by omega_using [hU]), xf, u₁.mem, h.frame.bytes tailD hlen hq,
      (svMem_frame s₀).bytes tailS hlen hq,
      ← bytesAt_getD s.mem (cBk s₀) (show q < 16 by omega_using [hU, hq]), h.out]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame fr ivT (by decide), h.ctr, ← AesCtr.next_add]

theorem final_mid_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole AesCtr.ctrMode s₀ s) :
    WP isa (.ite (.zero .s3) (.block []) finalTail) s (Done s₀) := by
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [eval_u h, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [eval_u h, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (tail_args_wp hp h) fun _ h₁ =>
      WP.seq (WP.mono (tail_call_wp hp h₁) fun _ h₂ => tail_xor_wp hp h₂ hu))

/-! ## Restoring the registers -/

theorem final_end_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Done s₀ s) :
    WP isa (.block finalRestore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ s'.mem = s.mem := by
  obtain hs : Spill.Saved (fV s₀) s₀.gpr finalSaved s.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (fV s₀) s₀.gpr).frame h.frame fun p hp' r hr => by
      obtain hsub : Region.Sub ⟨fV s₀ + BitVec.ofNat 64 p.2, 8⟩ (cSv s₀) :=
        Offset.sub_base _ (by have := saved_slots p hp'; omega_using [this])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.iv_sv.symm.sub_left hsub
      · exact hp.data_sv.symm.sub_left hsub
      · exact hp.scr_sv.symm.sub_left hsub
      · exact slot_blk s₀ p hp'
  show WP isa (.block (Spill.restoreCode .s7 finalSaved)) _ _
  refine WP.mono (Spill.restore_wp hp.sv_al h.s7 saved_fits (by decide) (fun p hp' => ?_) hs)
    fun s' r => ⟨fun q hq => r.gpr_of ?_, r.gpr (.ra, 0) (by decide), r.mem⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    have := saved_slots p hp'
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega_using [this]) (by have := hp.sv_wrap; omega_arith)⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact .inl (by decide)
      | exact .inr (h.kept _ (by simp))

/-! ## The whole function -/

theorem final_wp {s₀ : State} (hp : CPre s₀) :
    WP isa cryptFinal s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        ∃ s₁, Done s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (final_setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (final_mid_wp hp h₂) fun s₃ h₃ => ?_)
  exact WP.mono (final_end_wp hp h₃) fun _ ⟨g, ra, m⟩ => ⟨g, ra, s₃, h₃, m⟩

/-- `Spec.Ctr.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done s₀ s₁) (hm : s'.mem = s₁.mem) : ctrFinalRISCV64.post s₀ s' := by
  show Spec.Ctr.CryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
  exact Modes.CtrFinal.cryptFinal_of (aesWith_length _ _) (by rw [hm]; exact h.blocks)
    (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.ctr)

theorem final_correct (s : State) (hs : ctrFinalRISCV64.pre s) :
    ∃ t s', Exec isa cryptFinal s t s' ∧ abiPreserved s s' ∧ ctrFinalRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, s₁, h₁, hm⟩ := final_wp (CPre.of hs)
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, final_post h₁ hm⟩

/-! ## Constant time -/

/-- Counter blocks whose last 32 bits agree still do after `k` increments. -/
theorem lo32_next_of {t t' : List Byte} (ht : t.length = 16) (ht' : t'.length = 16)
    (h : AesCtr.lo32 t = AesCtr.lo32 t') (k : Nat) :
    AesCtr.lo32 (Spec.Ctr.next t k) = AesCtr.lo32 (Spec.Ctr.next t' k) := by
  rw [AesCtr.lo32_next ht, AesCtr.lo32_next ht']
  unfold AesCtr.lo32 at h
  omega_using [h]

theorem setup_taint : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6])
    (.block finalSetup) h).isSome = true := ⟨_, by taint_decide⟩

theorem tailArgs_taint : ∃ h, (taint.check (Taint.ofRegs [.s1, .s4, .s5, .s6, .s7])
    (.block tailArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (Taint.ofRegs [.s7, .s2, .s3])
    (.seq (.block tailKey) (.loop (.block Impl.Modes.RISCV64.xorStep) (.nonzero .s3))) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.s7]) (.block finalRestore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem final_rel {s₀ s₀' : State} (h0 : ctrFinalRISCV64.pre s₀) (h0' : ctrFinalRISCV64.pre s₀')
    (hq : ctrFinalRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') cryptFinal fun _ _ => True := by
  obtain hp := CPre.of h0
  obtain hp' := CPre.of h0'
  obtain ⟨⟨qW, qR, qIv, qD, qL, qS, qV, qSp⟩, qLk⟩ := hq
  obtain qU : fU s₀ = fU s₀' := by simp only [fU, fL, qL]
  obtain qN : fN s₀ = fN s₀' := by simp only [fN, fL, qL]
  obtain qT : fT s₀ = fT s₀' := by simp only [fT, fD, qD, qN]
  obtain qLo : AesCtr.lo32 (fIv0 s₀) = AesCtr.lo32 (fIv0 s₀') :=
    AesCtr.lo32_of_leak (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _) qLk
  -- The registers saved and the arguments set up.
  obtain ⟨_, t₁⟩ := setup_taint
  obtain r₁ := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of qSp fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) t₁).wp
    (F₁ := Setup s₀) (F₂ := Setup s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨final_setup_wp hp, final_setup_wp hp'⟩
  -- The whole blocks.
  obtain r₂ := (RelCT.callEx (k := wholeK) (n := "vg_aes_ctr_core") crypt_correct crypt_ct
    (P := fun a b => Setup s₀ a ∧ Setup s₀' b) fun a b ⟨ha, hb⟩ => by
      obtain ⟨pa, ca, wa⟩ := whole_pre hp ha
      obtain ⟨pb, cb, wb⟩ := whole_pre hp' hb
      refine ⟨_, _, _, _, pa, pb, ⟨?_, ?_⟩, ca, wa, cb, wb⟩
      · simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
          callEntry a (by decide : Reg.a0 ∉ linkRegs), callEntry a (by decide : Reg.a1 ∉ linkRegs),
          callEntry a (by decide : Reg.a2 ∉ linkRegs), callEntry a (by decide : Reg.a3 ∉ linkRegs),
          callEntry a (by decide : Reg.a4 ∉ linkRegs), callEntry a (by decide : Reg.a5 ∉ linkRegs),
          callEntry b (by decide : Reg.a0 ∉ linkRegs), callEntry b (by decide : Reg.a1 ∉ linkRegs),
          callEntry b (by decide : Reg.a2 ∉ linkRegs), callEntry b (by decide : Reg.a3 ∉ linkRegs),
          callEntry b (by decide : Reg.a4 ∉ linkRegs), callEntry b (by decide : Reg.a5 ∉ linkRegs),
          ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.sp, hb.a0, hb.a1, hb.a2, hb.a3, hb.a4, hb.a5, hb.sp]
        rw [fW, fW, fIv, fIv, fD, fD, fS, fS, qW, qR, qIv, qD, qS, qSp, qN]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [AesCbc.RISCV64.iv0, AesCbc.RISCV64.Iv, State.withRegions_gpr, State.withRegions_mem,
          State.callEntry_mem, callEntry a (by decide : Reg.a2 ∉ linkRegs),
          callEntry b (by decide : Reg.a2 ∉ linkRegs), ha.a2, hb.a2, ha.mem, hb.mem]
        rw [(sv_bytes hp).2.1, (sv_bytes hp').2.1]
        exact qLo).wp
    (F₁ := Whole AesCtr.ctrMode s₀) (F₂ := Whole AesCtr.ctrMode s₀')
    fun a b h => ⟨whole_wp hp h.1, whole_wp hp' h.2⟩
  -- The partial last block.
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b)
      finalTail fun a b => Done s₀ a ∧ Done s₀' b := by
    obtain hu' : fU s₀' ≠ 0 := qU ▸ hu
    obtain ⟨_, t₃⟩ := tailArgs_taint
    obtain a₁ := (RelCT.taint (A := taint)
      (P := fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b) _
      (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, qSp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [h.1.s1, h.2.s1, fW, fW, qW]
        · rw [h.1.s4, h.2.s4, qR]
        · rw [h.1.s5, h.2.s5, fIv, fIv, qIv]
        · rw [h.1.s6, h.2.s6, fS, fS, qS]
        · rw [h.1.s7, h.2.s7, fV, fV, qV]) t₃).wp
      (F₁ := TArgs s₀) (F₂ := TArgs s₀')
      fun a b h => ⟨tail_args_wp hp h.1, tail_args_wp hp' h.2⟩
    obtain a₂ := (RelCT.callEx (k := wholeK) (n := "vg_aes_ctr_core") crypt_correct crypt_ct
      (P := fun a b => TArgs s₀ a ∧ TArgs s₀' b) fun a b ⟨ha, hb⟩ => by
        obtain ⟨pa, ca, wa⟩ := tail_pre hp ha
        obtain ⟨pb, cb, wb⟩ := tail_pre hp' hb
        refine ⟨_, _, _, _, pa, pb, ⟨?_, ?_⟩, ca, wa, cb, wb⟩
        · simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
            callEntry a (by decide : Reg.a0 ∉ linkRegs), callEntry a (by decide : Reg.a1 ∉ linkRegs),
            callEntry a (by decide : Reg.a2 ∉ linkRegs), callEntry a (by decide : Reg.a3 ∉ linkRegs),
            callEntry a (by decide : Reg.a4 ∉ linkRegs), callEntry a (by decide : Reg.a5 ∉ linkRegs),
            callEntry b (by decide : Reg.a0 ∉ linkRegs), callEntry b (by decide : Reg.a1 ∉ linkRegs),
            callEntry b (by decide : Reg.a2 ∉ linkRegs), callEntry b (by decide : Reg.a3 ∉ linkRegs),
            callEntry b (by decide : Reg.a4 ∉ linkRegs), callEntry b (by decide : Reg.a5 ∉ linkRegs),
            ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.sp, hb.a0, hb.a1, hb.a2, hb.a3, hb.a4, hb.a5, hb.sp]
          rw [fW, fW, fIv, fIv, cBk, cBk, fV, fV, fS, fS, qW, qR, qIv, qV, qS, qSp]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
        · simp only [AesCbc.RISCV64.iv0, AesCbc.RISCV64.Iv, State.withRegions_gpr, State.withRegions_mem,
            State.callEntry_mem, callEntry a (by decide : Reg.a2 ∉ linkRegs),
            callEntry b (by decide : Reg.a2 ∉ linkRegs), ha.a2, hb.a2]
          rw [ha.ctr, hb.ctr, qN]
          exact lo32_next_of (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _) qLo _).wp
      (F₁ := TCall s₀) (F₂ := TCall s₀') fun a b h => ⟨tail_call_wp hp h.1, tail_call_wp hp' h.2⟩
    obtain ⟨_, t₄⟩ := xor_taint
    obtain a₃ := (RelCT.taint (A := taint) (P := fun a b => TCall s₀ a ∧ TCall s₀' b) _
      (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, qSp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.s7, h.2.s7, fV, fV, qV]
        · rw [h.1.s2, h.2.s2, qT]
        · rw [h.1.s3, h.2.s3, qU]) t₄).wp
      (F₁ := Done s₀) (F₂ := Done s₀')
      fun a b h => ⟨tail_xor_wp hp h.1 hu, tail_xor_wp hp' h.2 hu'⟩
    exact (a₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((a₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq (a₃.mono (fun _ _ h => h) fun _ _ h => h.2))
  obtain r₃ : RelCT isa (fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b)
      (.ite (.zero .s3) (.block []) finalTail) (fun a b => Done s₀ a ∧ Done s₀' b) := by
    refine RelCT.ite (fun a b h => by rw [eval_u h.1, eval_u h.2, qU]) ?_ ?_
    · refine RelCT.block_nil fun a b h => ?_
      obtain h0 : fU s₀ = 0 := by
        have := h.2; rw [eval_u h.1.1] at this; simpa using this
      exact ⟨done_of_zero h.1.1 h0, done_of_zero h.1.2 (qU ▸ h0)⟩
    · refine (RelCT.exists_ fun (hu : fU s₀ ≠ 0) => tail hu).mono
        (fun a b h => ⟨?_, h.1.1, h.1.2⟩) fun _ _ h => h
      have := h.2; rw [eval_u h.1.1] at this; simpa using this
  obtain r₃' := r₃.wp (F₁ := fun (s : State) => s.sp = s₀.sp) (F₂ := fun (s : State) => s.sp = s₀'.sp)
    fun a b h =>
      ⟨WP.mono (AesCbc.RISCV64.wp_sp (final_mid_wp hp h.1)) fun _ x => x.2.trans h.1.sp,
        WP.mono (AesCbc.RISCV64.wp_sp (final_mid_wp hp' h.2)) fun _ x => x.2.trans h.2.sp⟩
  -- The registers restored.
  obtain ⟨_, t₅⟩ := restore_taint
  obtain r₄ := RelCT.taint (A := taint) (P := fun a b => (Done s₀ a ∧ Done s₀' b) ∧
      a.sp = s₀.sp ∧ b.sp = s₀'.sp) _
    (fun a b h => agree_of (by rw [h.2.1, h.2.2, qSp]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.s7, h.1.2.s7, fV, fV, qV]) t₅
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (r₃'.seq r₄))

theorem final_ct : ConstantTime isa ctrFinalRISCV64.pre ctrFinalRISCV64.pub cryptFinal :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem cryptFinal_verified : Verified RISCV64.target cryptFinal finalScratchContract :=
  Verified.of_correct final_correct final_ct final_implies

/-! ## With `save` on the stack

The final function has six argument words, so `save` is its seventh, in
`a6`: it runs its code in a frame of 80 bytes on the stack
(`withStackScratchWiped`), `save`'s 80 bytes (the registers, then the block
that held the last output block), which it zeroes before returning. The
code's calls use no stack, so 80 in all. -/

theorem frameSat_pre : ∃ s, (finalRoundsContract RISCV64.abi 80).pre s := by
  implies_sat [finalRoundsContract, Spec.Ctr.aesFinalSig, finalPre, finalPost, RISCV64.abi,
    RISCV64.argRegs] [finalFrameSat, finalSat] using finalFrameSat

theorem cryptFinal_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchWiped 80 .a6 10 cryptFinal)
      (finalRoundsContract RISCV64.abi 80) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Ctr.aesFinalSig) (nm := "save") (e := .u64) (n := 10)
    (pre := finalPre RISCV64.abi.ptrBits) (post := finalPost RISCV64.abi.ptrBits) (wa := false)
    (leak := some (finalLeak RISCV64.abi.ptrBits))
    (stack := 0) (bytes := 80) (words := 10) cryptFinal_verified (by decide) (by decide) (by decide)
    (finalPost_localOut _) frameSat_pre

end VG.Proof.AesCtr.RISCV64.Final
