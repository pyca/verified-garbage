module
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SubState
public import VerifiedGarbage.Impl.Bignum.Arm.SubModBuffers

import VerifiedGarbage.Proof.Bignum.Arm.SubModControls
import VerifiedGarbage.Proof.Bignum.Arm.SubModMath
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Bignum.Arm.ProductRowMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Exact modular subtraction through the shared native arithmetic loops -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem subModBuffers_ok (s : State) {base : BitVec 32} {size o a b m n : Nat}
    (ctx : SubCtx s base size o a b n) (row : RowCtx s base size o m n)
    (hn : 0 < n) (space : o + 4 * (n + 2) ≤ size)
    (p0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (p10 : s.gpr .r10 = base + BitVec.ofNat 32 a)
    (p12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (p9 : s.gpr .r9 = base + BitVec.ofNat 32 m) (count : s.gpr .lr = BitVec.ofNat 32 n)
    (high : val32 s.mem (State.addr base) (o + 4 * n) 2 = 0)
    (ha : val32 s.mem (State.addr base) a n < val32 s.mem (State.addr base) m n)
    (hb : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) m n) :
    WP isa subModBuffers s fun t =>
      val32 t.mem (State.addr base) o n =
        (val32 s.mem (State.addr base) a n + val32 s.mem (State.addr base) m n -
          val32 s.mem (State.addr base) b n) % val32 s.mem (State.addr base) m n ∧
      val32 t.mem (State.addr base) o n < val32 s.mem (State.addr base) m n ∧
      Outside (State.addr base) o (4 * (n + 2)) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [subModBuffers, WP.seq_iff]
  refine WP.mono (subModHead_ok s) ?_
  rintro u ⟨saved, width, zero, keepU⟩
  have restU : Rest [.r7, .r8, .r11] s u := ⟨keepU.regs, keepU.rd, keepU.wr, keepU.sp⟩
  have ctxU : SubCtx u base size o a b n :=
    ⟨ctx.nowrap, ctx.outFits, ctx.aFits, ctx.bFits, ctx.sepA, ctx.sepB,
      by rw [keepU.wr]; exact ctx.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (subRow_ok u ctxU hn
    ((restU.gpr .r0 (by simp)).trans p0) ((restU.gpr .r10 (by simp)).trans p10)
    ((restU.gpr .r12 (by simp)).trans p12) ((restU.gpr .lr (by simp)).trans count)
    (by rw [zero]; decide)) ?_
  intro v inv
  have value := inv.value
  rw [keepU.mem, zero] at value
  have outside := inv.outside
  rw [keepU.mem] at outside
  have top := outside.val32 (d := o + 4 * n) (k := 2) (by omega)
    (by have := ctx.nowrap; omega)
  have modulus := outside.val32 (d := m) (k := n) row.separate.symm
    (by have := ctx.nowrap; have := row.inFits; omega)
  have extended : val32 v.mem (State.addr base) o (n + 2) = val32 v.mem (State.addr base) o n := by
    rw [val32_append, top, high, Nat.mul_zero, Nat.add_zero]
  rw [WP.seq_iff]
  refine WP.mono (subModAddArgs_ok v) ?_
  rintro z ⟨scalar, out, modPtr, widthZ, zeroZ, keepZ⟩
  have restZ : Rest [.r1, .r0, .r12, .lr, .r11] v z := ⟨keepZ.regs, keepZ.rd, keepZ.wr, keepZ.sp⟩
  have rowZ : RowCtx z base size o m n :=
    ⟨row.nowrap, row.outFits, row.inFits, row.separate,
      by rw [keepZ.wr, inv.rest.wr, keepU.wr]; exact row.writable⟩
  have outZ := out.trans ((inv.rest.gpr .r7 (by simp [subLoopClobbers])).trans (saved.trans p0))
  have modZ := modPtr.trans ((inv.rest.gpr .r9 (by simp [subLoopClobbers])).trans
    ((restU.gpr .r9 (by simp)).trans p9))
  have countZ := widthZ.trans ((inv.rest.gpr .r8 (by simp [subLoopClobbers])).trans (width.trans count))
  have fit : val32 z.mem (State.addr base) o (n + 2) +
      (z.gpr .r1).toNat * val32 z.mem (State.addr base) m n + (z.gpr .r11).toNat <
        2 ^ (32 * (n + 2)) := by
    rw [keepZ.mem, extended, scalar, zeroZ]
    exact product_row_fits (val32_lt _ _ _ _) (v.gpr .r11).isLt (val32_lt _ _ _ _)
  refine WP.mono (rowFull_ok z rowZ hn space outZ modZ countZ fit) ?_
  rintro t ⟨whole, outsideT, _, restT⟩
  rw [keepZ.mem, extended, scalar, zeroZ, modulus] at whole
  change val32 t.mem (State.addr base) o (n + 2) =
    val32 v.mem (State.addr base) o n + (v.gpr .r11).toNat * val32 s.mem (State.addr base) m n at whole
  obtain ⟨result, bound⟩ := subMod_value ha hb (val32_lt _ _ _ _) (val32_lt _ _ _ _) inv.borrow value
  have low : val32 t.mem (State.addr base) o n =
      (val32 v.mem (State.addr base) o n + (v.gpr .r11).toNat * val32 s.mem (State.addr base) m n) % 2 ^ (32 * n) := by
    rw [← whole, val32_append, Nat.add_mod, Nat.mul_mod_right, Nat.add_zero,
      Nat.mod_eq_of_lt (val32_lt _ _ _ _)]
    exact (Nat.mod_eq_of_lt (val32_lt _ _ _ _)).symm
  rw [keepZ.mem] at outsideT
  exact ⟨low.trans result, low ▸ bound,
    (outside.mono (Nat.le_refl _) (by omega)).trans outsideT,
    (restU.mono (by simp [roundClobbers])).trans ((inv.rest.mono (by simp [roundClobbers, subLoopClobbers])).trans
      ((restZ.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers, loopClobbers]))))⟩

end VG.Proof.Bignum.Arm
