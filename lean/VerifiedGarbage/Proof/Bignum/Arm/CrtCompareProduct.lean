module

public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SubState
public import VerifiedGarbage.Impl.Bignum.Arm.CrtCompareProduct

import VerifiedGarbage.Proof.Bignum.Arm.CrtCompareArgs
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Bignum.Arm.EqualBuffers
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Impl.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SubCompare
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectPrepare
/-! # Exact branchless equality of the factor product and padded modulus -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/EqualControls.lean`, which only this module imported.
section

/-! # Branchless setup and result combination for exact buffer equality -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp op2_reg op2_imm dpVal)

theorem equalHead_ok (s : State) : WP isa (.block equalHead) s fun t =>
    t.gpr .r8 = s.gpr .lr ∧ t.gpr .r11 = 0 ∧ t.mem = s.mem ∧ Rest [.r8, .r11] s t := by
  unfold equalHead
  refine wp_mov (op2_reg _ _) fun u h => ?_
  refine wp_mov (op2_imm (by decide)) fun t j => WP.block_nil ?_
  exact ⟨(j.other .r8 (by decide)).trans h.gpr, j.gpr, j.mem.trans h.mem,
    (h.rest (by simp)).trans (j.rest (by simp))⟩

theorem equalFinish_ok (s : State) {A B : Nat}
    (left : s.gpr .r6 = (if A < B then 1 else 0))
    (right : s.gpr .r11 = (if B < A then 1 else 0)) :
    WP isa (.block equalFinish) s fun t =>
      t.gpr .r11 = (if A = B then 1 else 0) ∧ t.mem = s.mem ∧ Rest [.r11] s t := by
  unfold equalFinish
  refine wp_dp (op2_reg _ _) fun u h => ?_
  refine wp_dp (op2_imm (by decide)) fun t j => WP.block_nil ?_
  refine ⟨?_, j.mem.trans h.mem, (h.rest (by simp)).trans (j.rest (by simp))⟩
  rw [j.gpr, dpVal, h.gpr, dpVal, left, right]
  rcases Nat.lt_trichotomy A B with lt | eq | gt
  · rw [ite_eq_left lt, ite_eq_right (by omega : ¬B < A), ite_eq_right (by omega : A ≠ B)]; decide
  · rw [ite_eq_right (by omega : ¬A < B), ite_eq_right (by omega : ¬B < A), ite_eq_left eq]; decide
  · rw [ite_eq_right (by omega : ¬A < B), ite_eq_left gt, ite_eq_right (by omega : A ≠ B)]; decide

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/EqualReverse.lean`, which only this module imported.
section

/-! # Swap and rewind the comparison inputs while retaining the first borrow -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem equalReverse_ok (s : State) : WP isa (.block equalReverse) s fun t =>
    t.gpr .r6 = s.gpr .r11 ∧ t.gpr .r0 = s.gpr .r0 - (s.gpr .r8 <<< 2) ∧
    t.gpr .r10 = s.gpr .r12 - (s.gpr .r8 <<< 2) ∧
    t.gpr .r12 = s.gpr .r10 - (s.gpr .r8 <<< 2) ∧ t.gpr .lr = s.gpr .r8 ∧ t.gpr .r11 = 0 ∧
    Preserves [.r0, .r6, .r7, .r10, .r11, .r12, .lr] s t := by
  apply WP.of_runBlock
  simp only [equalReverse, runBlock_cons, runStep_some, exec, Op2.eval, Option.map_some,
    ↓reduceIte, gpr_setReg, reduceCtorEq]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/SubCompareRow.lean`, which only this module imported.
section

/-! # Keep pointer postconditions together with the exact subtraction comparison -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem subCompareRow_ok (s : State) {base : BitVec 32} {size o a b n : Nat}
    (ctx : SubCtx s base size o a b n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp10 : s.gpr .r10 = base + BitVec.ofNat 32 a)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (count : s.gpr .lr = BitVec.ofNat 32 n) (borrow : s.gpr .r11 = 0) :
    WP isa subRow s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a n < val32 s.mem (State.addr base) b n then 1 else 0) ∧
      SubInv s base o a b n n t :=
  WP.mono ((subCompare_ok s ctx hn hp0 hp10 hp12 count borrow).and
    (subRow_ok s ctx hn hp0 hp10 hp12 count (by rw [borrow]; decide))) (fun _ h => ⟨h.1.1, h.2⟩)

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/EqualBuffers.lean`, which only this module imported.
section

/-! # Both unsigned comparisons yield exact equality without secret-dependent branches -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem equalBuffers_ok (s : State) {base : BitVec 32} {size o a b n : Nat}
    (ctx : SubCtx s base size o a b n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp10 : s.gpr .r10 = base + BitVec.ofNat 32 a)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b) (count : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa equalBuffers s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a n = val32 s.mem (State.addr base) b n then 1 else 0) ∧
      Outside (State.addr base) o (4 * n) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [equalBuffers, WP.seq_iff]
  refine WP.mono (equalHead_ok s) ?_
  rintro u ⟨saved, zero, memU, restU⟩
  have ctxU : SubCtx u base size o a b n :=
    ⟨ctx.nowrap, ctx.outFits, ctx.aFits, ctx.bFits, ctx.sepA, ctx.sepB, by rw [restU.wr]; exact ctx.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (subCompareRow_ok u ctxU hn
    ((restU.gpr .r0 (by decide)).trans hp0) ((restU.gpr .r10 (by decide)).trans hp10)
    ((restU.gpr .r12 (by decide)).trans hp12) ((restU.gpr .lr (by decide)).trans count) zero) ?_
  rintro v ⟨less, inv⟩
  have width : v.gpr .r8 = BitVec.ofNat 32 n :=
    (inv.rest.gpr .r8 (by decide)).trans (saved.trans count)
  rw [memU] at less
  rw [WP.seq_iff]
  refine WP.mono (equalReverse_ok v) ?_
  rintro z ⟨bit, p0, p10, p12, countZ, zeroZ, keep⟩
  rw [width, inv.outPtr, rewind32] at p0
  rw [width, inv.bPtr, rewind32] at p10
  rw [width, inv.aPtr, rewind32] at p12
  rw [width] at countZ
  have ctxZ : SubCtx z base size o b a n :=
    ⟨ctx.nowrap, ctx.outFits, ctx.bFits, ctx.aFits, ctx.sepB, ctx.sepA,
      by rw [keep.wr, inv.rest.wr, restU.wr]; exact ctx.writable⟩
  have aOld : val32 z.mem (State.addr base) a n = val32 s.mem (State.addr base) a n := by
    rw [keep.mem, inv.outside.val32 ctx.sepA.symm (by have := ctx.nowrap; have := ctx.aFits; omega), memU]
  have bOld : val32 z.mem (State.addr base) b n = val32 s.mem (State.addr base) b n := by
    rw [keep.mem, inv.outside.val32 ctx.sepB.symm (by have := ctx.nowrap; have := ctx.bFits; omega), memU]
  rw [WP.seq_iff]
  refine WP.mono (subCompare_ok z ctxZ hn p0 p10 p12 countZ zeroZ) ?_
  rintro t ⟨greater, outsideT, restT⟩
  rw [aOld, bOld] at greater
  have first : t.gpr .r6 = (if val32 s.mem (State.addr base) a n < val32 s.mem (State.addr base) b n then 1 else 0) :=
    (restT.gpr .r6 (by decide)).trans (bit.trans less)
  refine WP.mono (equalFinish_ok t first greater) ?_
  rintro final ⟨result, memFinal, restFinal⟩
  have outsideV := inv.outside
  rw [memU] at outsideV
  rw [keep.mem] at outsideT
  have restZ : Rest [.r0, .r6, .r7, .r10, .r11, .r12, .lr] v z := ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩
  exact ⟨result, by rw [memFinal]; exact outsideV.trans outsideT,
    (restU.mono (by decide)).trans ((inv.rest.mono (by decide)).trans
      ((restZ.mono (by decide)).trans ((restT.mono (by decide)).trans
        (restFinal.mono (by decide)))))⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtCompareInput (base : BitVec 32) (size o a b w : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  fit : 244 ≤ size
  subtraction : SubCtx s base size o a b (4 * w + 2)
  ptr : s.gpr .r0 = base
  count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w
  output : s.mem.readW (off (State.addr base) 236) 32 = base + BitVec.ofNat 32 o
  first : s.mem.readW (off (State.addr base) 232) 32 = base + BitVec.ofNat 32 a
  second : s.mem.readW (off (State.addr base) 240) 32 = base + BitVec.ofNat 32 b
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, size⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

theorem crt_compareProduct_ok (s : State) {base : BitVec 32} {size o a b w : Nat}
    (h : CrtCompareInput base size o a b w s) :
    WP isa compareProduct s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a (4 * w + 2) =
        val32 s.mem (State.addr base) b (4 * w + 2) then 1 else 0) ∧
      Outside (State.addr base) o (4 * (4 * w + 2)) s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [compareProduct, WP.seq_iff]
  refine WP.mono (crt_compareArgs_ok s h.workspace h.fit h.ptr h.count h.output h.first h.second) ?_
  rintro u ⟨ptrU, aU, bU, countU, memU, restU⟩
  have ctx : SubCtx u base size o a b (4 * w + 2) :=
    ⟨h.subtraction.nowrap, h.subtraction.outFits, h.subtraction.aFits, h.subtraction.bFits,
      h.subtraction.sepA, h.subtraction.sepB, by rw [restU.wr]; exact h.subtraction.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (equalBuffers_ok u ctx (by omega) ptrU aU bU countU) ?_
  rintro v ⟨value, outside, restV⟩
  rw [memU] at value outside
  have frame := outside_workspace outside h.subtraction.outFits
  have rest : Rest roundClobbers s v := (restU.mono (by decide)).trans restV
  refine WP.mono (restoreBase_ok v (by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead)
    (saved_base_kept frame h.stackSep h.saved rest.sp)) ?_
  rintro t ⟨ptrT, memT, restT⟩
  exact ⟨(restT.gpr .r11 (by decide)).trans value, by rw [memT]; exact outside,
    by rw [memT]; exact frame, ptrT, rest.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
