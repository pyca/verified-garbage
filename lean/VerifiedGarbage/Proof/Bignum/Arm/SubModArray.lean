module

public import VerifiedGarbage.Impl.Bignum.Arm.SubModArray
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.SubModBuffers
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.SubState
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Bignum.Arm.ProductRowMath
/-! # Modular subtraction preserves the shared workspace invariant -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/SubModControls.lean`, which only this module imported.
section

/-! # Preserve public buffer addresses and carry the secret borrow into addition -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem subModHead_ok (s : State) : WP isa (.block subModHead) s fun t =>
    t.gpr .r7 = s.gpr .r0 ∧ t.gpr .r8 = s.gpr .lr ∧ t.gpr .r11 = 0 ∧
    Preserves [.r7, .r8, .r11] s t := by
  apply WP.of_runBlock
  simp only [subModHead, runBlock_cons, runStep_some, exec, Op2.eval, Option.map_some,
    ↓reduceIte, gpr_setReg, reduceCtorEq]
  refine ⟨_, rfl, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

theorem subModAddArgs_ok (s : State) : WP isa (.block subModAddArgs) s fun t =>
    t.gpr .r1 = s.gpr .r11 ∧ t.gpr .r0 = s.gpr .r7 ∧ t.gpr .r12 = s.gpr .r9 ∧ t.gpr .lr = s.gpr .r8 ∧ t.gpr .r11 = 0 ∧
    Preserves [.r1, .r0, .r12, .lr, .r11] s t := by
  apply WP.of_runBlock
  simp only [subModAddArgs, runBlock_cons, runStep_some, exec, Op2.eval, Option.map_some,
    ↓reduceIte, gpr_setReg, reduceCtorEq]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/SubModMath.lean`, which only this module imported.
section

/-! # A borrow-masked addition implements modular subtraction -/

section

namespace VG.Proof.Bignum.Arm

theorem subMod_value {A B M R D c : Nat} (ha : A < M) (hb : B < M)
    (hm : M < R) (hd : D < R) (hc : c ≤ 1) (value : D + B = A + R * c) :
    (D + c * M) % R = (A + M - B) % M ∧ (D + c * M) % R < M := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
  · simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at value ⊢
    have hdm : D < M := by omega
    have eq : A + M - B = D + M := by omega
    simp only [Nat.mod_eq_of_lt hd, eq, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hdm]
    exact ⟨trivial, hdm⟩
  · simp only [Nat.mul_one, Nat.one_mul] at value ⊢
    have order : A < B := by omega
    have small : A + M - B < M := by omega
    have eq : D + M = R + (A + M - B) := by omega
    simp only [eq, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega : A + M - B < R),
      Nat.mod_eq_of_lt small]
    exact ⟨trivial, small⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/SubModBuffers.lean`, which only this module imported.
section

/-! # Exact modular subtraction through the shared native arithmetic loops -/

section

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
    ((restU.gpr .r0 (by decide)).trans p0) ((restU.gpr .r10 (by decide)).trans p10)
    ((restU.gpr .r12 (by decide)).trans p12) ((restU.gpr .lr (by decide)).trans count)
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
  have outZ := out.trans ((inv.rest.gpr .r7 (by decide)).trans (saved.trans p0))
  have modZ := modPtr.trans ((inv.rest.gpr .r9 (by decide)).trans
    ((restU.gpr .r9 (by decide)).trans p9))
  have countZ := widthZ.trans ((inv.rest.gpr .r8 (by decide)).trans (width.trans count))
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
    (restU.mono (by decide)).trans ((inv.rest.mono (by decide)).trans
      ((restZ.mono (by decide)).trans (restT.mono (by decide))))⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem subModArray_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (ho0 : o ≠ 0) (hoa : o ≠ a) (hob : o ≠ b)
    (boundA : numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0)
    (boundB : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (subModArray o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w o =
        (numAt s.mem (State.addr base) w a + numAt s.mem (State.addr base) w 0 -
          numAt s.mem (State.addr base) w b) % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have endO := Nat.le_trans (array_end_le ho.1) fits
  have endA := Nat.le_trans (array_end_le ha.1) fits
  have endB := Nat.le_trans (array_end_le hb.1) fits
  have endM := Nat.le_trans (array_end_le (w := w) (j := 0) (by decide : 0 < 8)) fits
  have small : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have nowrap := h.workspace.nowrap
  have width : 2 ≤ w := h.width ▸ h.layout.1
  have sepA := array_sep (w := w) hoa
  have sepB := array_sep (w := w) hob
  have sepM := array_sep (w := w) ho0
  rw [subModArray, WP.seq_iff]
  refine WP.mono (clearArrayWide_ok s h ho.1 ho0) ?_
  rintro u ⟨readyU, zero, keepsU, frameU, restU⟩
  have oldA := keeps_array_num keepsU fits ha (Ne.symm hoa)
  have oldB := keeps_array_num keepsU fits hb (Ne.symm hob)
  have oldM := keeps_array_num keepsU fits (q := 0)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (Ne.symm ho0)
  have high : val32 u.mem (State.addr base) (arrAt w o + 4 * (2 * w)) 2 = 0 := by
    rw [val32_append] at zero
    have positive : 0 < 2 ^ (32 * (2 * w)) := Nat.two_pow_pos _
    have mul : 2 ^ (32 * (2 * w)) * val32 u.mem (State.addr base) (arrAt w o + 4 * (2 * w)) 2 = 0 := by omega
    rcases Nat.mul_eq_zero.mp mul with bad | good
    · omega
    · exact good
  have header := nativeHeader_of_layout u.mem base nowrap (Nat.le_refl _) readyU.layout
  rw [readyU.width] at header
  rw [WP.seq_iff]
  refine WP.mono (subModArrayArgs_ok u ho.1 ha.1 hb.1 readyU.workspace (by omega) header readyU.ptr) ?_
  rintro v ⟨p0, p10, p12, p9, count, memV, restV⟩
  have ctx : SubCtx v base (8 * len) (arrAt w o) (arrAt w a) (arrAt w b) (2 * w) :=
    ⟨nowrap, by omega, by omega, by omega, by omega, by omega,
      by rw [restV.wr]; exact readyU.workspace.writable⟩
  have row : RowCtx v base (8 * len) (arrAt w o) (arrAt w 0) (2 * w) :=
    ⟨nowrap, by omega, by omega, by omega, by rw [restV.wr]; exact readyU.workspace.writable⟩
  have nums (q : Nat) : val32 v.mem (State.addr base) (arrAt w q) (2 * w) = numAt u.mem (State.addr base) w q := by
    rw [memV, numAt_native]
  rw [WP.seq_iff]
  refine WP.mono (subModBuffers_ok v ctx row (by omega) (by omega) p0 p10 p12 p9 count
    (by rw [memV]; exact high) (by rw [nums a, nums 0, oldA, oldM]; exact boundA)
    (by rw [nums b, nums 0, oldB, oldM]; exact boundB)) ?_
  rintro z ⟨value, _, outside, restZ⟩
  rw [nums a, nums b, nums 0, oldA, oldB, oldM] at value
  rw [memV] at outside
  have frameZ := outside_workspace outside (by omega : arrAt w o + 4 * (2 * w + 2) ≤ 8 * len)
  have keepsZ := outside_array_prefix_keeps outside (by omega : 8 * len < 2 ^ 64) (by omega)
  have restUZ : Rest roundClobbers u z := (restV.mono (by decide)).trans restZ
  refine WP.mono (restoreBase_ok z (by rw [restUZ.rd, restUZ.wr, restUZ.sp]; exact readyU.stackRead)
    (saved_base_kept frameZ readyU.stackSep readyU.saved restUZ.sp)) ?_
  rintro t ⟨ptrT, memT, restT⟩
  rw [← memT] at keepsZ frameZ
  have rest : Rest roundClobbers u t := restUZ.trans (restT.mono (by decide))
  exact ⟨(readyU.after_array ho0 keepsZ frameZ rest ptrT).1,
    by rw [numAt_native, memT]; exact value,
    fun i hi sep => (keepsZ i hi sep).trans (keepsU i hi sep), frameU.trans frameZ, restU.trans rest⟩

end VG.Proof.Bignum.Arm
