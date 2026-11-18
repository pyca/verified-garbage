module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopy
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperand
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.TransferPadded
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Bignum.Arm.SubModArray
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
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

/-! ### `Bignum.Arm.SubModArray`, which this module and modules that import it used -/

section

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
  have small : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
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
    have mul : 2 ^ (32 * (2 * w)) * val32 u.mem (State.addr base) (arrAt w o + 4 * (2 * w)) 2 = 0 := by omega_using [zero]
    rcases Nat.mul_eq_zero.mp mul with bad | good
    · omega_using [positive, bad]
    · exact good
  have header := nativeHeader_of_layout u.mem base nowrap (Nat.le_refl _) readyU.layout
  rw [readyU.width] at header
  rw [WP.seq_iff]
  refine WP.mono (subModArrayArgs_ok u ho.1 ha.1 hb.1 readyU.workspace (by omega_using [small]) header readyU.ptr) ?_
  rintro v ⟨p0, p10, p12, p9, count, memV, restV⟩
  have ctx : SubCtx v base (8 * len) (arrAt w o) (arrAt w a) (arrAt w b) (2 * w) :=
    ⟨nowrap, by omega_using [endO], by omega_using [endA], by omega_using [endB], by omega_using [sepA], by omega_using [sepB],
      by rw [restV.wr]; exact readyU.workspace.writable⟩
  have row : RowCtx v base (8 * len) (arrAt w o) (arrAt w 0) (2 * w) :=
    ⟨nowrap, by omega_using [endO], by omega_using [endM], by omega_using [sepM], by rw [restV.wr]; exact readyU.workspace.writable⟩
  have nums (q : Nat) : val32 v.mem (State.addr base) (arrAt w q) (2 * w) = numAt u.mem (State.addr base) w q := by
    rw [memV, numAt_native]
  rw [WP.seq_iff]
  refine WP.mono (subModBuffers_ok v ctx row (by omega_using [width]) (by omega_using [endO]) p0 p10 p12 p9 count
    (by rw [memV]; exact high) (by rw [nums a, nums 0, oldA, oldM]; exact boundA)
    (by rw [nums b, nums 0, oldB, oldM]; exact boundB)) ?_
  rintro z ⟨value, _, outside, restZ⟩
  rw [nums a, nums b, nums 0, oldA, oldB, oldM] at value
  rw [memV] at outside
  have frameZ := outside_workspace outside (by omega_using [endO] : arrAt w o + 4 * (2 * w + 2) ≤ 8 * len)
  have keepsZ := outside_array_prefix_keeps outside (by omega_using [nowrap] : 8 * len < 2 ^ 64) (by omega_using [])
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

end

end

/-! # A full-width number modulo the narrow workspace's modulus

A number `x` of `w ≤ 2 v` limbs is `l + h R` with `R = 2^(64 v)` and `l`, `h`
below `R`: `h R mod M` from `h R² R⁻¹`, its negation from zero, and `l mod M`
from `l R² R⁻¹ R⁻¹` give `x mod M = l mod M - (0 - h R mod M)`.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

/-- `l mod M - (0 - c mod M)`, modulo `M`, is `l + c`. -/
theorem half_combine {M l c : Nat} (pos : 0 < M) :
    (l % M + M - (0 + M - c % M) % M) % M = (l + c) % M := by
  obtain hc := Nat.mod_lt c pos
  rw [Nat.zero_add]
  rcases Nat.eq_zero_or_pos (c % M) with zero | positive
  · rw [zero, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod, Nat.add_mod l c, zero,
      Nat.add_zero, Nat.mod_mod]
  · rw [Nat.mod_eq_of_lt (by omega_using [pos, positive] : M - c % M < M), show l % M + M - (M - c % M) = l % M + c % M by omega_using [hc],
      ← Nat.add_mod]

/-- A cleared array is zero. -/
theorem numAt_of_cleared {m : Mem} {base : Addr} {w o : Nat}
    (cleared : val32 m base (arrAt w o) (2 * w + 2) = 0) : numAt m base w o = 0 := by
  rw [numAt_native]; exact (val32_zero_split cleared).1

theorem CrtCopyCtx.after_narrow {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v : Nat} {rs : List Reg} (h : CrtCopyCtx g bs child slot v s)
    (ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t)
    (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem)
    (rest : Rest rs s t) : CrtCopyCtx g bs child slot v t := by
  obtain sepN : ∀ r ∈ [(⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sep
  obtain sepM : ∀ r ∈ [(⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr g.base, 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.shared.buffers.context.sepMN
  obtain frame' : Frame (⟨State.addr s.sp, 4⟩ :: [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩])
      s.mem t.mem := frame.mono (by simp)
  obtain eqC := h.shared.eq_of_frame h.childWs h.member frame' sepN
  obtain eqM := h.shared.eq_of_frame h.shared.buffers.context.main (by simp [crtRegions]) frame' sepM
  exact ⟨h.shared.after_narrow (frame.mono (by simp)) rest, ready, h.childWs.congr rest.wr, h.member,
    h.layout.congr eqC, h.sep, h.slotFit, h.slotSmall,
    by rw [eqM.word (d := slot) (bits := 32) (by have := h.slotFit; omega_using [this])]; exact h.link, h.le⟩

theorem CrtShared.copyCtx {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v : Nat} (h : CrtShared g bs s) (kind : CrtChild g child slot)
    (ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s) (le : v ≤ g.words) :
    CrtCopyCtx g bs child slot v s :=
  ⟨h, ready, (h.child kind).2.1, (h.child kind).1, (h.child kind).2.2.1, (h.child kind).2.2.2.1,
    (h.child kind).2.2.2.2.1, (h.child kind).2.2.2.2.2.1, (h.child kind).2.2.2.2.2.2, le⟩

theorem CrtCopyCtx.child_num {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v j : Nat} (h : CrtCopyCtx g bs child slot v s) (hj : j < 8)
    (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem) :
    numAt t.mem (State.addr child) g.words j = numAt s.mem (State.addr child) g.words j := by
  obtain sepN : ∀ r ∈ [(⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sep
  obtain eqC := h.shared.eq_of_frame h.childWs h.member (frame.mono (by simp)) sepN
  exact eqC.number (h.layout.width ▸ h.layout.layout.2.2.1) hj

theorem CrtCopyCtx.child_eq {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v : Nat} (h : CrtCopyCtx g bs child slot v s)
    (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem) :
    WorkspaceEq (State.addr child) (8 * workspaceWords g.words) s.mem t.mem := by
  obtain sepN : ∀ r ∈ [(⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sep
  exact h.shared.eq_of_frame h.childWs h.member (frame.mono (by simp)) sepN

/-- After a copy into the low limbs of the full array `j`: the context holds, the
narrow workspace is unchanged and the full one keeps its other arrays. -/
theorem CrtCopyCtx.after_copyOut {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v j : Nat} (h : CrtCopyCtx g bs child slot v s) (kind : CrtChild g child slot) (hj : j < 8)
    (ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t)
    (outside : Outside (State.addr child) (arrAt g.words j) (8 * v) s.mem t.mem) (rest : Rest roundClobbers s t) :
    CrtCopyCtx g bs child slot v t ∧ Keeps (State.addr child) (workspaceWords g.words) g.words j s.mem t.mem ∧
      Frame [⟨State.addr child, 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      WorkspaceEq (State.addr (crtN g.base g.words)) (8 * workspaceWords g.words) s.mem t.mem := by
  obtain fitsC : arrAt g.words 8 ≤ 8 * workspaceWords g.words := h.layout.width ▸ h.layout.layout.2.2.1
  obtain endJ := Nat.le_trans (array_end_le (w := g.words) hj) fitsC
  obtain words : g.words ≤ 128 := (crt_width_valid h.shared.buffers.lengthValid).2.1
  obtain wsSmall : workspaceWords g.words ≤ 16 * 128 + 64 := by simp only [workspaceWords]; omega_using [words]
  have le := h.le
  obtain frameC := outside_workspace outside (size := 8 * workspaceWords g.words) (by omega_using [endJ, le])
  obtain keeps := outside_array_prefix_keeps outside (by omega_using [wsSmall] : 8 * workspaceWords g.words < 2 ^ 64)
    (by omega_using [le] : 8 * v ≤ 8 * (g.words + 2))
  obtain layoutT : CrtLayoutState child (workspaceWords g.words) g.words t.mem := by
    obtain kl := keeps_layout h.layout.layout (by rw [h.layout.width]; exact keeps)
    exact ⟨kl.2, kl.1.trans h.layout.width⟩
  obtain sharedT : CrtShared g bs t := by
    obtain f : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem :=
      frameC.mono (by simp)
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact h.shared.after_p f rest layoutT
    · exact h.shared.after_q f rest layoutT
  obtain sepC : ∀ r ∈ [(⟨State.addr child, 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sep.symm
  obtain eqN := h.shared.eq_of_frame h.shared.buffers.context.narrow h.shared.narrow_member
    (regions := [⟨State.addr child, 8 * workspaceWords g.words⟩]) (frameC.mono (by simp)) sepC
  exact ⟨⟨sharedT, ready, (sharedT.child kind).2.1, h.member, layoutT, h.sep, h.slotFit, h.slotSmall,
    (sharedT.child kind).2.2.2.2.2.2, h.le⟩, keeps, frameC, eqN⟩

theorem crt_reduceHalf_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v j M : Nat} (h : CrtCopyCtx g bs child slot v s) (hj : j < 8) (half : g.words ≤ 2 * v)
    (modulus : numAt s.mem (State.addr (crtN g.base g.words)) v 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr (crtN g.base g.words)) v 4 = 2 ^ (128 * v) % M) :
    WP isa (reduceHalf slot j) s fun t =>
      ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 0 = M ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 4 = 2 ^ (128 * v) % M ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 7 = 1 ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 1 = numAt s.mem (State.addr child) g.words j % M ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  obtain fits : arrAt v 8 ≤ 8 * workspaceWords g.words := h.ready.width ▸ h.ready.layout.2.2.1
  obtain op : ∀ q, q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 → Operand q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  obtain positive : 0 < M := by have := h.ready.modulus; omega_using [odd]
  -- `h`, the high limbs, into array 1.
  rw [reduceHalf, WP.seq_iff]
  refine WP.mono (clearArrayWide_ok s h.ready (o := 1) (by decide) (by decide)) ?_
  rintro s1 ⟨ready1, cleared1, keeps1, frame1, rest1⟩
  obtain ctx1 := h.after_narrow ready1 frame1 rest1
  obtain mod1 := (keeps_array_num keeps1 fits (op 0 (by simp)) (by decide)).trans modulus
  obtain r21 := (keeps_array_num keeps1 fits (op 4 (by simp)) (by decide)).trans r2
  rw [WP.seq_iff]
  refine WP.mono (crt_copyHigh_ok s1 ctx1 hj (by decide) (by decide) half) ?_
  rintro s2 ⟨ready2, high2, keeps2, frame2, rest2⟩
  replace high2 := high2 cleared1
  rw [h.child_num hj frame1] at high2
  obtain mod2 := (keeps_array_num keeps2 fits (op 0 (by simp)) (by decide)).trans mod1
  obtain r22 := (keeps_array_num keeps2 fits (op 4 (by simp)) (by decide)).trans r21
  -- One, and `h R mod M`.
  rw [WP.seq_iff]
  refine WP.mono (smallConst_ok s2 (o := 7) 1 ready2 (by decide) (by decide) (by decide) (by decide)) ?_
  rintro s3 ⟨ready3, one3, _, keeps3, frame3, rest3⟩
  obtain mod3 := (keeps_array_num keeps3 fits (op 0 (by simp)) (by decide)).trans mod2
  obtain r23 := (keeps_array_num keeps3 fits (op 4 (by simp)) (by decide)).trans r22
  obtain high3 := (keeps_array_num keeps3 fits (op 1 (by simp)) (by decide)).trans high2
  rw [WP.seq_iff]
  refine WP.mono (montEncode_ok s3 ready3 (op 1 (by simp)) (op 1 (by simp)) (by decide) mod3 odd r23) ?_
  rintro s4 ⟨ready4, mod4, enc4, keeps4, frame4, rest4⟩
  rw [high3] at enc4
  obtain r24 := (keeps_array_num keeps4 fits (op 4 (by simp)) (by decide)).trans r23
  obtain one4 := (keeps_array_num keeps4 fits (op 7 (by simp)) (by decide)).trans one3
  -- Its negation, from a zero array 5, into array 6.
  rw [WP.seq_iff]
  refine WP.mono (clearArrayWide_ok s4 ready4 (o := 5) (by decide) (by decide)) ?_
  rintro s5 ⟨ready5, cleared5, keeps5, frame5, rest5⟩
  obtain mod5 := (keeps_array_num keeps5 fits (op 0 (by simp)) (by decide)).trans mod4
  obtain r25 := (keeps_array_num keeps5 fits (op 4 (by simp)) (by decide)).trans r24
  obtain one5 := (keeps_array_num keeps5 fits (op 7 (by simp)) (by decide)).trans one4
  obtain enc5 := (keeps_array_num keeps5 fits (op 1 (by simp)) (by decide)).trans enc4
  obtain zero5 : numAt s5.mem (State.addr (crtN g.base g.words)) v 5 = 0 := numAt_of_cleared cleared5
  rw [WP.seq_iff]
  refine WP.mono (subModArray_ok s5 ready5 (o := 6) (a := 5) (b := 1) (op 6 (by simp)) (op 5 (by simp))
    (op 1 (by simp)) (by decide) (by decide) (by decide) (by rw [zero5, mod5]; exact positive)
    (by rw [enc5, mod5]; exact Nat.mod_lt _ positive)) ?_
  rintro s6 ⟨ready6, neg6, keeps6, frame6, rest6⟩
  rw [zero5, mod5, enc5] at neg6
  obtain mod6 := (keeps_array_num keeps6 fits (op 0 (by simp)) (by decide)).trans mod5
  obtain r26 := (keeps_array_num keeps6 fits (op 4 (by simp)) (by decide)).trans r25
  obtain one6 := (keeps_array_num keeps6 fits (op 7 (by simp)) (by decide)).trans one5
  -- `l mod M`, from the low limbs into array 5.
  obtain frame16 : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s1.mem s6.mem :=
    frame2.trans (frame3.trans (frame4.trans (frame5.trans frame6)))
  obtain rest16 : Rest roundClobbers s1 s6 := rest2.trans (rest3.trans (rest4.trans (rest5.trans rest6)))
  obtain ctx6 := ctx1.after_narrow ready6 frame16 rest16
  rw [WP.seq_iff]
  refine WP.mono (crt_copyLow_ok s6 ctx6 hj (by decide) (by decide)) ?_
  rintro s7 ⟨ready7, low7, keeps7, frame7, rest7⟩
  rw [ctx1.child_num hj frame16, h.child_num hj frame1] at low7
  obtain mod7 := (keeps_array_num keeps7 fits (op 0 (by simp)) (by decide)).trans mod6
  obtain r27 := (keeps_array_num keeps7 fits (op 4 (by simp)) (by decide)).trans r26
  obtain one7 := (keeps_array_num keeps7 fits (op 7 (by simp)) (by decide)).trans one6
  obtain neg7 := (keeps_array_num keeps7 fits (op 6 (by simp)) (by decide)).trans neg6
  rw [WP.seq_iff]
  refine WP.mono (reduceOperand_ok s7 ready7 (op 5 (by simp)) (by decide) (by decide) mod7 odd r27 one7) ?_
  rintro s8 ⟨ready8, mod8, low8, keeps8, frame8, rest8⟩
  rw [low7] at low8
  obtain r28 := (keeps_array_num keeps8 fits (op 4 (by simp)) (by decide)).trans r27
  obtain one8 := (keeps_array_num keeps8 fits (op 7 (by simp)) (by decide)).trans one7
  obtain neg8 := (keeps_array_num keeps8 fits (op 6 (by simp)) (by decide)).trans neg7
  -- The difference.
  refine WP.mono (subModArray_ok s8 ready8 (o := 1) (a := 5) (b := 6) (op 1 (by simp)) (op 5 (by simp))
    (op 6 (by simp)) (by decide) (by decide) (by decide) (by rw [low8, mod8]; exact Nat.mod_lt _ positive)
    (by rw [neg8, mod8]; exact Nat.mod_lt _ positive)) ?_
  rintro t ⟨readyT, valueT, keepsT, frameT, restT⟩
  refine ⟨readyT, (keeps_array_num keepsT fits (op 0 (by simp)) (by decide)).trans mod8,
    (keeps_array_num keepsT fits (op 4 (by simp)) (by decide)).trans r28,
    (keeps_array_num keepsT fits (op 7 (by simp)) (by decide)).trans one8, ?_,
    frame1.trans (frame16.trans (frame7.trans (frame8.trans frameT))),
    rest1.trans (rest16.trans (rest7.trans (rest8.trans restT)))⟩
  rw [valueT, low8, mod8, neg8, half_combine positive, Nat.mod_add_div']

end VG.Proof.Bignum.Arm
