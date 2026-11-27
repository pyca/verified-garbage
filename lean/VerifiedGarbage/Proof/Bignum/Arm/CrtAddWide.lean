module

public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Impl.Bignum.Arm.CrtAddWide
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWideArgs
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! ### `Bignum.Arm.CrtAddWideArgs`, which this module and modules that import it used -/

section

/-! # Load the public pointers and width for final CRT addition -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtAddWideScalars.lean`, which only this module imported.
section

/-! # Set an extended addition's scalar and carry to one and zero -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.X25519.Arm (Rest wp_dp wp_mov op2_imm dpVal)

theorem crt_addWideScalars_ok (s : State) {w : Nat} (count : s.gpr .lr = BitVec.ofNat 32 (4 * w + 2)) :
    WP isa (.block addWideScalars) s fun t => t.gpr .lr = BitVec.ofNat 32 (4 * w) ∧
      t.gpr .r1 = 1 ∧ t.gpr .r11 = 0 ∧ t.mem = s.mem ∧ Rest [.r1, .r11, .lr] s t := by
  unfold addWideScalars
  refine wp_dp (op2_imm (by decide)) fun u a => ?_
  refine wp_mov (op2_imm (by decide)) fun v b => ?_
  refine wp_mov (op2_imm (by decide)) fun t c => WP.block_nil ?_
  refine ⟨?_, (c.other .r1 (by decide)).trans b.gpr, c.gpr, c.mem.trans (b.mem.trans a.mem),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans (c.rest (by simp)))⟩
  rw [c.other .lr (by decide), b.other .lr (by decide), a.gpr, dpVal, count, BitVec.ofNat_add]
  change (BitVec.ofNat 32 (4 * w) + 2#32) - 2#32 = _
  exact BitVec.add_sub_cancel _ _

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem crt_addWideArgs_ok (s : State) {base dst src : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : 244 ≤ size) (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (output : s.mem.readW (off (State.addr base) 232) 32 = dst)
    (input : s.mem.readW (off (State.addr base) 240) 32 = src) :
    WP isa addWideArgs s fun t => t.gpr .r0 = dst ∧ t.gpr .r12 = src ∧
      t.gpr .lr = BitVec.ofNat 32 (4 * w) ∧ t.gpr .r1 = 1 ∧ t.gpr .r11 = 0 ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r3, .r11, .r12, .lr] s t := by
  rw [addWideArgs, WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) 240) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega_using [fit, this])) (ws.read fit) fun u a => WP.block_nil ?_
  rw [WP.seq_iff]
  refine WP.mono (crt_clearWideArgs_ok u (dst := dst) (w := w) (ws.congr a.wr) (by omega_using [fit]) (by omega_using [fit]) (by decide)
    ((a.other .r0 (by decide)).trans ptr) (by rw [a.mem]; exact count) (by rw [a.mem]; exact output)) ?_
  rintro v ⟨out, width, _, memV, restV⟩
  refine WP.mono (crt_addWideScalars_ok v width) ?_
  rintro t ⟨countT, one, zero, memT, restT⟩
  exact ⟨(restT.gpr .r0 (by decide)).trans out,
    (restT.gpr .r12 (by decide)).trans ((restV.gpr .r12 (by decide)).trans (a.gpr.trans input)),
    countT, one, zero, memT.trans (memV.trans a.mem),
    (a.rest (by decide)).trans ((restV.mono (by decide)).trans (restT.mono (by decide)))⟩

end VG.Proof.Bignum.Arm

end

end

/-! # Exact full-width addition in the CRT result buffer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtAddWideInput (base : BitVec 32) (size o b w : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  fit : 244 ≤ size
  row : RowCtx s base size o b (4 * w)
  positive : 0 < w
  outputFits : o + 4 * (4 * w + 2) ≤ size
  ptr : s.gpr .r0 = base
  count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w
  output : s.mem.readW (off (State.addr base) 232) 32 = base + BitVec.ofNat 32 o
  input : s.mem.readW (off (State.addr base) 240) 32 = base + BitVec.ofNat 32 b
  sumFits : val32 s.mem (State.addr base) o (4 * w + 2) + val32 s.mem (State.addr base) b (4 * w) < 2 ^ (32 * (4 * w + 2))
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, size⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

theorem crt_addWide_ok (s : State) {base : BitVec 32} {size o b w : Nat}
    (h : CrtAddWideInput base size o b w s) :
    WP isa addWide s fun t =>
      val32 t.mem (State.addr base) o (4 * w + 2) =
        val32 s.mem (State.addr base) o (4 * w + 2) + val32 s.mem (State.addr base) b (4 * w) ∧
      Outside (State.addr base) o (4 * (4 * w + 2)) s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [addWide, WP.seq_iff]
  refine WP.mono (crt_addWideArgs_ok s h.workspace h.fit h.ptr h.count h.output h.input) ?_
  rintro u ⟨out, input, count, one, zero, memU, restU⟩
  have row : RowCtx u base size o b (4 * w) :=
    ⟨h.row.nowrap, h.row.outFits, h.row.inFits, h.row.separate,
      by rw [restU.wr]; exact h.row.writable⟩
  have fits : val32 u.mem (State.addr base) o (4 * w + 2) +
      (u.gpr .r1).toNat * val32 u.mem (State.addr base) b (4 * w) + (u.gpr .r11).toNat < 2 ^ (32 * (4 * w + 2)) := by
    rw [one, zero, memU]
    change _ + 1 * _ + 0 < _
    simpa only [Nat.one_mul, Nat.add_zero] using h.sumFits
  rw [WP.seq_iff]
  refine WP.mono (rowFull_ok u row (by have := h.positive; omega_using [this]) h.outputFits out input count fits) ?_
  rintro v ⟨value, outside, _, restV⟩
  rw [one, zero, memU] at value
  change _ = _ + 1 * _ + 0 at value
  simp only [Nat.one_mul, Nat.add_zero] at value
  rw [memU] at outside
  have frame := outside_workspace outside h.outputFits
  have rest : Rest roundClobbers s v := (restU.mono (by decide)).trans
    (restV.mono (by decide))
  refine WP.mono (restoreBase_ok v (by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead)
    (saved_base_kept frame h.stackSep h.saved rest.sp)) ?_
  rintro t ⟨ptrT, memT, restT⟩
  exact ⟨by rw [memT]; exact value, by rw [memT]; exact outside, by rw [memT]; exact frame,
    ptrT, rest.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
