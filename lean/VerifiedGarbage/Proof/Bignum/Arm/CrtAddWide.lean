module
public import Batteries.Logic
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Bignum.Arm.CrtAddWide

import VerifiedGarbage.Proof.Bignum.Arm.CrtAddWideArgs
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block

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
  refine WP.mono (rowFull_ok u row (by have := h.positive; omega) h.outputFits out input count fits) ?_
  rintro v ⟨value, outside, _, restV⟩
  rw [one, zero, memU] at value
  change _ = _ + 1 * _ + 0 at value
  simp only [Nat.one_mul, Nat.add_zero] at value
  rw [memU] at outside
  have frame := outside_workspace outside h.outputFits
  have rest : Rest roundClobbers s v := (restU.mono (by simp [roundClobbers])).trans
    (restV.mono (by simp [loopClobbers, roundClobbers]))
  refine WP.mono (restoreBase_ok v (by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead)
    (saved_base_kept frame h.stackSep h.saved rest.sp)) ?_
  rintro t ⟨ptrT, memT, restT⟩
  exact ⟨by rw [memT]; exact value, by rw [memT]; exact outside, by rw [memT]; exact frame,
    ptrT, rest.trans (restT.mono (by simp [roundClobbers]))⟩

end VG.Proof.Bignum.Arm
