module

import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
import VerifiedGarbage.Proof.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinish
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Impl.Bignum.Arm.Round
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Exact division and state advance after Montgomery cancellation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem quotientStage_ok (s : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (hdr : RoundMeta s.mem base tmp a b mod acc n i inv)
    (hi : i < n) (ptr : s.gpr .r0 = base + BitVec.ofNat 32 (acc + 4 * n))
    (cancel : val32 s.mem (State.addr base) acc (n + 2) % 2 ^ 32 = 0) :
    WP isa quotientStage s fun t =>
      2 ^ 32 * val32 t.mem (State.addr base) acc (n + 2) = val32 s.mem (State.addr base) acc (n + 2) ∧
      RoundMeta t.mem base tmp a b mod acc n (i + 1) inv ∧
      t.gpr .r0 = base + BitVec.ofNat 32 tmp ∧
      Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp + 16, 8)] s.mem t.mem ∧
      t.z = decide (i + 1 = n) ∧ Rest roundClobbers s t := by
  have hn := ctx.count
  have ht := ctx.tmpFits
  have layout := ctx.layout
  have nowrap := ctx.workspace.nowrap
  have fits := ctx.accFits
  rw [quotientStage, WP.seq_iff]
  refine WP.mono (shiftArgs_ok s (acc := acc) (n := n) ctx.workspace (by omega) ptr ?_ ?_) ?_
  · simpa only [show acc + 4 * n + 16 = tmp by omega] using hdr.count
  · simpa only [show acc + 4 * n + 44 = tmp + 28 by omega] using hdr.accPtr
  · rintro u ⟨p0, count, mem, keep⟩
    have shiftCtx : ShiftCtx u base size acc (n + 1) :=
      ⟨nowrap, by omega, by rw [keep.wr]; exact ctx.workspace.writable⟩
    rw [WP.seq_iff]
    refine WP.mono (shift_ok u shiftCtx (by omega) p0 count) ?_
    intro v sv
    have outside := sv.outside
    rw [mem] at outside
    have headerV := hdr.of_outside outside (by omega) (by omega)
    have quotient := shift_quotient sv
    rw [mem] at quotient
    have wv := ctx.workspace.congr (sv.rest.wr.trans keep.wr)
    refine WP.mono (roundFinish_ok v (tmp := tmp) wv (by omega) (by omega) sv.ptr) ?_
    rintro t ⟨memT, ptrT, zero, rest⟩
    have mt : t.mem = finishMem v.mem (State.addr base) (acc + 4 * (n + 1)) tmp := memT
    have nowrap' : (State.addr base).toNat + size ≤ 2 ^ 32 := by
      rw [VG.Proof.X25519.Arm.addr_toNat]
      exact nowrap
    obtain ⟨value, frame⟩ := finish_value (mem := v.mem) (acc := acc) (n := n) (tmp := tmp) nowrap' (by omega) rfl
      (show tmp = acc + 4 * (n + 1) + 12 by omega)
    rw [← mt] at value frame
    refine ⟨?_, ?_, ptrT, ?_, ?_, ?_⟩
    · rw [value, quotient]
      exact round_div_exact cancel
    · rw [mt]
      exact finish_meta nowrap ht (by omega) headerV hi
    · exact (Outs.of_outside (outside.mono (o' := acc) (n' := 4 * (n + 2)) (by omega) (by omega))
        (by simp)).trans frame
    · rw [zero, headerV.remaining]
      change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
      simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]
    · exact (keep.mono (by simp [roundClobbers])).trans
        ((sv.rest.mono (by simp [roundClobbers])).trans (rest.mono (by simp [roundClobbers])))

end VG.Proof.Bignum.Arm
