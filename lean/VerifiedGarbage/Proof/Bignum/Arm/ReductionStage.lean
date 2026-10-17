module

public import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
public import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The cancellation multiply-add of a Montgomery round -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem reductionStage_ok (s : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (hdr : RoundMeta s.mem base tmp a b mod acc n i inv)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 (acc + 4 * n))
    (hInv : (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0)
    (hfit : val32 s.mem (State.addr base) acc (n + 2) +
      (inv * s.mem.readW (off (State.addr base) acc) 32).toNat * val32 s.mem (State.addr base) mod n <
        2 ^ (32 * (n + 2))) :
    WP isa reductionStage s fun t =>
      val32 t.mem (State.addr base) acc (n + 2) = val32 s.mem (State.addr base) acc (n + 2) +
        (inv * s.mem.readW (off (State.addr base) acc) 32).toNat * val32 s.mem (State.addr base) mod n ∧
      val32 t.mem (State.addr base) acc (n + 2) % 2 ^ 32 = 0 ∧
      RoundMeta t.mem base tmp a b mod acc n i inv ∧
      t.gpr .r0 = base + BitVec.ofNat 32 (acc + 4 * n) ∧
      Outside (State.addr base) acc (4 * (n + 2)) s.mem t.mem ∧ Rest roundClobbers s t := by
  have hn := ctx.count
  have ht := ctx.tmpFits
  have layout := ctx.layout
  have nowrap := ctx.workspace.nowrap
  have fits := ctx.accFits
  rw [reductionStage, WP.seq_iff]
  refine WP.mono (reductionArgs_ok s (acc := acc) (mod := mod) (n := n) inv ctx.workspace (by omega) (by omega) ptr ?_ ?_ ?_ ?_) ?_
  · simpa only [show acc + 4 * n + 16 = tmp by omega] using hdr.count
  · simpa only [show acc + 4 * n + 24 = tmp + 8 by omega] using hdr.mPtr
  · simpa only [show acc + 4 * n + 28 = tmp + 12 by omega] using hdr.inverse
  · simpa only [show acc + 4 * n + 44 = tmp + 28 by omega] using hdr.accPtr
  · rintro u ⟨scalar, p0, p12, count, carry, mem, keep⟩
    refine WP.mono (rowFull_ok u (ctx.rowM keep.wr) (by omega) fits p0 p12 count ?_) ?_
    · rw [mem, scalar, carry]
      simpa only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero] using hfit
    · rintro t ⟨value, outside, ptop, rest⟩
      rw [mem] at outside
      have result : val32 t.mem (State.addr base) acc (n + 2) =
          val32 s.mem (State.addr base) acc (n + 2) +
            (inv * s.mem.readW (off (State.addr base) acc) 32).toNat * val32 s.mem (State.addr base) mod n := by
        rw [value, mem, scalar, carry]
        simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero]
      refine ⟨result, ?_, hdr.of_outside outside (by omega) (by omega), ptop, outside, ?_⟩
      · exact round_cancel hInv (coefficient_value inv s.mem (State.addr base) acc (n + 1)) result
      · exact (keep.mono (by simp [roundClobbers])).trans (rest.mono (by simp [loopClobbers, roundClobbers]))

end VG.Proof.Bignum.Arm
