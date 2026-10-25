module

import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Impl.Bignum.Arm.Round
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The first multiply-add of a Montgomery round -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem productStage_ok (s : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (hdr : RoundMeta s.mem base tmp a b mod acc n i inv)
    (hi : i < n) (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (hT : val32 s.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n) :
    WP isa productStage s fun t =>
      val32 t.mem (State.addr base) acc (n + 2) = val32 s.mem (State.addr base) acc (n + 2) +
        w32 s.mem (State.addr base) (a + 4 * i) * val32 s.mem (State.addr base) b n ∧
      RoundMeta t.mem base tmp a b mod acc n i inv ∧
      t.gpr .r0 = base + BitVec.ofNat 32 (acc + 4 * n) ∧
      Outside (State.addr base) acc (4 * (n + 2)) s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits := ctx.aFits
  have hn := ctx.count
  have ht := ctx.tmpFits
  have layout := ctx.layout
  have nowrap := ctx.workspace.nowrap
  rw [productStage, WP.seq_iff]
  refine WP.mono (productArgs_ok s ctx.workspace ht (by omega) ptr hdr.aPtr hdr.count hdr.bPtr hdr.accPtr) ?_
  rintro u ⟨scalar, p0, p12, count, carry, mem, keep⟩
  have capacity := round_fit (u := 0) hT (s.mem.readW (off (State.addr base) (a + 4 * i)) 32).isLt
    hB (by decide) (val32_lt s.mem (State.addr base) mod n)
  refine WP.mono (rowFull_ok u (ctx.rowB keep.wr) (by omega) ctx.accFits p0 p12 count ?_) ?_
  · rw [mem, scalar, carry]
    simpa only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero, w32] using capacity
  · rintro t ⟨value, outside, ptop, rest⟩
    rw [mem] at outside
    refine ⟨?_, hdr.of_outside outside (by omega) (by omega), ptop, outside, ?_⟩
    · rw [value, mem, scalar, carry]
      simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, w32]
    · exact (keep.mono (by decide)).trans (rest.mono (by decide))

end VG.Proof.Bignum.Arm
