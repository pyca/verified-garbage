module
public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Framework.Block

/-! # A complete ARMv7 Montgomery round, including its memory and loop state -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem montRound_ok (s : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (hdr : RoundMeta s.mem base tmp a b mod acc n i inv)
    (hi : i < n) (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (hT : val32 s.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n)
    (hInv : (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa montRound s fun t => RoundPost s t base tmp a b mod acc n i inv := by
  have nowrap := ctx.workspace.nowrap
  have mfits := ctx.mFits
  have sep := ctx.accM
  rw [montRound, WP.seq_iff]
  refine WP.mono (productStage_ok s ctx hdr hi ptr hT hB) ?_
  rintro u ⟨product, hdrU, ptrU, outsideU, keepU⟩
  have modulus := outsideU.val32 (d := mod) (k := n) (by omega) (by omega)
  have ctxU := ctx.congr keepU.wr
  let q := (inv * u.mem.readW (off (State.addr base) acc) 32).toNat
  have hq : q < 2 ^ 32 := (inv * u.mem.readW (off (State.addr base) acc) 32).isLt
  have ha : w32 s.mem (State.addr base) (a + 4 * i) < 2 ^ 32 :=
    (s.mem.readW (off (State.addr base) (a + 4 * i)) 32).isLt
  have capacity := round_fit hT ha hB hq (val32_lt s.mem (State.addr base) mod n)
  rw [WP.seq_iff]
  refine WP.mono (reductionStage_ok u ctxU hdrU ptrU (by rw [modulus]; exact hInv) ?_) ?_
  · rw [product, modulus]
    exact capacity
  · rintro v ⟨reduction, cancel, hdrV, ptrV, outsideV, keepV⟩
    refine WP.mono (quotientStage_ok v (ctxU.congr keepV.wr) hdrV hi ptrV cancel) ?_
    rintro t ⟨quotient, hdrT, ptrT, outsideT, zero, keepT⟩
    have value : 2 ^ 32 * val32 t.mem (State.addr base) acc (n + 2) =
        val32 s.mem (State.addr base) acc (n + 2) +
          w32 s.mem (State.addr base) (a + 4 * i) * val32 s.mem (State.addr base) b n +
            q * val32 s.mem (State.addr base) mod n := by
      rw [quotient, reduction, product, modulus]
    refine ⟨hdrT, ptrT, ⟨q, hq, value⟩, round_lt value hT ha hB hq, ?_, zero,
      keepU.trans (keepV.trans keepT)⟩
    exact (Outs.of_outside (outsideU.trans outsideV) (by simp)).trans outsideT

end VG.Proof.Bignum.Arm
