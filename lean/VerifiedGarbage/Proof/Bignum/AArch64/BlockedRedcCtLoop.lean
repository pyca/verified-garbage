module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtContext

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (eval_nonzero ne_zero_iff)

theorem row_ctx_next {L : Ws} {j : Nat} {s : State} (hj : j < blocks L) (h : LoopCtx L j s) :
    WP isa rowBody s fun t => LoopCtx L (j + 1) t ∧
      isa.eval (.nonzero .x .x12) t = some (decide (j + 1 < blocks L)) := by
  obtain ⟨mi, hg, hz⟩ := h.fast.1
  obtain ⟨hk, hkw, hHdr, hSize, hNQ⟩ := row_bounds h.fast hj
  obtain ⟨p, hp⟩ := word_flag (s.gpr .x10) h.carry
  have he : 8 * blocks L = L.w := by have := h.fast.2.2; dsimp [blocks]; omega
  refine WP.mono (rowBody_ok hg.scr hg.x0 h.ptr h.zero hp hHdr hSize hNQ hk hkw
    (hg.hdr.harr aN (by decide)) hg.hdr.hminv
    (hg.hdr.hw.trans (congrArg (BitVec.ofNat 64) he.symm)))
    fun t ⟨_, _, _, ho, hc, ht8, ht12, kt⟩ => ?_
  have ha := Square.scratch_arrays (ho.mono (o' := rawBase L) (n' := 8 * (2 * L.w + 2))
    (by dsimp [rowBase]; omega) (by dsimp [rowBase]; omega))
  have htCount : t.gpr .x12 = BitVec.ofNat 64 (blocks L - (j + 1)) := by
    exact (ht12.trans (congrArg (· - BitVec.ofNat 64 1) h.count)).trans
      ((BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)).trans
        (congrArg (BitVec.ofNat 64) (by omega)))
  refine ⟨⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0,
    ha.hdr hg.hdr⟩, hz⟩, h.fast.2⟩,
    ht8.trans (congrArg (off L.B) (by dsimp [rowBase]; omega)), htCount,
    (kt.gpr .x7 (by decide)).trans h.zero, hc⟩, ?_⟩
  rw [eval_nonzero, htCount, ne_zero_iff, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show blocks L - (j + 1) < 2 ^ 64 by omega)]
  simp only [Option.some.injEq, decide_eq_decide]
  omega

theorem rows_ct : RelCT isa (Two fun L s => 0 < blocks L ∧ LoopCtx L 0 s)
    (.loop rowBody (.nonzero .x .x12)) (Two fun L s => LoopCtx L (blocks L) s) := by
  apply two_loop blocks rowBody_ct
  intro L j s hj h
  refine WP.mono (row_ctx_next hj h) fun t ⟨ht, he⟩ => ⟨he, fun _ => ht, ?_⟩
  intro hlast
  exact hlast ▸ ht

end VG.Proof.Bignum.AArch64.BlockedRedc
