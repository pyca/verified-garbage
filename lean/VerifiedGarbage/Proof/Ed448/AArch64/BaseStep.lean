import VerifiedGarbage.Proof.Ed448.AArch64.BaseField
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters

/-!
# Ed448 verification on AArch64: a point swapped in by the mask of a bit

The mask of a bit (`mask_bit`), and the conditional swap of the point in
slots 3–5 into slots 0–2 (`swaps_ok`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps off contains_sc read1_eq Outside2 workRegs)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv cswapE opSwap decCounter_ok)
open VG.Proof.Curve448.AArch64 (mask)
open VG.Impl.X448.AArch64 (BITS ACC slot)

theorem mask_bit : ∀ b < 2, (0 : BitVec 64) - (BitVec.ofNat 8 b).setWidth 64 = mask (decide (b = 1)) := by
  decide

/-- The swaps of `T` into `R`. -/
theorem swaps_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {sw : Bool} (hm : s.gpr .x6 = mask sw) :
    WP isa (.block (Impl.Curve448.AArch64.cswap (slot 0) (slot 3) ++
        (Impl.Curve448.AArch64.cswap (slot 1) (slot 4) ++ Impl.Curve448.AArch64.cswap (slot 2) (slot 5)))) s
      fun t => Keep base s t ∧ BoundedEnv t.mem base ∧
        E t.mem base = opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw (E s.mem base))) := by
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs hb 0 3 (by decide) hm) fun t ⟨tk, tb, tc, te⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cswapE (tk.scr hs) tb 1 4 (by decide) (tc.trans hm)) fun u ⟨uk, ub, uc, ue⟩ => ?_
  refine WP.mono (cswapE (uk.scr (tk.scr hs)) ub 2 5 (by decide) (uc.trans (tc.trans hm)))
    fun v ⟨vk, vb, _, ve⟩ => ⟨(tk.trans uk).trans vk, vb, by rw [ve, ue, te]⟩

end VG.Proof.Ed448.AArch64
