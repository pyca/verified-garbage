module

public import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Turning a zero or equality accumulator into an acceptance mask -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- Compare an accumulator with zero without branching, optionally invert
the predicate. Used for zero tests, byte-string equality, range and one
checks. (`zeroMask_ok`, `Masks.lean`, is the comparison alone.) -/
theorem testMask_ok (r : Reg) (invert : Bool) {s : State} :
    WP isa (.block (([mov .x3 r] : List Instr) ++ Checks.zeroMask ++
      (if invert then [.logic .eor .x .x15 .x15 .x4] else []))) s fun t =>
      t.gpr .x15 = mask (if invert then !decide (s.gpr r = 0) else decide (s.gpr r = 0)) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4, .x7, .x15] s t := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun u => u.gpr .x3 = s.gpr r ∧ u.mem = s.mem) (by brun) rfl rfl rfl)
    fun u ⟨⟨hu3, hum⟩, hku⟩ => ?_
  refine WP.mono (zeroMask_ok u) fun v ⟨⟨hv15, hv4, _, hvm⟩, hkv⟩ => ?_
  rw [hu3] at hv15
  cases invert
  · exact WP.block_nil ⟨hv15, hvm.trans hum, (hku.trans hkv).mono (by decide)⟩
  · refine WP.mono (WP.keep [.x15] (Q := fun t =>
      t.gpr .x15 = mask (!decide (s.gpr r = 0)) ∧ t.mem = v.mem)
      (by brun [hv15, hv4, mask_true, mask_complement]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨ht, htm⟩, hkt⟩ => ⟨ht, htm.trans (hvm.trans hum), ((hku.trans hkv).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
