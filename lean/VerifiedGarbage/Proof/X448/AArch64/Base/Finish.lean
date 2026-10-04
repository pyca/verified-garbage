import VerifiedGarbage.Proof.X448.AArch64.Base.Setup
import VerifiedGarbage.Proof.X448.AArch64.Fast.Finish
import VerifiedGarbage.Proof.X448.AArch64.Fast.Inv

/-!
# X448 of the base point on AArch64: `Y² / X²`, encoded

Untrusted: everything here is checked by Lean. `Y²` and `X²` go to the ladder's
`x₂` and `z₂` slots; the ladder's inversion and finish (`Fast.invert_ok`,
`Fast.finish_ok`) encode `Y² · (X²)^(p-2)` to the output, reloaded from the
working space, and restore the callee-saved registers.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 Saved ofs)
open VG.Proof.X448.AArch64.Weak (Index Env invEnv invEnv_eval invEnv_x2)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- `Y²` to slot 1 and `X²` to slot 2. -/
theorem squares_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (.block (Impl.X448.AArch64.Fast.codeOf [.mul X2 AY AY, .mul Z2 AX AX])) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧
      EV t.mem base = Function.update (Function.update (EV s.mem base) 1 (EV s.mem base 1 * EV s.mem base 1)) 2
        (EV s.mem base 0 * EV s.mem base 0) := by
  refine block_codeOf (mulOp hs hb 1 1 1 (Or.inl rfl) fun t1 k1 b1 _ _ e1 => ?_)
  refine mulOp (k1.scr hs) b1 2 0 0 (Or.inl rfl) fun t2 k2 b2 _ _ e2 => WP.block_nil ⟨k1.trans k2, b2, ?_⟩
  rw [e2, e1]
  rfl

end VG.Proof.X448.AArch64.Base
