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

theorem ldOut_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [ld .x1 OUT]) s fun t =>
      t.gpr .x1 = word s.mem base OUT ∧ t.mem = s.mem ∧ Keeps [.x1] s t := by
  have hr := hs.read (d := OUT) (n := 8) (by decide)
  have enc : OUT % 8 = 0 ∧ OUT < 4096 * 8 := by decide
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.load, enc, and_self, BitVec.setWidth_eq,
    hs.x3, hr, RegUpd.gpr_write, RegUpd.mem_write,
    ite_true, Option.map_some, Option.bind_some,
    VG.Proof.X448.AArch64.read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.X448.AArch64.Base
