module

public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RC2 on RISC-V: running blocks

`rrun [facts]` runs a block of the RC2 code symbolically (`mrun`), keeping
16-bit loads as `Mem.readW` and byte stores as `Mem.writeW`, as the PPC64LE proofs' `rrun`
(`Proof/Rc2/PPC64LE/Run.lean`) does; and the loops' conditions.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64

theorem read_two (m : Mem) (a : Addr) : m.read a 2 = m.readW a 16 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem write_one (m : Mem) (a : Addr) (v : BitVec 8) : m.write a 1 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

/-- Steps a block of the RC2 code. -/
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic| mrun [↓read_two, write_one, $ls,*])

/-- A loop counting to `stop`, exiting when `r` is zero. -/
theorem countLoop (body : Prog isa) (r : Reg) (I : Nat → State → Prop) (stop : Nat)
    (step : ∀ i < stop, ∀ s, I i s → WP isa body s (fun s' =>
      I (i + 1) s' ∧ (s'.gpr r != (0 : BitVec 64)) = !decide (i + 1 = stop)))
    (i : Nat) (hi : i < stop) (s : State) (hs : I i s) :
    WP isa (.loop body (.nonzero r)) s (I stop) := by
  refine WP.loop (M := isa) (fun n s => ∃ i, i < stop ∧ stop - i = n ∧ I i s) ?_ (stop - i) s ⟨i, hi, rfl, hs⟩
  intro n s ⟨j, hj, hn, hI⟩
  refine WP.mono (step j hj s hI) fun s' ⟨h', hc⟩ => ?_
  by_cases he : j + 1 = stop
  · left
    rw [Steps.eval_nonzero, hc, he]
    exact ⟨by simp, he ▸ h'⟩
  · right
    rw [Steps.eval_nonzero, hc]
    exact ⟨by simp [he], stop - (j + 1), by omega, j + 1, by omega, rfl, h'⟩

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.ofNat_add]

theorem sub_bne {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y != (0 : BitVec 64)) = !decide (x = y) := by
  rw [bne, ← Offset.ofNat_sub_ofNat_beq hx hy]

end VG.Proof.Rc2.RISCV64
