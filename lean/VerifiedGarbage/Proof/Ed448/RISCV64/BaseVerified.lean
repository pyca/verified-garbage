module

public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseMain
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# `vg_ed448_scalar_base` on RISC-V, verified

The function meets its contract of `Spec/Ed448/Contract.lean`, with no
stack: the proof against `baseRISCV64`, which it implies, and a state satisfying
it. The correctness proof carries register preservation through the shared
addition-chain call, establishing the ABI obligations.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64

theorem scalarBase_ok (hl : Proof.Ed448.BaseLadder2Ok) (s : State) (hs : baseRISCV64.pre s) :
    ∃ t s', Exec isa Impl.Ed448.RISCV64.scalarBase s t s' ∧ abiPreserved s s' ∧ baseRISCV64.post s s' := by
  obtain ⟨t, s', he, h, hr⟩ := scalarBase_correct hl hs
  exact ⟨t, s', he, ⟨fun r hm => hr.gpr r (by cases r <;> simp_all [preserved]),
    hr.sp, hr.gpr .ra (by decide)⟩, h⟩

end VG.Proof.Ed448.RISCV64
