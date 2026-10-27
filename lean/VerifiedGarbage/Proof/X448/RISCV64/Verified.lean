module

public import VerifiedGarbage.Proof.X448.RISCV64.Main
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X448.RISCV64.CT
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# X448 on RISC-V: verified

`vg_x448` meets the shared contract of `Spec/X448/Contract.lean`: the
proof against `x448RISCV64`, which it implies, and a state satisfying it.
The code calls no function and writes only caller-saved registers (`WP.keep`),
so the ABI's obligations hold of every execution.
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64

open VG VG.RISCV64

theorem x448_ok (s : State) (hs : x448RISCV64.pre s) :
    ∃ t s', Exec isa Impl.X448.RISCV64.x448 s t s' ∧ abiPreserved s s' ∧ x448RISCV64.post s s' := by
  obtain ⟨t, s', he, h, hk⟩ := WP.keep [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2]
    (x448_correct (XPre.of hs)) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), h⟩

theorem x448_ct' : ConstantTime isa x448RISCV64.pre x448RISCV64.pub Impl.X448.RISCV64.x448 :=
  x448_ct fun _ _ _ _ ⟨h3, h4, h5, h6, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩

/-- A state satisfying the precondition. -/
def x448Sat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_verified :
    Verified RISCV64.target Impl.X448.RISCV64.x448 (Spec.X448.x448Contract RISCV64.abi) :=
  Verified.of_correct x448_ok x448_ct' (by
    contract_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, Proof.X448.RISCV64.x448RISCV64,
      RISCV64.abi, RISCV64.argRegs] [Proof.X448.RISCV64.x448Sat] using Proof.X448.RISCV64.x448Sat)

end VG.Proof.X448.RISCV64
