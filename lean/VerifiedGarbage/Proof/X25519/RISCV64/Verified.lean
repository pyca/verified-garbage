module

public import VerifiedGarbage.Proof.X25519.RISCV64.Main
public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.X25519.RISCV64.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# X25519 on RISC-V: verified

`vg_x25519` meets the shared contract of `Spec/X25519/Contract.lean`: the
proof against `x25519RISCV64`, which it implies, and a state satisfying it.
The code calls no function and writes only caller-saved registers (`WP.keep`),
so the ABI's obligations hold of every execution.
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64

open VG VG.RISCV64

theorem x25519_ok (s : State) (hs : x25519RISCV64.pre s) :
    ∃ t s', Exec isa Impl.X25519.RISCV64.x25519 s t s' ∧ abiPreserved s s' ∧ x25519RISCV64.post s s' := by
  obtain ⟨t, s', he, h, hk⟩ := WP.keep [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2]
    (x25519_correct (XPre.of hs)) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), h⟩

theorem x25519_ct' : ConstantTime isa x25519RISCV64.pre x25519RISCV64.pub Impl.X25519.RISCV64.x25519 :=
  x25519_ct fun _ _ _ _ ⟨h3, h4, h5, h6, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩

/-- A state satisfying the precondition. -/
def x25519Sat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_verified :
    Verified RISCV64.target Impl.X25519.RISCV64.x25519 (Spec.X25519.x25519Contract RISCV64.abi) :=
  Verified.of_correct x25519_ok x25519_ct' (by
    contract_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, Proof.X25519.RISCV64.x25519RISCV64,
      RISCV64.abi, RISCV64.argRegs] [Proof.X25519.RISCV64.x25519Sat] using Proof.X25519.RISCV64.x25519Sat)

end VG.Proof.X25519.RISCV64
