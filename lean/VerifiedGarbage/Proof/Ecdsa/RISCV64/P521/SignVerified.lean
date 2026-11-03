module

-- separate module: its taint check (the code's literal, evaluated) costs more than its imports,
-- and its importer's changes need not re-run it

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.Sign
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.Sign
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignLit

/-!
# ECDSA signatures over P-521 on RISC-V: constant time

`vg_ecdsa_p521_sign`'s constant time, by taint tracking (only the pointers,
in `a0`–`a4`, public: every address is a pointer plus a constant, and the
only branches are the callees' loops, on their counters), for its calls by
RFC 6979's signature (`Proof/Ecdsa/Rfc6979/RISCV64/P521.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P521

open VG VG.RISCV64

theorem sign_ct : ConstantTime isa signRV.pre signRV.pub Impl.Ecdsa.RISCV64.P521.signP521 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2, h3, h4⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩) (by taint_decide)

end VG.Proof.Ecdsa.RISCV64.P521
