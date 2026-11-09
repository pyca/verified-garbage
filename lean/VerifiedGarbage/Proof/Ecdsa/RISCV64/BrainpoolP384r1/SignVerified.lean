module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Sign
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.SignLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Sign
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.SignLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA signatures over brainpoolP384r1 on RISC-V: constant time

`vg_ecdsa_brainpoolp384r1_sign`'s constant time, by taint tracking (only the pointers,
in `a0`–`a4`, public: every address is a pointer plus a constant, and the
only branches are the callees' loops, on their counters), for its calls by
RFC 6979's signature (`Proof/Ecdsa/Rfc6979/RISCV64/BrainpoolP384r1.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1

open VG VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Sign

theorem sign_ct : ConstantTime isa signRV.pre signRV.pub signBrainpoolP384r1 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2, h3, h4⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩) (by taint_decide)

end VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1
