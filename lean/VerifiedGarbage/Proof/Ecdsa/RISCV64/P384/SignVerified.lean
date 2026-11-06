module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.Sign
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Ecdsa.P384
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.SignLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.Sign
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Spec.Ecdsa.P384
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.SignLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA signatures over P-384 on RISC-V: constant time

`vg_ecdsa_p384_sign`'s constant time, by taint tracking (only the pointers,
in `a0`–`a4`, and the comb's table's address public: every address is a
pointer or the table's address plus a constant, and the only branches are
the callees' loops, on their counters), for its calls by
RFC 6979's signature (`Proof/Ecdsa/Rfc6979/RISCV64/P384.lean`).
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.RISCV64.P384

open VG VG.RISCV64 VG.Impl.Ecdsa.RISCV64.Sign

theorem sign_ct : ConstantTime isa signRVC.pre signRVC.pub signP384 :=
  VG.Taint.constantTime (A := taintSym [Impl.Ecdsa.RISCV64.Comb.p384Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ ⟨⟨hsp, h0, h1, h2, h3, h4⟩, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

end VG.Proof.Ecdsa.RISCV64.P384
