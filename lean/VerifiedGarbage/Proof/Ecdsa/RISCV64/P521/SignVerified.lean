module

-- separate module: its taint check (the code's literal, evaluated) costs more than its imports,
-- and its importer's changes need not re-run it

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.Sign
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.Sign
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignLit
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.CombVerified
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.CombVerified
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.CombU
meta import VerifiedGarbage.Impl.Weierstrass.Layout.Mont
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Field.Verified
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Field.Verified
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Order.Verified
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Order.Verified

/-!
# ECDSA signatures over P-521 on RISC-V: constant time

`vg_ecdsa_p521_sign`'s constant time, by taint tracking (only the pointers,
in `a0`–`a4`, and the comb's table's address public: every address is a
pointer or the table's address plus a constant, and the only branches are
the callees' loops, on their counters), for its calls by
RFC 6979's signature (`Proof/Ecdsa/Rfc6979/RISCV64/P521.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P521

open VG VG.RISCV64

/-! The constant-time analyses of the calls of the functions of P-521's `n` from their arguments,
with the comb's table public, each done once for every check of code that calls it
(`taint_decide_sum`), which keep what is public of `s0`–`s11`: the functions write none of them. -/
taint_summary nMulSymSum : (taintSym [Impl.Ecdsa.RISCV64.CombU.p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p521n.fn "mul") Impl.Weierstrass.RISCV64.P521Order.mulFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary nAddSymSum : (taintSym [Impl.Ecdsa.RISCV64.CombU.p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p521n.fn "add") Impl.Weierstrass.RISCV64.P521Order.addFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

theorem sign_ct : ConstantTime isa signRVC.pre signRVC.pub Impl.Ecdsa.RISCV64.P521.signP521 :=
  VG.Taint.constantTime_of_exists (A := taintSym [Impl.Ecdsa.RISCV64.CombU.p521Sym])
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ ⟨⟨hsp, h0, h1, h2, h3, h4⟩, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    (by taint_decide_sum [Comb.mulGSum, Comb.pMulSymSum, nMulSymSum, nAddSymSum])

end VG.Proof.Ecdsa.RISCV64.P521
