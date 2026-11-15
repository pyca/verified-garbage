module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Impl.Ecdsa.P192.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
meta import VerifiedGarbage.Impl.Ecdsa.P192.RISCV64
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-!
# Arithmetic modulo P-192's `p` and `n` on RISC-V: verified

The functions of any four-word modulus (`Proof/Weierstrass/RISCV64/Gen4.lean`)
for P-192's `p` and `n`: each modulus meets `Ok` (`ok_p`, `ok_n`, by
`decide`), and the taint analysis finds each operation constant time.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P192Field

open VG VG.RISCV64
open VG.Impl.Ecdsa.RISCV64 (p192p4 p192n4)
open VG.Proof.Weierstrass.RISCV64 (mulRV addRV subRV)
open VG.Impl.Ecdsa.RISCV64 (p192MulP p192AddP p192SubP p192MulN p192AddN p192SubN)
open VG.Proof.Weierstrass.RISCV64.Gen4 (Ok CtOk)

theorem ok_p : Ok p192p4.m := ⟨by decide, by decide, by decide⟩
theorem ok_n : Ok p192n4.m := ⟨by decide, by decide, by decide⟩

theorem mul_rv (s : State) (hs : (mulRV p192p4).pre s) :
    ∃ t s', Exec isa p192MulP s t s' ∧ abiPreserved s s' ∧ (mulRV p192p4).post s s' := Gen4.mul_rv rfl ok_p s hs
theorem add_rv (s : State) (hs : (addRV p192p4).pre s) :
    ∃ t s', Exec isa p192AddP s t s' ∧ abiPreserved s s' ∧ (addRV p192p4).post s s' := Gen4.add_rv rfl ok_p s hs
theorem sub_rv (s : State) (hs : (subRV p192p4).pre s) :
    ∃ t s', Exec isa p192SubP s t s' ∧ abiPreserved s s' ∧ (subRV p192p4).post s s' := Gen4.sub_rv rfl ok_p s hs
theorem mul_rv_n (s : State) (hs : (mulRV p192n4).pre s) :
    ∃ t s', Exec isa p192MulN s t s' ∧ abiPreserved s s' ∧ (mulRV p192n4).post s s' := Gen4.mul_rv rfl ok_n s hs
theorem add_rv_n (s : State) (hs : (addRV p192n4).pre s) :
    ∃ t s', Exec isa p192AddN s t s' ∧ abiPreserved s s' ∧ (addRV p192n4).post s s' := Gen4.add_rv rfl ok_n s hs
theorem sub_rv_n (s : State) (hs : (subRV p192n4).pre s) :
    ∃ t s', Exec isa p192SubN s t s' ∧ abiPreserved s s' ∧ (subRV p192n4).post s s' := Gen4.sub_rv rfl ok_n s hs

theorem mulA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p192p4)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p192MulPA s t s' ∧ abiPreserved s s' ∧ (mulRV p192p4).post s s' :=
  Gen4.mulA_rv rfl ok_p s hs
theorem addA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p192p4)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p192AddPA s t s' ∧ abiPreserved s s' ∧ (addRV p192p4).post s s' :=
  Gen4.addA_rv rfl ok_p s hs
theorem subA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p192p4)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p192SubPA s t s' ∧ abiPreserved s s' ∧ (subRV p192p4).post s s' :=
  Gen4.subA_rv rfl ok_p s hs
theorem mulA_rv_n (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p192n4)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p192MulNA s t s' ∧ abiPreserved s s' ∧ (mulRV p192n4).post s s' :=
  Gen4.mulA_rv rfl ok_n s hs
theorem addA_rv_n (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p192n4)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p192AddNA s t s' ∧ abiPreserved s s' ∧ (addRV p192n4).post s s' :=
  Gen4.addA_rv rfl ok_n s hs
theorem subA_rv_n (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p192n4)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p192SubNA s t s' ∧ abiPreserved s s' ∧ (subRV p192n4).post s s' :=
  Gen4.subA_rv rfl ok_n s hs

/-! The constant-time analyses of the calls of the functions of P-192's `p` from their arguments,
each done once for every check of code that calls it (`taint_decide_sum`), which keep what is public
of `s0`–`s6`: the functions write none of them. -/
taint_summary mulASum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Ecdsa.RISCV64.p192p4.fn "mul") Impl.Ecdsa.RISCV64.p192MulPA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6])
taint_summary addASum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Ecdsa.RISCV64.p192p4.fn "add") Impl.Ecdsa.RISCV64.p192AddPA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6])
taint_summary subASum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Ecdsa.RISCV64.p192p4.fn "sub") Impl.Ecdsa.RISCV64.p192SubPA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6])

/-! The constant-time analyses of the calls of the functions of P-192's `n` from their arguments,
each done once for every check of code that calls it (`taint_decide_sum`), which keep what is public
of `s0`–`s6`: the functions write none of them. -/
taint_summary mulASum_n : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Ecdsa.RISCV64.p192n4.fn "mul") Impl.Ecdsa.RISCV64.p192MulNA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6])
taint_summary addASum_n : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Ecdsa.RISCV64.p192n4.fn "add") Impl.Ecdsa.RISCV64.p192AddNA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6])

end VG.Proof.Weierstrass.RISCV64.P192Field
