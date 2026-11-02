module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Impl.Ecdsa.P192.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
meta import VerifiedGarbage.Impl.Ecdsa.P192.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit

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

theorem ct_mulP : CtOk (Impl.Weierstrass.RISCV64.Gen4.mulCore p192p4.m) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide)
theorem ct_addP : CtOk (.block (Impl.Weierstrass.RISCV64.Gen4.addCore p192p4.m)) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide)
theorem ct_subP : CtOk (.block (Impl.Weierstrass.RISCV64.Gen4.subCore p192p4.m)) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide)
theorem ct_mulN : CtOk (Impl.Weierstrass.RISCV64.Gen4.mulCore p192n4.m) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide)
theorem ct_addN : CtOk (.block (Impl.Weierstrass.RISCV64.Gen4.addCore p192n4.m)) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide)
theorem ct_subN : CtOk (.block (Impl.Weierstrass.RISCV64.Gen4.subCore p192n4.m)) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide)

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

theorem mul_verified : Verified RISCV64.target p192MulP (p192p4.mulContract RISCV64.abi) :=
  Gen4.mul_verified rfl ok_p ct_mulP
theorem add_verified : Verified RISCV64.target p192AddP (p192p4.addContract RISCV64.abi) :=
  Gen4.add_verified rfl ok_p ct_addP
theorem sub_verified : Verified RISCV64.target p192SubP (p192p4.subContract RISCV64.abi) :=
  Gen4.sub_verified rfl ok_p ct_subP
theorem mul_verified_n : Verified RISCV64.target p192MulN (p192n4.mulContract RISCV64.abi) :=
  Gen4.mul_verified rfl ok_n ct_mulN
theorem add_verified_n : Verified RISCV64.target p192AddN (p192n4.addContract RISCV64.abi) :=
  Gen4.add_verified rfl ok_n ct_addN
theorem sub_verified_n : Verified RISCV64.target p192SubN (p192n4.subContract RISCV64.abi) :=
  Gen4.sub_verified rfl ok_n ct_subN

end VG.Proof.Weierstrass.RISCV64.P192Field
