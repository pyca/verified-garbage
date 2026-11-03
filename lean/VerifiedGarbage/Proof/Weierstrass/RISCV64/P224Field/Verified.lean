module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Impl.Ecdsa.P224.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P224Field.Lit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
meta import VerifiedGarbage.Impl.Ecdsa.P224.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P224Field.Lit

/-!
# Arithmetic modulo P-224's `p` and `n` on RISC-V: verified

The functions of any four-word modulus (`Proof/Weierstrass/RISCV64/Gen4.lean`)
for P-224's `p` and `n`: each modulus meets `Ok` (`ok_p`, `ok_n`, by
`decide`), and the taint analysis finds each operation constant time.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P224Field

open VG VG.RISCV64
open VG.Impl.Weierstrass.Mont (p224p p224n)
open VG.Proof.Weierstrass.RISCV64 (mulRV addRV subRV)
open VG.Impl.Ecdsa.RISCV64 (p224MulP p224AddP p224SubP p224MulN p224AddN p224SubN)
open VG.Proof.Weierstrass.RISCV64.Gen4 (Ok CtOk)

theorem ok_p : Ok p224p.m := ⟨by decide, by decide, by decide⟩
theorem ok_n : Ok p224n.m := ⟨by decide, by decide, by decide⟩

theorem ct_mulP : CtOk (Impl.Weierstrass.RISCV64.Gen4.mulCore p224p.m) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide)
theorem ct_addP : CtOk (.block (Impl.Weierstrass.RISCV64.Gen4.addCore p224p.m)) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide)
theorem ct_subP : CtOk (.block (Impl.Weierstrass.RISCV64.Gen4.subCore p224p.m)) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide)
theorem ct_mulN : CtOk (Impl.Weierstrass.RISCV64.Gen4.mulCore p224n.m) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide)
theorem ct_addN : CtOk (.block (Impl.Weierstrass.RISCV64.Gen4.addCore p224n.m)) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide)
theorem ct_subN : CtOk (.block (Impl.Weierstrass.RISCV64.Gen4.subCore p224n.m)) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide)

theorem mul_rv (s : State) (hs : (mulRV p224p).pre s) :
    ∃ t s', Exec isa p224MulP s t s' ∧ abiPreserved s s' ∧ (mulRV p224p).post s s' := Gen4.mul_rv rfl ok_p s hs
theorem add_rv (s : State) (hs : (addRV p224p).pre s) :
    ∃ t s', Exec isa p224AddP s t s' ∧ abiPreserved s s' ∧ (addRV p224p).post s s' := Gen4.add_rv rfl ok_p s hs
theorem sub_rv (s : State) (hs : (subRV p224p).pre s) :
    ∃ t s', Exec isa p224SubP s t s' ∧ abiPreserved s s' ∧ (subRV p224p).post s s' := Gen4.sub_rv rfl ok_p s hs
theorem mul_rv_n (s : State) (hs : (mulRV p224n).pre s) :
    ∃ t s', Exec isa p224MulN s t s' ∧ abiPreserved s s' ∧ (mulRV p224n).post s s' := Gen4.mul_rv rfl ok_n s hs
theorem add_rv_n (s : State) (hs : (addRV p224n).pre s) :
    ∃ t s', Exec isa p224AddN s t s' ∧ abiPreserved s s' ∧ (addRV p224n).post s s' := Gen4.add_rv rfl ok_n s hs
theorem sub_rv_n (s : State) (hs : (subRV p224n).pre s) :
    ∃ t s', Exec isa p224SubN s t s' ∧ abiPreserved s s' ∧ (subRV p224n).post s s' := Gen4.sub_rv rfl ok_n s hs

theorem mulA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p224p)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p224MulPA s t s' ∧ abiPreserved s s' ∧ (mulRV p224p).post s s' :=
  Gen4.mulA_rv rfl ok_p s hs
theorem addA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p224p)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p224AddPA s t s' ∧ abiPreserved s s' ∧ (addRV p224p).post s s' :=
  Gen4.addA_rv rfl ok_p s hs
theorem subA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p224p)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p224SubPA s t s' ∧ abiPreserved s s' ∧ (subRV p224p).post s s' :=
  Gen4.subA_rv rfl ok_p s hs
theorem mulA_rv_n (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p224n)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p224MulNA s t s' ∧ abiPreserved s s' ∧ (mulRV p224n).post s s' :=
  Gen4.mulA_rv rfl ok_n s hs
theorem addA_rv_n (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p224n)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p224AddNA s t s' ∧ abiPreserved s s' ∧ (addRV p224n).post s s' :=
  Gen4.addA_rv rfl ok_n s hs
theorem subA_rv_n (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p224n)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p224SubNA s t s' ∧ abiPreserved s s' ∧ (subRV p224n).post s s' :=
  Gen4.subA_rv rfl ok_n s hs

theorem mul_verified : Verified RISCV64.target p224MulP (p224p.mulContract RISCV64.abi) :=
  Gen4.mul_verified rfl ok_p ct_mulP
theorem add_verified : Verified RISCV64.target p224AddP (p224p.addContract RISCV64.abi) :=
  Gen4.add_verified rfl ok_p ct_addP
theorem sub_verified : Verified RISCV64.target p224SubP (p224p.subContract RISCV64.abi) :=
  Gen4.sub_verified rfl ok_p ct_subP
theorem mul_verified_n : Verified RISCV64.target p224MulN (p224n.mulContract RISCV64.abi) :=
  Gen4.mul_verified rfl ok_n ct_mulN
theorem add_verified_n : Verified RISCV64.target p224AddN (p224n.addContract RISCV64.abi) :=
  Gen4.add_verified rfl ok_n ct_addN
theorem sub_verified_n : Verified RISCV64.target p224SubN (p224n.subContract RISCV64.abi) :=
  Gen4.sub_verified rfl ok_n ct_subN

end VG.Proof.Weierstrass.RISCV64.P224Field
