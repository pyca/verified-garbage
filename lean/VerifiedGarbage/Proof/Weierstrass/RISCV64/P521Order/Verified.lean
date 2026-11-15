module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Order
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Field
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Order
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Order.Lit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Order.Lit

/-!
# Arithmetic modulo P-521's order on RISC-V: verified

Each function meets a contract by register (`mulRV`, `addRV`, `subRV`), from
the functions of any wide modulus (`Proof/Weierstrass/RISCV64/GenWide/RV.lean`).
-/

-- Checking the facts of the modulus (`WideOk`) evaluates `2⁵²¹` and `2⁵⁷⁶`.
set_option exponentiation.threshold 1024

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P521Order

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.P521Order
open VG.Impl.Weierstrass.Mont (numAt p521n Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV)
open VG.Proof.Weierstrass.RISCV64.GenWide (WideOk)
open VG.Impl.Weierstrass.RISCV64.GenWide (wordOf negInv)

theorem wide : WideOk p521n := ⟨by decide, by decide, by decide, by decide⟩

theorem mul_rv (s : State) (hs : (mulRV p521n).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV p521n).post s s' :=
  GenWide.mul_rv wide s hs

theorem add_rv (s : State) (hs : (addRV p521n).pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ (addRV p521n).post s s' :=
  GenWide.add_rv wide s hs

theorem sub_rv (s : State) (hs : (subRV p521n).pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ (subRV p521n).post s s' :=
  GenWide.sub_rv wide s hs

theorem mulA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p521n)).pre s) :
    ∃ t s', Exec isa mulFnA s t s' ∧ abiPreserved s s' ∧ (mulRV p521n).post s s' :=
  GenWide.mulA_rv wide s hs

theorem addA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p521n)).pre s) :
    ∃ t s', Exec isa addFnA s t s' ∧ abiPreserved s s' ∧ (addRV p521n).post s s' :=
  GenWide.addA_rv wide s hs

theorem subA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p521n)).pre s) :
    ∃ t s', Exec isa subFnA s t s' ∧ abiPreserved s s' ∧ (subRV p521n).post s s' :=
  GenWide.subA_rv wide s hs

/-! The constant-time analyses of the functions for aligned offsets from their arguments, done
once for every check of code that calls them (`taint_decide_sum`), which keep what is public
of `s0`–`s11`: they write none of them. -/
taint_summary mulASum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3]) mulFnA
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary addASum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3]) addFnA
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary subASum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3]) subFnA
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

end VG.Proof.Weierstrass.RISCV64.P521Order
