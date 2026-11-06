module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Field
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Field
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Mersenne
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Field
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Arithmetic modulo P-521's prime on RISC-V: verified

Each function meets a contract by register (`mulRV`, `addRV`, `subRV`), from
the functions of any wide modulus (`Proof/Weierstrass/RISCV64/GenWide/RV.lean`)
and, for the product, its Mersenne form (`Proof/Weierstrass/RISCV64/P521Mersenne.lean`).
-/

-- Checking the facts of the modulus (`WideOk`) evaluates `2⁵²¹` and `2⁵⁷⁶`.
set_option exponentiation.threshold 1024

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P521Field

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.P521Field
open VG.Impl.Weierstrass.Mont (numAt p521p Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV)
open VG.Proof.Weierstrass.RISCV64.GenWide (WideOk)
open VG.Impl.Weierstrass.RISCV64.GenWide (wordOf negInv)

theorem wide : WideOk p521p := ⟨by decide, by decide, by decide, by decide⟩

theorem mul_rv (s : State) (hs : (mulRV p521p).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV p521p).post s s' :=
  P521Mersenne.mul_rv s hs

theorem add_rv (s : State) (hs : (addRV p521p).pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ (addRV p521p).post s s' :=
  GenWide.add_rv wide s hs

theorem sub_rv (s : State) (hs : (subRV p521p).pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ (subRV p521p).post s s' :=
  GenWide.sub_rv wide s hs

theorem mulA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p521p)).pre s) :
    ∃ t s', Exec isa mulFnA s t s' ∧ abiPreserved s s' ∧ (mulRV p521p).post s s' :=
  P521Mersenne.mulA_rv s hs

theorem addA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p521p)).pre s) :
    ∃ t s', Exec isa addFnA s t s' ∧ abiPreserved s s' ∧ (addRV p521p).post s s' :=
  GenWide.addA_rv wide s hs

theorem subA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p521p)).pre s) :
    ∃ t s', Exec isa subFnA s t s' ∧ abiPreserved s s' ∧ (subRV p521p).post s s' :=
  GenWide.subA_rv wide s hs


end VG.Proof.Weierstrass.RISCV64.P521Field
