module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
import VerifiedGarbage.Proof.Bignum.Arm.CrtContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Bignum.Words

/-! # ARMv7 private CRT RSA is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

/-- Separate buffers for a 64-byte modulus and 32-byte factors, with native stack arguments. -/
def crtSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else
    if a = 0x8004 then 0x40 else
    if a = 0x8009 then 0x31 else
    if a = 0x800c then 0x20 else
    if a = 0x8011 then 0x32 else
    if a = 0x8014 then 0x20 else
    if a = 0x8019 then 0x33 else
    if a = 0x801c then 0x20 else
    if a = 0x8021 then 0x34 else
    if a = 0x8024 then 0x20 else
    if a = 0x8029 then 0x35 else
    if a = 0x802c then 0x20 else
    if a = 0x8031 then 0x40 else
    if a = 0x8034 then 0x20 else
    if a = 0x8035 then 0x4 else
    0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩, ⟨0x3200, 32⟩,
    ⟨0x3300, 32⟩, ⟨0x3400, 32⟩, ⟨0x3500, 32⟩, ⟨0x8000, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem crt_contract_sat : ∃ s, (Proof.Rsa.privateCrtContract abi 56).pre s := by
  sig_implies_sat [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [crtSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
      Spec.Rsa.scratchWords] using crtSatState

theorem crt_verified (kernel : WindowKernel := baselineWindowKernel) : Verified target (CrtFn.codeWith kernel.code) (Proof.Rsa.privateCrtContract abi 56) :=
  ⟨(crt_contract_correct (kernel := kernel)), (crt_contract_ct (kernel := kernel)), crt_contract_sat⟩

end VG.Proof.Bignum.Arm
