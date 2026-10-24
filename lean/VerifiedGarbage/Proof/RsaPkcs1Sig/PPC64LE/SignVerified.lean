module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Sign
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignCorrect
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignCT
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: verified against the shared contract

`fnContract` states the shared contract's postcondition on the registers and
the stack (`sign_implies`); with correctness (`code_correct`) and constant
time (`code_ct`), `code` is verified for the `stackBytes` bytes of stack its
frame and `vg_rsa_private_checked`'s use (`code_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Spec.RsaPkcs1Sig.signContract abi stackBytes).pre
  post := fnPost
  pub := (Spec.RsaPkcs1Sig.signContract abi stackBytes).pub

/-- A state meeting the precondition: a 64-byte modulus and `out`, a one-byte
exponent, primes, exponents and `qInv`, a SHA-256 hash value, and the stack
arguments at `0x10060`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x3000 | .r8 => 1
    | .r9 => 3 | .r10 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := if a = 0x10060 then 0x20 else if a = 0x10069 then 0x41 else if a = 0x10070 then 1
    else if a = 0x10079 then 0x42 else if a = 0x10080 then 1 else if a = 0x10089 then 0x43
    else if a = 0x10090 then 1 else if a = 0x10099 then 0x44 else if a = 0x100A0 then 1
    else if a = 0x100A9 then 0x45 else if a = 0x100B0 then 1 else if a = 0x100BA then 0x02
    else if a = 0x100C0 then 0x20 else if a = 0x100C1 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 32⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x10060, 104⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

theorem sign_implies : fnContract.Implies (Spec.RsaPkcs1Sig.signContract abi stackBytes) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, fnContract,
      fnPost, hashOf, stackArgs_thirteen, List.append_eq]
  pub := fun _ _ _ _ h => h
  sat := by
    sig_implies_sat [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, fnContract,
      stackArgs_thirteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using satState

/-- `vg_rsa_pkcs1_sign`. -/
theorem code_verified : Verified target code (Spec.RsaPkcs1Sig.signContract abi stackBytes) :=
  Verified.of_correct code_correct code_ct sign_implies

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign
