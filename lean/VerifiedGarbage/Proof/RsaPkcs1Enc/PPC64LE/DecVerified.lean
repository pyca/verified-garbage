module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCorrect
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCT4
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: verified against the shared contract

`fnContract` states the shared contract's postcondition on the registers and
the stack (`dec_implies`); with correctness (`code_correct`) and constant
time (`code_ct`), `code` is verified for the stack its frame and
`vg_rsa_private_checked`'s use (`dec_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pre
  post := fnPost
  pub := (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pub

/-- A state meeting the precondition: a 64-byte modulus, input and `out`,
one-byte exponents, primes, CRT exponents and `qInv`, and the stack
arguments at `0x10060`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1100 | .r6 => 0x2000 | .r7 => 64 | .r8 => 0x3000
    | .r9 => 1 | .r10 => 0x3100 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := if a = 0x10060 then 1 else if a = 0x10069 then 0x40 else if a = 0x10070 then 0x40
    else if a = 0x10079 then 0x41 else if a = 0x10080 then 1 else if a = 0x10089 then 0x42
    else if a = 0x10090 then 1 else if a = 0x10099 then 0x43 else if a = 0x100A0 then 1
    else if a = 0x100A9 then 0x44 else if a = 0x100B0 then 1 else if a = 0x100B9 then 0x45
    else if a = 0x100C0 then 1 else if a = 0x100CA then 0x02 else if a = 0x100D0 then 0x20
    else if a = 0x100D1 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x4000, 64⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩,
    ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x10060, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x20000, 8448⟩]

theorem dec_implies : fnContract.Implies (Spec.RsaPkcs1Enc.decryptContract abi stackBytes) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, fnContract,
      fnPost, stackArgs_fifteen, List.append_eq, dOf, cOf]
  pub := fun _ _ _ _ h => h
  sat := by
    sig_implies_sat [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, fnContract,
      stackArgs_fifteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

/-- `vg_rsa_pkcs1_decrypt`. -/
theorem dec_verified : Verified target code (Spec.RsaPkcs1Enc.decryptContract abi stackBytes) :=
  Verified.of_correct code_correct code_ct dec_implies

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
