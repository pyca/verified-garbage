module

public import VerifiedGarbage.Impl.Rsa.Arm.PrivChecked
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.CrtPrecomputedContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved

/-! # Verified callees for the ARMv7 checked private operation

Each callee uses at most 56 stack bytes, and the codes its callers call
make no indirect call (`crtPNoIcall`, `pcNoIcall`, `pdNoIcall`): with their
stacks, what each variant gives of its own code for its callers' cleanup
(`Arm.Scrub.CodeOk`). Callers are generic over the CRT and its associated
public implementation, so future variants propagate.
-/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm

structure CrtImpl where
  name : String
  code : Prog isa
  verified : Verified target code (Proof.Rsa.privateCrtContract abi 56)
  stack : FrameStack.armStack code ≤ 56
  /-- `vg_rsa_private_crt_precomputed`, of the same arithmetic. -/
  crtPName : String
  crtP : Prog isa
  crtPVerified : Verified target crtP (Proof.Rsa.privateCrtPrecomputedContract abi 56)
  crtPStack : FrameStack.armStack crtP ≤ 56
  crtPNoIcall : noIcall crtP = true
  pcName : String
  pc : Prog isa
  pcVerified : Verified target pc (Spec.Rsa.publicPrecomputeContract abi 56)
  pcStack : FrameStack.armStack pc ≤ 56
  pcNoIcall : noIcall pc = true
  pdName : String
  pd : Prog isa
  pdVerified : Verified target pd (Proof.Rsa.publicPrecomputedCheckedContract abi 56)
  pdStack : FrameStack.armStack pd ≤ 56
  pdNoIcall : noIcall pd = true
  suffix : String
  features : List String

/-- What `vg_rsa_private_crt_precomputed`'s code gives its callers' cleanup. -/
theorem CrtImpl.crtPOk (v : CrtImpl) : Arm.Scrub.CodeOk v.crtP 56 := ⟨v.crtPStack, v.crtPNoIcall⟩

/-- What `vg_rsa_public_precompute`'s code gives its callers' cleanup. -/
theorem CrtImpl.pcOk (v : CrtImpl) : Arm.Scrub.CodeOk v.pc 56 := ⟨v.pcStack, v.pcNoIcall⟩

/-- What `vg_rsa_public_precomputed_checked`'s code gives its callers' cleanup. -/
theorem CrtImpl.pdOk (v : CrtImpl) : Arm.Scrub.CodeOk v.pd 56 := ⟨v.pdStack, v.pdNoIcall⟩

def privName (v : CrtImpl) : String := "vg_rsa_private_checked" ++ v.suffix
def privCode (v : CrtImpl) : Prog isa := Impl.Rsa.Arm.PrivChecked.code v.name v.code v.pcName v.pc v.pdName v.pd
def privNameP (v : CrtImpl) : String := "vg_rsa_private_checked_precomputed" ++ v.suffix
def privCodeP (v : CrtImpl) : Prog isa := Impl.Rsa.Arm.PrivChecked.codeP v.crtPName v.crtP v.pdName v.pd
/-- Inner frame, register save, and the largest callee frame. -/
def stackBytes : Nat := 3440
end VG.Proof.Rsa.Arm
