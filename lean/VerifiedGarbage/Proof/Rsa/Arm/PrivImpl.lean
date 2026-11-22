module

public import VerifiedGarbage.Impl.Rsa.Arm.PrivChecked
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.CrtPrecomputedContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved

/-! # Verified callees for the ARMv7 checked private operation

The private CRT uses at most 104 stack bytes, its frame and the Montgomery
product it calls, and every other callee at most 56; the codes its callers call
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
  verified : Verified target code (Proof.Rsa.privateCrtContract abi 104)
  stack : FrameStack.armStack code ≤ 104
  /-- `vg_rsa_private_crt_precomputed`, of the same arithmetic. -/
  crtPName : String
  crtP : Prog isa
  crtPVerified : Verified target crtP (Proof.Rsa.privateCrtPrecomputedContract abi 104)
  crtPStack : FrameStack.armStack crtP ≤ 104
  crtPNoIcall : noIcall crtP = true
  pcName : String
  pc : Prog isa
  pcVerified : Verified target pc (Spec.Rsa.publicPrecomputeContract abi 104)
  pcStack : FrameStack.armStack pc ≤ 104
  pcNoIcall : noIcall pc = true
  pdName : String
  pd : Prog isa
  pdVerified : Verified target pd (Proof.Rsa.publicPrecomputedCheckedContract abi 104)
  pdStack : FrameStack.armStack pd ≤ 104
  pdNoIcall : noIcall pd = true
  suffix : String
  features : List String

/-- What `vg_rsa_private_crt_precomputed`'s code gives its callers' cleanup. -/
theorem CrtImpl.crtPOk (v : CrtImpl) : Arm.Scrub.CodeOk v.crtP 104 := ⟨v.crtPStack, v.crtPNoIcall⟩

/-- What `vg_rsa_public_precompute`'s code gives its callers' cleanup. -/
theorem CrtImpl.pcOk (v : CrtImpl) : Arm.Scrub.CodeOk v.pc 104 := ⟨v.pcStack, v.pcNoIcall⟩

/-- What `vg_rsa_public_precomputed_checked`'s code gives its callers' cleanup. -/
theorem CrtImpl.pdOk (v : CrtImpl) : Arm.Scrub.CodeOk v.pd 104 := ⟨v.pdStack, v.pdNoIcall⟩

def privName (v : CrtImpl) : String := "vg_rsa_private_checked" ++ v.suffix
def privCode (v : CrtImpl) : Prog isa := Impl.Rsa.Arm.PrivChecked.code v.name v.code v.pcName v.pc v.pdName v.pd
def privNameP (v : CrtImpl) : String := "vg_rsa_private_checked_precomputed" ++ v.suffix
def privCodeP (v : CrtImpl) : Prog isa := Impl.Rsa.Arm.PrivChecked.codeP v.crtPName v.crtP v.pdName v.pd
/-- Inner frame, register save, and the largest callee's stack: the private
CRT's frame of 56 and the 48 of a Montgomery call it makes. -/
def stackBytes : Nat := 3488
end VG.Proof.Rsa.Arm
