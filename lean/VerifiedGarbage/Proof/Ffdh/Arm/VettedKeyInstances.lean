module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleScalar
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.SamplePrograms
import VerifiedGarbage.Proof.Ffdh.Arm.VettedKeyGenerateVerified
import VerifiedGarbage.Proof.Ffdh.Arm.SampleInstance
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.VettedKeyGenerateTable
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGenerationContract

/-! Every callable Montgomery backend supplies the vetted attempt. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedKeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

def sample : Prog isa := VG.Impl.Ffdh.Arm.SampleScalar.code VettedBound.code

def code (b : MontBackend) : Prog isa := b.caller.code (SampleKeyGenerate.code b sample)

theorem verified (b : MontBackend) : Verified target (code b)
    (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176) :=
  b.caller.verified (vettedKeyGenerate_verified (KeyGenerate.prepare b) sample (SampleKeyGenerate.tail b)
    VettedGroups.environment (normalizedPrepareLaw b)
    (sampleLaw _ _ _ VettedBound.law) (SampleKeyGenerate.tailLaw b)
    vettedKeyGenerate_environment (fun _ _ h => h))

theorem stack_ok (b : MontBackend) : FrameStack.armStack (code b) ≤ 176 :=
  Nat.le_trans (b.caller.stack_le _) (SampleKeyGenerate.stack_ok b sample (by rfl))

def backend (b : MontBackend) : KeyBackend .vetted where
  generateKey := code b
  generateKey_verified := verified b
  keyStack := stack_ok b
  suffix := b.suffix
  features := b.features

end VG.Proof.Ffdh.Arm.VettedKeyGenerate
