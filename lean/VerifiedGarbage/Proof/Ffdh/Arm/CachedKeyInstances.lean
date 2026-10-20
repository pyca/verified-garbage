module

public import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyPrograms
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyLaws
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyStack
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateVerified

/-! Cached attempts inherit every callable RSA Montgomery backend and caller transform. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedKeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm

def native (b : MontBackend) : Prog isa := b.caller.code (code b)

theorem native_verified (b : MontBackend) : Verified target (native b)
    (Spec.Ffdh.cachedGenerateKeyContract abi 176) :=
  b.caller.verified (cachedKeyGenerate_verified prepare sample (tail b) prepareLaw sampleLaw (tailLaw b))

theorem native_stack (b : MontBackend) : FrameStack.armStack (native b)≤176 :=
  Nat.le_trans (b.caller.stack_le _) (stack_ok b)

def backend (b : MontBackend) : KeyBackend .cached where
  generateKey := native b
  generateKey_verified := native_verified b
  keyStack := native_stack b
  suffix := b.suffix
  features := b.features

end VG.Proof.Ffdh.Arm.CachedKeyGenerate
