module

public import VerifiedGarbage.Impl.Dsa.X86_64.Fn
public import VerifiedGarbage.Proof.Dsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCode
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCorrect
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFillG
import VerifiedGarbage.Proof.Framework.Lit

/-!
# DSA's functions over its arithmetic on x86-64, without secret residue

Each function as emitted (`Impl.Dsa.X86_64.Fn`), over any implementation of
the arithmetic (`Backend`), with its whole stack wiped by its cleanup at the
implementation's level. Its code is its code over stubs of the squaring and
the multiplication, with the implementation's where it runs them (`FillG`,
`fill_gen`): the kernel evaluates what the cleanup needs of the stub once,
and the implementation what it needs of its own code where it is defined
(`Backend.sqSide`, `Backend.mulSide`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.Dsa.X86_64.BackendScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.Dsa.X86_64

/-- A stub of the squaring. -/
abbrev stubSq : Prog isa := .call "sq" (.block [])

/-- A stub of the multiplication. -/
abbrev stubMul : Nat → Nat → Nat → Prog isa := fun _ _ _ => .call "mm" (.block [])

/-- The stack the squaring and the multiplication (called) need. -/
def stubStack : String → Nat := fun _ => 8

theorem randomSign_stub : stubSideG (Impl.Dsa.X86_64.RandomSign.code "s" (Impl.Dsa.X86_64.PrevalidatedSign.sign stubSq stubMul)) VecLevel.sse.level stubStack 264 [] = true := by lit_decide

/-- `Spec.Dsa.randomSignPrevalidatedApi`'s function as emitted over `v` meets its contract in constant
time and returns without secret residue. -/
theorem randomSign_scrubbed (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.X86_64.Fn.randomSignPrevalidated v.level (prevalidatedSignerName v) v.sq v.mul)
      (Spec.Dsa.randomSignPrevalidatedApi.contract X86_64.abi 264) 32 := by
  have h := random_sign_prevalidated_verified v
  rw [v.stack_eq] at h
  exact verifiedScrubbedAllFillG (api := Spec.Dsa.randomSignPrevalidatedApi)
    { code := Impl.Dsa.X86_64.RandomSign.code (prevalidatedSignerName v) (Impl.Dsa.X86_64.PrevalidatedSign.sign v.sq v.mul)
      verified := h
      spSafe := random_sign_sp v.prevalidatedSigner } _ (Proof.Dsa.X86_64.Scrub.randomSignPrevalidatedOut _)
    (by have := v.sqSide; have := v.mulSide; fill_gen) (Nat.zero_le _) (Nat.le_refl _) (ha := randomSign_stub)

theorem randomSign_spSafe (v : Backend) :
    (Impl.Dsa.X86_64.Fn.randomSignPrevalidated v.level (prevalidatedSignerName v) v.sq v.mul).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (random_sign_sp v.prevalidatedSigner)

theorem validatePrivate_stub : stubSideG (Impl.Dsa.X86_64.PrevalidatedSign.validate stubSq stubMul) VecLevel.sse.level stubStack 8 [] = true := by lit_decide

/-- `Spec.Dsa.validatePrivateKeyApi`'s function as emitted over `v` meets its contract in constant
time and returns without secret residue. -/
theorem validatePrivate_scrubbed (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.X86_64.Fn.validatePrivateKey v.level v.sq v.mul)
      (Spec.Dsa.validatePrivateKeyApi.contract X86_64.abi 8) 32 := by
  have h := v.validatePrivateVerified
  rw [v.stack_eq] at h
  exact verifiedScrubbedAllFillG (api := Spec.Dsa.validatePrivateKeyApi)
    { code := Impl.Dsa.X86_64.PrevalidatedSign.validate v.sq v.mul
      verified := h
      spSafe := v.validatePrivateSp } _ (Proof.Dsa.X86_64.Scrub.validatePrivateKeyOut _)
    (by have := v.sqSide; have := v.mulSide; fill_gen) (Nat.zero_le _) (Nat.le_refl _) (ha := validatePrivate_stub)

theorem validatePrivate_spSafe (v : Backend) :
    (Impl.Dsa.X86_64.Fn.validatePrivateKey v.level v.sq v.mul).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (v.validatePrivateSp)

theorem validatePublic_stub : stubSideG (Impl.Dsa.X86_64.Prevalidated.validate stubSq stubMul) VecLevel.sse.level stubStack 8 [] = true := by lit_decide

/-- `Spec.Dsa.validatePublicKeyApi`'s function as emitted over `v` meets its contract in constant
time and returns without secret residue. -/
theorem validatePublic_scrubbed (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.X86_64.Fn.validatePublicKey v.level v.sq v.mul)
      (Spec.Dsa.validatePublicKeyApi.contract X86_64.abi 8) 32 := by
  have h := v.validateVerified
  rw [v.stack_eq] at h
  exact verifiedScrubbedAllFillG (api := Spec.Dsa.validatePublicKeyApi)
    { code := Impl.Dsa.X86_64.Prevalidated.validate v.sq v.mul
      verified := h
      spSafe := v.validateSp } _ (Proof.Dsa.X86_64.Scrub.validatePublicKeyOut _)
    (by have := v.sqSide; have := v.mulSide; fill_gen) (Nat.zero_le _) (Nat.le_refl _) (ha := validatePublic_stub)

theorem validatePublic_spSafe (v : Backend) :
    (Impl.Dsa.X86_64.Fn.validatePublicKey v.level v.sq v.mul).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (v.validateSp)

theorem verify_stub : stubSideG (Impl.Dsa.X86_64.Prevalidated.verify stubSq stubMul) VecLevel.sse.level stubStack 8 [] = true := by lit_decide

/-- `Spec.Dsa.verifyPrevalidatedApi`'s function as emitted over `v` meets its contract in constant
time and returns without secret residue. -/
theorem verify_scrubbed (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.X86_64.Fn.verifyPrevalidated v.level v.sq v.mul)
      (Spec.Dsa.verifyPrevalidatedApi.contract X86_64.abi 8) 32 := by
  have h := v.prevalidatedVerified
  rw [v.stack_eq] at h
  exact verifiedScrubbedAllFillG (api := Spec.Dsa.verifyPrevalidatedApi)
    { code := Impl.Dsa.X86_64.Prevalidated.verify v.sq v.mul
      verified := h
      spSafe := v.prevalidatedSp } _ (Proof.Dsa.X86_64.Scrub.verifyPrevalidatedOut _)
    (by have := v.sqSide; have := v.mulSide; fill_gen) (Nat.zero_le _) (Nat.le_refl _) (ha := verify_stub)

theorem verify_spSafe (v : Backend) :
    (Impl.Dsa.X86_64.Fn.verifyPrevalidated v.level v.sq v.mul).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (v.prevalidatedSp)

theorem generateKey_stub : stubSideG (Impl.Dsa.X86_64.GenerateKey.code "c" "d" (Impl.Dsa.X86_64.Generate.checkParameters stubSq stubMul) (Impl.Dsa.X86_64.Generate.deriveChecked stubSq stubMul)) VecLevel.sse.level stubStack 264 [] = true := by lit_decide

/-- `Spec.Dsa.generateKeyApi`'s function as emitted over `v` meets its contract in constant
time and returns without secret residue. -/
theorem generateKey_scrubbed (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.X86_64.Fn.generateKey v.level (keygenCheckName v) (keygenDeriveName v) v.sq v.mul)
      (Spec.Dsa.generateKeyApi.contract X86_64.abi 264) 32 := by
  have h := keygen_verified v
  rw [v.stack_eq] at h
  exact verifiedScrubbedAllFillG (api := Spec.Dsa.generateKeyApi)
    { code := Impl.Dsa.X86_64.GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Impl.Dsa.X86_64.Generate.checkParameters v.sq v.mul) (Impl.Dsa.X86_64.Generate.deriveChecked v.sq v.mul)
      verified := h
      spSafe := keygen_sp v } _ (Proof.Dsa.X86_64.Scrub.generateKeyOut _)
    (by have := v.sqSide; have := v.mulSide; fill_gen) (Nat.zero_le _) (Nat.le_refl _) (ha := generateKey_stub)

theorem generateKey_spSafe (v : Backend) :
    (Impl.Dsa.X86_64.Fn.generateKey v.level (keygenCheckName v) (keygenDeriveName v) v.sq v.mul).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (keygen_sp v)

theorem deriveKey_stub : stubSideG (Impl.Dsa.X86_64.Generate.deriveKey stubSq stubMul) VecLevel.sse.level stubStack 8 [] = true := by lit_decide

/-- `Spec.Dsa.deriveKeyApi`'s function as emitted over `v` meets its contract in constant
time and returns without secret residue. -/
theorem deriveKey_scrubbed (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.X86_64.Fn.deriveKey v.level v.sq v.mul)
      (Spec.Dsa.deriveKeyApi.contract X86_64.abi 8) 32 := by
  have h := v.deriveVerified
  rw [v.stack_eq] at h
  exact verifiedScrubbedAllFillG (api := Spec.Dsa.deriveKeyApi)
    { code := Impl.Dsa.X86_64.Generate.deriveKey v.sq v.mul
      verified := h
      spSafe := v.deriveSp } _ (Proof.Dsa.X86_64.Scrub.deriveKeyOut _)
    (by have := v.sqSide; have := v.mulSide; fill_gen) (Nat.zero_le _) (Nat.le_refl _) (ha := deriveKey_stub)

theorem deriveKey_spSafe (v : Backend) :
    (Impl.Dsa.X86_64.Fn.deriveKey v.level v.sq v.mul).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (v.deriveSp)

end VG.Proof.Dsa.X86_64.BackendScrub
