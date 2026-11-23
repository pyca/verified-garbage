module

public import VerifiedGarbage.Impl.Dsa.X86_64.Fn
public import VerifiedGarbage.Proof.Dsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Dsa.X86_64.Slots
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCode
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCorrect

/-!
# DSA's complete entry points over its arithmetic on x86-64, without secret residue

Each complete entry point as emitted (`Impl.Dsa.X86_64.Fn`), over any
implementation of the arithmetic (`SlotBackend`), with its whole stack wiped by
its cleanup at the implementation's level. It calls functions that call the
arithmetic through slots (`Fn.signerS`, `Fn.checkS`, `Fn.deriveCheckedS`), so
its contract makes the arithmetic's addresses public (`Abi.withFns`), and the
cleanup is `Slots.scrubbedFns`'s, from what the kernel evaluates of its code
(`Slots.EntriesOk`).
-/

-- separate module: the cleanup of the complete entry points needs their proofs, which the variants, importers of `Slots`, do not

@[expose] public section

namespace VG.Proof.Dsa.X86_64.BackendScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.Dsa.X86_64 VG.Proof.Dsa.X86_64.Slots

/-- `Spec.Dsa.randomSignPrevalidatedApi`'s function as emitted over `A` meets its contract in constant
time and returns without secret residue. -/
theorem randomSign_scrubbed (A : SlotBackend) :
    VerifiedScrubbed target
      (Impl.Dsa.X86_64.Fn.randomSignPrevalidatedS A.backend.level (prevalidatedSignerName A.backend) A.nm A.ns A.bm A.bs)
      (Spec.Dsa.randomSignPrevalidatedApi.contract (X86_64.abi.withFns [A.nm, A.ns]) 328) 32 := by
  have h := random_sign_prevalidated_verified A.backend
  rw [A.backend.stack_eq] at h
  have e := A.ok.randomSign
  exact scrubbedFns A.backend.level 328 h (random_sign_sp A.backend.prevalidatedSigner) e.depth e.ins e.inames
    (by decide) rfl (Proof.Dsa.X86_64.Scrub.randomSignPrevalidatedOut 328)

theorem randomSign_spSafe (A : SlotBackend) :
    (Impl.Dsa.X86_64.Fn.randomSignPrevalidatedS A.backend.level (prevalidatedSignerName A.backend) A.nm A.ns A.bm
      A.bs).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (random_sign_sp A.backend.prevalidatedSigner)

/-- `Spec.Dsa.generateKeyApi`'s function as emitted over `A` meets its contract in constant
time and returns without secret residue. -/
theorem generateKey_scrubbed (A : SlotBackend) :
    VerifiedScrubbed target
      (Impl.Dsa.X86_64.Fn.generateKeyS A.backend.level (keygenCheckName A.backend) (keygenDeriveName A.backend) A.nm
        A.ns A.bm A.bs)
      (Spec.Dsa.generateKeyApi.contract (X86_64.abi.withFns [A.nm, A.ns]) 328) 32 := by
  have h := keygen_verified A.backend
  rw [A.backend.stack_eq] at h
  have e := A.ok.generateKey
  exact scrubbedFns A.backend.level 328 h (keygen_sp A.backend) e.depth e.ins e.inames (by decide) rfl
    (Proof.Dsa.X86_64.Scrub.generateKeyOut 328)

theorem generateKey_spSafe (A : SlotBackend) :
    (Impl.Dsa.X86_64.Fn.generateKeyS A.backend.level (keygenCheckName A.backend) (keygenDeriveName A.backend) A.nm
      A.ns A.bm A.bs).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (keygen_sp A.backend)

end VG.Proof.Dsa.X86_64.BackendScrub
