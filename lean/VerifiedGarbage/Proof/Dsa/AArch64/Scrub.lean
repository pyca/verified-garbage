module

public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCorrect
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyVerified
import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub

/-!
# DSA on AArch64, without secret residue

The postconditions of `vg_dsa_validate_public_key` and
`vg_dsa_validate_private_key` do not read the memory on return, and that of
`vg_dsa_parameter_search` reads it only within its outputs
(`Ffdh.AArch64.Scrub.bytesAt_of`, `wordsAt_of`; `ScrubAll.ScrubAllOk`, as
x86-64's `Proof/Dsa/X86_64/Scrub.lean` proves them): each implementation
returns with every register it may leave secret cleared, and its whole stack
zeroed, if it has one (`Impl.Dsa.AArch64.Fn`, with the registers `Fn.clear`;
the parameter search, whose registers differ with its hash functions, by
`ScrubAll.withScrubAll` still).
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Proof.Ffdh.AArch64.Scrub

theorem validatePublicKeyOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.validatePublicKeyContract abi stack) stack
      (Spec.Dsa.validatePublicKeySig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := Spec.Dsa.validatePublicKeySig) (Nat.le_of_ble_eq_true rfl) fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem validatePrivateKeyOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.validatePrivateKeyContract abi stack) stack
      (Spec.Dsa.validatePrivateKeySig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := Spec.Dsa.validatePrivateKeySig) (Nat.le_of_ble_eq_true rfl) fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem parameterSearchOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.parameterSearchContract abi stack) stack
      (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := Spec.Dsa.parameterSearchSig) (Nat.le_of_ble_eq_true rfl) fun
    | [out, outLen, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.parameterSearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2]
      · exact h
      · exact toNat_sw outLen


/-! ## With arguments on the stack -/

theorem verifyPrevalidatedOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.verifyPrevalidatedContract abi stack) stack (Spec.Dsa.verifySig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Dsa.verifySig) fun
    | [_, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem deriveKeyOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.deriveKeyContract abi stack) stack (Spec.Dsa.deriveKeySig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Dsa.deriveKeySig) fun
    | [out, outLen, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.deriveKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.deriveKeySig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.deriveKeySig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX]
      · exact h
      · exact toNat_sw outLen

theorem generateKeyOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.generateKeyContract abi stack) stack (Spec.Dsa.generateKeySig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Dsa.generateKeySig) fun
    | [out, outLen, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.generateKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.generateKeySig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.generateKeySig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1]
      · exact h
      · exact toNat_sw outLen

theorem randomSignPrevalidatedOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.randomSignPrevalidatedContract abi stack) stack (Spec.Dsa.randomSignSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Dsa.randomSignSig) fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.randomSignSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.randomSignSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.randomSignSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1]
      · exact h
      · exact toNat_sw outLen


/-! ## The functions, as emitted

Each function with its cleanup (`Impl.Dsa.AArch64.Fn`), over an arithmetic
backend `v`: it meets its contract in constant time and returns without
secret residue (`VerifiedScrubbed`), which is what its registration binds.
What the cleanup needs of the code (`ScrubAll.scrubSide`) is the backend's
(`Backend.validateScrub` and the others), proved where it is defined. -/

open VG.Proof.Dsa.AArch64 (Backend prevalidatedSignerName keygenCheckName keygenDeriveName)

/-- `vg_dsa_random_sign_prevalidated`. -/
theorem randomSignPrevalidated (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.AArch64.Fn.randomSignPrevalidated (prevalidatedSignerName v) v.mul v.stack)
      (Spec.Dsa.randomSignPrevalidatedContract abi (v.stack + 256)) 32 :=
  verifiedScrubbed (api := Spec.Dsa.randomSignPrevalidatedApi)
    { code := Impl.Dsa.AArch64.RandomSign.code (prevalidatedSignerName v) (Impl.Dsa.AArch64.PrevalidatedSign.sign v.mul)
      verified := Proof.Dsa.AArch64.random_sign_prevalidated_verified v } _
    (randomSignPrevalidatedOk _) v.randomSignScrub

/-- `vg_dsa_validate_private_key`. -/
theorem validatePrivateKey (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.AArch64.Fn.validatePrivateKey v.mul v.stack)
      (Spec.Dsa.validatePrivateKeyContract abi v.stack) 32 :=
  verifiedScrubbed (api := Spec.Dsa.validatePrivateKeyApi)
    { code := Impl.Dsa.AArch64.PrevalidatedSign.validate v.mul, verified := v.validatePrivateVerified } _
    (validatePrivateKeyOk _) v.validatePrivateScrub

/-- `vg_dsa_validate_public_key`. -/
theorem validatePublicKey (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.AArch64.Fn.validatePublicKey v.mul v.stack)
      (Spec.Dsa.validatePublicKeyContract abi v.stack) 32 :=
  verifiedScrubbed (api := Spec.Dsa.validatePublicKeyApi)
    { code := Impl.Dsa.AArch64.Prevalidated.validate v.mul, verified := v.validateVerified } _
    (validatePublicKeyOk _) v.validateScrub

/-- `vg_dsa_verify_prevalidated`. -/
theorem verifyPrevalidated (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.AArch64.Fn.verifyPrevalidated v.mul v.stack)
      (Spec.Dsa.verifyPrevalidatedContract abi v.stack) 32 :=
  verifiedScrubbed (api := Spec.Dsa.verifyPrevalidatedApi)
    { code := Impl.Dsa.AArch64.Prevalidated.verify v.mul, verified := v.prevalidatedVerified } _
    (verifyPrevalidatedOk _) v.prevalidatedScrub

/-- `vg_dsa_generate_key`. -/
theorem generateKey (v : Backend) :
    VerifiedScrubbed target
      (Impl.Dsa.AArch64.Fn.generateKey (keygenCheckName v) (keygenDeriveName v) v.mul v.stack)
      (Spec.Dsa.generateKeyContract abi (v.stack + 256)) 32 :=
  verifiedScrubbed (api := Spec.Dsa.generateKeyApi)
    { code := Impl.Dsa.AArch64.GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
        (Impl.Dsa.AArch64.Generate.checkParameters v.mul) (Impl.Dsa.AArch64.Generate.deriveChecked v.mul)
      verified := Proof.Dsa.AArch64.keygen_verified v } _
    (generateKeyOk _) v.generateKeyScrub

/-- `vg_dsa_derive_key`. -/
theorem deriveKey (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.AArch64.Fn.deriveKey v.mul v.stack)
      (Spec.Dsa.deriveKeyContract abi v.stack) 32 :=
  verifiedScrubbed (api := Spec.Dsa.deriveKeyApi)
    { code := Impl.Dsa.AArch64.Generate.deriveKey v.mul, verified := v.deriveVerified } _
    (deriveKeyOk _) v.deriveScrub

end VG.Proof.Dsa.AArch64.Scrub
