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
public import VerifiedGarbage.Proof.Variants.DsaArithmetic.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub

/-!
# DSA on AArch64, without secret residue

The postconditions of `vg_dsa_validate_public_key` and
`vg_dsa_validate_private_key` do not read the memory on return, and that of
`vg_dsa_parameter_search` reads it only within its outputs
(`Ffdh.AArch64.Scrub.bytesAt_of`, `wordsAt_of`; `ScrubAll.ScrubAllOk`, as
x86-64's `Proof/Dsa/X86_64/Scrub.lean` proves them): each implementation
returns with every register it may leave secret cleared, and its whole stack
zeroed, if it has one (`ScrubAll.scrubAllOf`, with the registers `clear`;
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


/-! ## What `scrubAllOf` needs of the code

`ScrubAll.scrubSide` of each function with each arithmetic backend: evaluated
here, by the kernel, so that the emitter works out nothing. -/

/-- The registers the tails clear: those the code, with each backend, may write. -/
def clear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v31], []⟩

/-- Of signing with a random nonce. -/
theorem randomSignPrevalidatedSide (v : Proof.Dsa.AArch64.Backend) (hv : v ∈ Proof.Variants.DsaArithmetic.AArch64.variants) :
    scrubSide (Impl.Dsa.AArch64.RandomSign.code (Proof.Dsa.AArch64.prevalidatedSignerName v)
        (Impl.Dsa.AArch64.PrevalidatedSign.sign v.mul))
      (v.stack + 256) (Spec.Dsa.randomSignSig.retBits abi.ptrBits) clear [] = true := by
  have e : (Proof.Variants.DsaArithmetic.AArch64.variants.all fun v => 
      scrubSide (Impl.Dsa.AArch64.RandomSign.code (Proof.Dsa.AArch64.prevalidatedSignerName v)
        (Impl.Dsa.AArch64.PrevalidatedSign.sign v.mul))
      (v.stack + 256) (Spec.Dsa.randomSignSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- Of validating a private key. -/
theorem validatePrivateKeySide (v : Proof.Dsa.AArch64.Backend) (hv : v ∈ Proof.Variants.DsaArithmetic.AArch64.variants) :
    scrubSide (Impl.Dsa.AArch64.PrevalidatedSign.validate v.mul)
      (v.stack) (Spec.Dsa.validatePrivateKeySig.retBits abi.ptrBits) clear [] = true := by
  have e : (Proof.Variants.DsaArithmetic.AArch64.variants.all fun v => 
      scrubSide (Impl.Dsa.AArch64.PrevalidatedSign.validate v.mul)
      (v.stack) (Spec.Dsa.validatePrivateKeySig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- Of validating a public key. -/
theorem validatePublicKeySide (v : Proof.Dsa.AArch64.Backend) (hv : v ∈ Proof.Variants.DsaArithmetic.AArch64.variants) :
    scrubSide (Impl.Dsa.AArch64.Prevalidated.validate v.mul)
      (v.stack) (Spec.Dsa.validatePublicKeySig.retBits abi.ptrBits) clear [] = true := by
  have e : (Proof.Variants.DsaArithmetic.AArch64.variants.all fun v => 
      scrubSide (Impl.Dsa.AArch64.Prevalidated.validate v.mul)
      (v.stack) (Spec.Dsa.validatePublicKeySig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- Of verification. -/
theorem verifyPrevalidatedSide (v : Proof.Dsa.AArch64.Backend) (hv : v ∈ Proof.Variants.DsaArithmetic.AArch64.variants) :
    scrubSide (Impl.Dsa.AArch64.Prevalidated.verify v.mul)
      (v.stack) (Spec.Dsa.verifySig.retBits abi.ptrBits) clear [] = true := by
  have e : (Proof.Variants.DsaArithmetic.AArch64.variants.all fun v => 
      scrubSide (Impl.Dsa.AArch64.Prevalidated.verify v.mul)
      (v.stack) (Spec.Dsa.verifySig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- Of key generation. -/
theorem generateKeySide (v : Proof.Dsa.AArch64.Backend) (hv : v ∈ Proof.Variants.DsaArithmetic.AArch64.variants) :
    scrubSide (Impl.Dsa.AArch64.GenerateKey.code (Proof.Dsa.AArch64.keygenCheckName v) (Proof.Dsa.AArch64.keygenDeriveName v)
        (Impl.Dsa.AArch64.Generate.checkParameters v.mul) (Impl.Dsa.AArch64.Generate.deriveChecked v.mul))
      (v.stack + 256) (Spec.Dsa.generateKeySig.retBits abi.ptrBits) clear [] = true := by
  have e : (Proof.Variants.DsaArithmetic.AArch64.variants.all fun v => 
      scrubSide (Impl.Dsa.AArch64.GenerateKey.code (Proof.Dsa.AArch64.keygenCheckName v) (Proof.Dsa.AArch64.keygenDeriveName v)
        (Impl.Dsa.AArch64.Generate.checkParameters v.mul) (Impl.Dsa.AArch64.Generate.deriveChecked v.mul))
      (v.stack + 256) (Spec.Dsa.generateKeySig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- Of deriving a key. -/
theorem deriveKeySide (v : Proof.Dsa.AArch64.Backend) (hv : v ∈ Proof.Variants.DsaArithmetic.AArch64.variants) :
    scrubSide (Impl.Dsa.AArch64.Generate.deriveKey v.mul)
      (v.stack) (Spec.Dsa.deriveKeySig.retBits abi.ptrBits) clear [] = true := by
  have e : (Proof.Variants.DsaArithmetic.AArch64.variants.all fun v => 
      scrubSide (Impl.Dsa.AArch64.Generate.deriveKey v.mul)
      (v.stack) (Spec.Dsa.deriveKeySig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

end VG.Proof.Dsa.AArch64.Scrub
