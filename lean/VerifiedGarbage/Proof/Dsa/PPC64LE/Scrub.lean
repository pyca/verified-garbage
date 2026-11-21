module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Init
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Instances
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit

/-!
# DSA on PPC64LE, without secret residue

`vg_dsa_derive_key`, `vg_dsa_generate_key`, `vg_dsa_sign_random_prevalidated`,
`vg_dsa_validate_public_key`, `vg_dsa_validate_private_key`,
`vg_dsa_verify_prevalidated` and `vg_dsa_parameter_search`, each followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbedAll`), which clears the
volatile registers and the stack their frames used, which they do not wipe
themselves. Their postconditions read the memory on return only within
their outputs, as x86-64's (`Proof/Dsa/X86_64/Scrub.lean`): the validations
and verification not at all, the others the octets at `out` and the words at
`used` (and the parameter search's counter).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

/-- The byte `k` of a region of more than `k` bytes at `o`. -/
theorem contains_of {o : Addr} {k N : Nat} (hk : k < N) : Region.Contains ⟨o, N⟩ (o + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [BitVec.add_comm o, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  have := Nat.mod_le k (2 ^ 64)
  omega_using [hk]

/-- The `n` octets at `o` read the memory only within `⟨o, n * 1⟩`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨o, n * 1⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (contains_of (by omega_using [this]))).symm

/-- The `n` words at `o` read the memory only within `⟨o, N⟩`, `n * 8 ≤ N`. -/
theorem wordsAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n * 8 ≤ N := by omega) :
    Spec.Rsa.wordsAt m₂ o n = Spec.Rsa.wordsAt m₁ o n :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (contains_of (by simp only [Nat.reduceDiv] at ht; omega_using [hN, ht, this]))).symm

theorem toNat_sw (cs : List (String × List (BitVec 64))) (x : BitVec 64) :
    (x.setWidth (abi.withConsts cs).ptrBits).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, (ScrubAbi.consts cs).ptrBits]
  exact Nat.mod_eq_of_lt x.isLt

theorem validatePublicKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.validatePublicKeyContract abi stack) (Spec.Dsa.validatePublicKeySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem validatePrivateKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.validatePrivateKeyContract abi stack) (Spec.Dsa.validatePrivateKeySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem verifyPrevalidatedOut (stack : Nat) :
    PostOut (Spec.Dsa.verifyPrevalidatedContract abi stack) (Spec.Dsa.verifySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem randomSignPrevalidatedOut (stack : Nat) :
    PostOut (Spec.Dsa.randomSignPrevalidatedContract abi stack) (Spec.Dsa.randomSignSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.randomSignSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1]
      · exact h
      · exact toNat_sw [] outLen

theorem generateKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.generateKeyContract abi stack) (Spec.Dsa.generateKeySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.generateKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1]
      · exact h
      · exact toNat_sw [] outLen

theorem deriveKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.deriveKeyContract abi stack) (Spec.Dsa.deriveKeySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.deriveKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX]
      · exact h
      · exact toNat_sw [] outLen

theorem parameterSearchOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.Dsa.parameterSearchContract (abi.withConsts cs) stack)
      (Spec.Dsa.parameterSearchSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [out, outLen, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.parameterSearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2]
      · exact h
      · exact toNat_sw cs outLen

/-! ## The functions as emitted -/

/-- `vg_dsa_derive_key` as emitted (`Impl.Dsa.PPC64LE.Fn.deriveKey`) meets its
contract in constant time and returns without secret residue. -/
theorem deriveKey_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Dsa.PPC64LE.Fn.deriveKey
      (Spec.Dsa.deriveKeyContract PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.deriveKeyApi) {
      code := Impl.Dsa.PPC64LE.Derive.derive
      verified := Proof.Dsa.PPC64LE.deriveKey_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (deriveKeyOut _)
    (by dsimp only; lit_decide)

/-- `vg_dsa_sign_random_prevalidated` as emitted
(`Impl.Dsa.PPC64LE.Fn.randomSignPrevalidated`) meets its contract in constant
time and returns without secret residue. -/
theorem randomSignPrevalidated_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Dsa.PPC64LE.Fn.randomSignPrevalidated
      (Spec.Dsa.randomSignPrevalidatedContract PPC64LE.abi Proof.Dsa.PPC64LE.rsStack) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.randomSignPrevalidatedApi) {
      code := Impl.Dsa.PPC64LE.RandomSign.code
      verified := Proof.Dsa.PPC64LE.randomSign_verified }
    304 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (randomSignPrevalidatedOut _)
    (by dsimp only; lit_decide)

/-- `vg_dsa_generate_key` as emitted (`Impl.Dsa.PPC64LE.Fn.generateKey`) meets its
contract in constant time and returns without secret residue. -/
theorem generateKey_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Dsa.PPC64LE.Fn.generateKey
      (Spec.Dsa.generateKeyContract PPC64LE.abi Proof.Dsa.PPC64LE.gkStack) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.generateKeyApi) {
      code := Impl.Dsa.PPC64LE.Generate.code
      verified := Proof.Dsa.PPC64LE.generate_verified }
    304 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (generateKeyOut _)
    (by dsimp only; lit_decide)

/-- `vg_dsa_validate_public_key` as emitted
(`Impl.Dsa.PPC64LE.Fn.validatePublicKey`) meets its contract in constant time
and returns without secret residue. -/
theorem validatePublicKey_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Dsa.PPC64LE.Fn.validatePublicKey
      (Spec.Dsa.validatePublicKeyContract PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.validatePublicKeyApi) {
      code := Impl.Dsa.PPC64LE.Prevalidated.validate
      verified := Proof.Dsa.PPC64LE.validate_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (validatePublicKeyOut _)
    (by dsimp only; lit_decide)

/-- `vg_dsa_validate_private_key` as emitted
(`Impl.Dsa.PPC64LE.Fn.validatePrivateKey`) meets its contract in constant time
and returns without secret residue. -/
theorem validatePrivateKey_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Dsa.PPC64LE.Fn.validatePrivateKey
      (Spec.Dsa.validatePrivateKeyContract PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.validatePrivateKeyApi) {
      code := Impl.Dsa.PPC64LE.PrevalidatedSign.validate
      verified := Proof.Dsa.PPC64LE.validatePrivate_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (validatePrivateKeyOut _)
    (by dsimp only; lit_decide)

/-- `vg_dsa_verify_prevalidated` as emitted
(`Impl.Dsa.PPC64LE.Fn.verifyPrevalidated`) meets its contract in constant time
and returns without secret residue. -/
theorem verifyPrevalidated_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Dsa.PPC64LE.Fn.verifyPrevalidated
      (Spec.Dsa.verifyPrevalidatedContract PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.verifyPrevalidatedApi) {
      code := Impl.Dsa.PPC64LE.Prevalidated.verify
      verified := Proof.Dsa.PPC64LE.prevalidated_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (verifyPrevalidatedOut _)
    (by dsimp only; lit_decide)

/-- What `verifiedScrubbedAll` needs of the parameter search with each Miller-Rabin
round: evaluated here. -/
theorem parameterSearchSide (v : Proof.MillerRabin.PPC64LE.RoundImpl)
    (hv : v ∈ Proof.Variants.MillerRabin.PPC64LE.variants) :
    scrubSide (Impl.Dsa.PPC64LE.Generation.code (Gen.gen1 v) (Gen.gen2 v) (Gen.gen3 v)) 176
      (Spec.Dsa.parameterSearchSig.retBits 64) Impl.Scrub.PPC64LE.Clear.all = true := by
  have h : (Proof.Variants.MillerRabin.PPC64LE.variants.all fun v =>
      scrubSide (Impl.Dsa.PPC64LE.Generation.code (Gen.gen1 v) (Gen.gen2 v) (Gen.gen3 v)) 176
        (Spec.Dsa.parameterSearchSig.retBits 64) Impl.Scrub.PPC64LE.Clear.all) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `vg_dsa_parameter_search` as emitted (`Impl.Dsa.PPC64LE.Fn.parameterSearch`),
with the Miller-Rabin round `v`, meets its contract in constant time and
returns without secret residue. -/
theorem parameterSearch_scrubbed (v : Proof.MillerRabin.PPC64LE.RoundImpl)
    (hv : v ∈ Proof.Variants.MillerRabin.PPC64LE.variants) :
    VerifiedScrubbed PPC64LE.target (Impl.Dsa.PPC64LE.Fn.parameterSearch v.suffix v.code)
      (Spec.Dsa.parameterSearchContract (PPC64LE.abi.withConsts Impl.RsaKeyGen.TrialTable32.consts) 176) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.parameterSearchApi) {
      code := Impl.Dsa.PPC64LE.Generation.code (Gen.gen1 v) (Gen.gen2 v) (Gen.gen3 v)
      verified := Gen.search_params v }
    176 Impl.Scrub.PPC64LE.Clear.all
    (parameterSearchOut Impl.RsaKeyGen.TrialTable32.consts 176)
    (parameterSearchSide v hv)

/-- `vg_dsa_parameter_init` needs no cleanup: it reads no memory, so what it leaves is a function of its
arguments. It meets its contract in constant time and returns without secret residue. -/
theorem parameterInit_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Dsa.PPC64LE.Generation.init
      (Spec.Dsa.parameterInitContract PPC64LE.abi) 32 :=
  ⟨Proof.Dsa.PPC64LE.Gen.init_verified, Proof.Dsa.PPC64LE.Gen.init_noResidue _ _⟩

end VG.Proof.Dsa.PPC64LE.Scrub
