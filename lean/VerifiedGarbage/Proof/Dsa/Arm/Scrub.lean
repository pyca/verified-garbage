module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Dsa.Arm.Fn
public import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Init
public import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Verified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Dsa.Arm.Fn
meta import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivateVerified
meta import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
meta import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified
meta import VerifiedGarbage.Proof.Dsa.Arm.Gen.Init
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Verified
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-!
# DSA's functions on ARMv7, as emitted

DSA's validations, its verification, its key derivation and the
initialization of its parameter search, with either multiplication
(`Dynamic.mul umaal`), have no frames: they keep the registers they save in
their scratch space, a buffer. Each is emitted with its cleanup
(`Impl.Dsa.Arm.Fn`, `Impl.Residue.Arm.scrub`): followed by instructions that
set the registers a callee may change, but the result, and the flags to
constants (`Arm.Scrub.verifiedScrubbed`). Signing and key generation, which
call the entropy function from a frame, also zero the 144 bytes of stack
their contracts reserve (`scrubF`, `Arm.Scrub.verifiedScrubbedF`): their
postconditions read the memory on return only at `out` and `used`
(`Arm.Scrub.PostOut`), and their code, with either multiplication, uses at
most those 144 bytes and makes no indirect call (`CodeOk`). `Fn` below has
the theorem of each, which its registration binds.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Scrub

open VG VG.Arm VG.Impl.Dsa.Arm

theorem validatePrivate_noFrames (umaal : Bool) : (PrevalidatedSign.validate umaal).noFrames = true := by
  cases umaal <;> lit_decide

theorem deriveKey_noFrames (umaal : Bool) : (Generate.deriveKey umaal).noFrames = true := by
  cases umaal <;> lit_decide

theorem validatePublic_noFrames (umaal : Bool) : (Prevalidated.validate umaal).noFrames = true := by
  cases umaal <;> lit_decide

theorem verify_noFrames (umaal : Bool) : (Prevalidated.verify umaal).noFrames = true := by
  cases umaal <;> lit_decide

theorem parameterInit_noFrames : Generation.init.noFrames = true := by lit_decide

/-! ## Signing and key generation

`vg_dsa_random_sign_prevalidated` and `vg_dsa_generate_key` call the entropy
function from a frame. Their postconditions read the memory on return only
at `out` and `used` (`Arm.Scrub.PostOut`). -/

open VG.Arm.Scrub VG.Arm.FrameStack

/-- The byte `k` of a region of more than `k` bytes at `o`. -/
theorem contains_of {o : Addr} {k N : Nat} (hk : k < N) : Region.Contains ⟨o, N⟩ (o + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [BitVec.add_comm o, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  have := Nat.mod_le k (2 ^ 64)
  omega_using [hk]

/-- The `n` octets at `o` read the memory only within `⟨o, N⟩`, `n ≤ N`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n ≤ N) :
    Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (contains_of (by omega_using [this, hN]))).symm

/-- A length, as a 32-bit argument, is at most the bytes of its buffer. -/
theorem toNat_sw_le (x : BitVec 64) : (x.setWidth abi.ptrBits).toNat ≤ x.toNat * 1 := by
  rw [BitVec.toNat_setWidth, Nat.mul_one]
  exact Nat.mod_le _ _

/-- The `n` words at `o` read the memory only within `⟨o, N⟩`, `n * 8 ≤ N`. -/
theorem wordsAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n * 8 ≤ N := by omega) :
    Spec.Rsa.wordsAt m₂ o n = Spec.Rsa.wordsAt m₁ o n :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (contains_of (by simp only [Nat.reduceDiv] at ht; omega_using [hN, ht, this]))).symm

theorem randomSignPrevalidatedOut (stack : Nat) :
    PostOut (Spec.Dsa.randomSignPrevalidatedContract abi stack) (Spec.Dsa.randomSignSig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.randomSignSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [bytesAt_of hb.1 (toNat_sw_le outLen), wordsAt_of hb.2.1]
      exact h

theorem generateKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.generateKeyContract abi stack) (Spec.Dsa.generateKeySig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.generateKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [bytesAt_of hb.1 (toNat_sw_le outLen), wordsAt_of hb.2.1]
      exact h

theorem frameOk_144 : FrameOk 144 := by decide

/-- Signing's code, with either multiplication, uses at most 144 bytes of
stack and makes no indirect call. -/
theorem randomSign_codeOk (umaal : Bool) :
    CodeOk (RandomSign.code (PrevalidatedSign.signerName umaal) (PrevalidatedSign.sign umaal)) 144 := by
  cases umaal
  · exact ⟨by lit_decide, by lit_decide⟩
  · exact ⟨by lit_decide, by lit_decide⟩

/-- Key generation's code, with either multiplication, uses at most 144 bytes
of stack and makes no indirect call. -/
theorem generateKey_codeOk (umaal : Bool) :
    CodeOk (GenerateKey.code (Generate.checkName umaal) (Generate.deriveName umaal)
      (Generate.checkParameters umaal) (Generate.deriveChecked umaal)) 144 := by
  cases umaal
  · exact ⟨by lit_decide, by lit_decide⟩
  · exact ⟨by lit_decide, by lit_decide⟩

end VG.Proof.Dsa.Arm.Scrub

namespace VG.Proof.Dsa.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Impl.Dsa.Arm

/-- `vg_dsa_validate_private_key`. -/
theorem validatePrivateKey (umaal : Bool) :
    VerifiedScrubbed target (Impl.Dsa.Arm.Fn.validatePrivateKey umaal)
      (Spec.Dsa.validatePrivateKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.Dsa.validatePrivateKeyApi)
    { code := PrevalidatedSign.validate umaal, verified := validating_private_verified }
    (Scrub.validatePrivate_noFrames umaal)

/-- `vg_dsa_derive_key`. -/
theorem deriveKey (umaal : Bool) :
    VerifiedScrubbed target (Impl.Dsa.Arm.Fn.deriveKey umaal) (Spec.Dsa.deriveKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.Dsa.deriveKeyApi)
    { code := Generate.deriveKey umaal, verified := derive_verified } (Scrub.deriveKey_noFrames umaal)

/-- `vg_dsa_validate_public_key`. -/
theorem validatePublicKey (umaal : Bool) :
    VerifiedScrubbed target (Impl.Dsa.Arm.Fn.validatePublicKey umaal)
      (Spec.Dsa.validatePublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.Dsa.validatePublicKeyApi)
    { code := Prevalidated.validate umaal, verified := validate_verified } (Scrub.validatePublic_noFrames umaal)

/-- `vg_dsa_verify_prevalidated`. -/
theorem verifyPrevalidated (umaal : Bool) :
    VerifiedScrubbed target (Impl.Dsa.Arm.Fn.verifyPrevalidated umaal)
      (Spec.Dsa.verifyPrevalidatedContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.Dsa.verifyPrevalidatedApi)
    { code := Prevalidated.verify umaal, verified := prevalidated_verified } (Scrub.verify_noFrames umaal)

/-- `vg_dsa_parameter_init`. -/
theorem parameterInit :
    VerifiedScrubbed target Impl.Dsa.Arm.Fn.parameterInit (Spec.Dsa.parameterInitContract abi) 32 :=
  verifiedScrubbed (api := Spec.Dsa.parameterInitApi)
    { code := Generation.init, verified := Gen.Init.init_verified } Scrub.parameterInit_noFrames

/-- `vg_dsa_random_sign_prevalidated`. -/
theorem randomSignPrevalidated (umaal : Bool) :
    VerifiedScrubbed target (Impl.Dsa.Arm.Fn.randomSignPrevalidated umaal)
      (Spec.Dsa.randomSignPrevalidatedContract abi 144) 32 :=
  verifiedScrubbedF (api := Spec.Dsa.randomSignPrevalidatedApi)
    { code := RandomSign.code (PrevalidatedSign.signerName umaal) (PrevalidatedSign.sign umaal)
      verified := randomSigningPrevalidated_verified }
    (Scrub.randomSignPrevalidatedOut _) (scrubSideF_of (Scrub.randomSign_codeOk umaal) Scrub.frameOk_144 _)

/-- `vg_dsa_generate_key`. -/
theorem generateKey (umaal : Bool) :
    VerifiedScrubbed target (Impl.Dsa.Arm.Fn.generateKey umaal) (Spec.Dsa.generateKeyContract abi 144) 32 :=
  verifiedScrubbedF (api := Spec.Dsa.generateKeyApi)
    { code := GenerateKey.code (Generate.checkName umaal) (Generate.deriveName umaal)
        (Generate.checkParameters umaal) (Generate.deriveChecked umaal)
      verified := Key.generating_verified }
    (Scrub.generateKeyOut _) (scrubSideF_of (Scrub.generateKey_codeOk umaal) Scrub.frameOk_144 _)

end VG.Proof.Dsa.Arm.Fn
