module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Init
public import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivateVerified
meta import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
meta import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified
meta import VerifiedGarbage.Proof.Dsa.Arm.Gen.Init
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Verified
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-!
# DSA on ARMv7, without secret residue

DSA's validations, its verification, its key derivation and the
initialization of its parameter search, with either multiplication
(`Dynamic.mul umaal`), have no frames: they keep the
registers they save in their scratch space, a buffer. Each is registered
scrubbed (`Arm.Scrub.scrubReg`): followed by instructions that set the
registers a callee may change, but the result, and the flags to constants.
Signing and key generation, which have a frame, are registered with the
stack they use zeroed too (`Arm.Scrub.scrubRegF`, below).
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

def validatePrivateKeyReg (umaal : Bool) (suffix : String) : Registration Spec.Dsa.validatePrivateKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := suffix
      code := PrevalidatedSign.validate umaal
      verified := validating_private_verified }
    (validatePrivate_noFrames umaal)

def deriveKeyReg (umaal : Bool) (suffix : String) : Registration Spec.Dsa.deriveKeyApi target :=
  Arm.Scrub.scrubReg { suffix := suffix, code := Generate.deriveKey umaal, verified := derive_verified }
    (deriveKey_noFrames umaal)

def validatePublicKeyReg (umaal : Bool) (suffix : String) : Registration Spec.Dsa.validatePublicKeyApi target :=
  Arm.Scrub.scrubReg { suffix := suffix, code := Prevalidated.validate umaal, verified := validate_verified }
    (validatePublic_noFrames umaal)

def verifyPrevalidatedReg (umaal : Bool) (suffix : String) : Registration Spec.Dsa.verifyPrevalidatedApi target :=
  Arm.Scrub.scrubReg { suffix := suffix, code := Prevalidated.verify umaal, verified := prevalidated_verified }
    (verify_noFrames umaal)

def parameterInitReg : Registration Spec.Dsa.parameterInitApi target :=
  Arm.Scrub.scrubReg { code := Generation.init, verified := Gen.Init.init_verified } (by lit_decide)

/-! ## Signing and key generation

`vg_dsa_sign_random_prevalidated` and `vg_dsa_generate_key` call the entropy
function from a frame. Their postconditions read the memory on return only
at `out` and `used` (`Arm.Scrub.PostOut`), so each is registered followed by
a wipe of the stack its contract reserves (`Arm.Scrub.scrubRegF`). -/

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

theorem randomSign_noIcall (umaal : Bool) : noIcall (RandomSign.code (PrevalidatedSign.signerName umaal) (PrevalidatedSign.sign umaal)) = true := by
  cases umaal <;> lit_decide

theorem randomSign_armStack (umaal : Bool) :
    armStack (RandomSign.code (PrevalidatedSign.signerName umaal) (PrevalidatedSign.sign umaal)) ≤ 144 := by
  cases umaal <;> lit_decide

theorem generateKey_noIcall (umaal : Bool) : noIcall (GenerateKey.code (Generate.checkName umaal) (Generate.deriveName umaal)
      (Generate.checkParameters umaal) (Generate.deriveChecked umaal)) = true := by
  cases umaal <;> lit_decide

theorem generateKey_armStack (umaal : Bool) :
    armStack (GenerateKey.code (Generate.checkName umaal) (Generate.deriveName umaal)
      (Generate.checkParameters umaal) (Generate.deriveChecked umaal)) ≤ 144 := by
  cases umaal <;> lit_decide

def randomSignPrevalidatedReg (umaal : Bool) (suffix : String) :
    Registration Spec.Dsa.randomSignPrevalidatedApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := RandomSign.code (PrevalidatedSign.signerName umaal) (PrevalidatedSign.sign umaal)
      verified := randomSigningPrevalidated_verified }
    (randomSign_armStack umaal) (randomSign_noIcall umaal) frameOk_144 (randomSignPrevalidatedOut _) rfl

def generateKeyReg (umaal : Bool) (suffix : String) : Registration Spec.Dsa.generateKeyApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := GenerateKey.code (Generate.checkName umaal) (Generate.deriveName umaal)
        (Generate.checkParameters umaal) (Generate.deriveChecked umaal)
      verified := Key.generating_verified }
    (generateKey_armStack umaal) (generateKey_noIcall umaal) frameOk_144 (generateKeyOut _) rfl

end VG.Proof.Dsa.Arm.Scrub
