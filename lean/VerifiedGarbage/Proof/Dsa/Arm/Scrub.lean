module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Dsa.Arm.Fn
public import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Init
public import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Verified
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Instances
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
meta import VerifiedGarbage.Proof.Dsa.Arm.Gen.Instances
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
(`Impl.Dsa.Arm.Fn`, `Impl.Scrub.Arm.scrub`): followed by instructions that
set the registers a callee may change, but the result, and the flags to
constants (`Arm.Scrub.verifiedScrubbed`). Signing and key generation, which
call the entropy function from a frame, also zero the 144 bytes of stack
their contracts reserve (`scrubAll`, `Arm.Scrub.verifiedScrubbedAll`): their
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

/-! ## The parameter search

`vg_dsa_parameter_search` keeps its working space in a frame of 304 bytes,
and its postcondition reads the memory on return only at `out`, `used` and
`state`. Its code calls the Miller–Rabin round of a variant
(`Proof/Variants/MillerRabin/Arm.lean`), which states its own stack and that
it makes no indirect call (`RoundImpl.stack`, `RoundImpl.icallFree`, by
`lit_decide` where it is defined). The search's own code is evaluated once
for each multiplication, with a stub in the round's place (`holeStub 56`, a
frame of the 56 bytes the round may use around nothing), and `Fill` carries
that to the code with any round: its frames use no more stack than the
stub's, and it makes no indirect call if the stub's code makes none. -/

theorem parameterSearchOut (stack : Nat) :
    PostOut (Spec.Dsa.parameterSearchContract abi stack) (Spec.Dsa.parameterSearchSig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, used, _, _, _, _, state], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.parameterSearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [bytesAt_of hb.1 (toNat_sw_le outLen), wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2]
      exact h

/-- A place for the round in the stub of the search: a frame of `k` bytes
around nothing, whose stack is `k`. -/
def holeStub (k : Nat) : Prog isa := .frame (.alloc k) (.block []) (.free k)

/-- `b` is `a` with some of its holes (`holeStub k`) replaced by code that
meets `CodeOk _ k`, and the names of its calls changed; any code matches
itself (`refl`). -/
inductive Fill : Prog isa → Prog isa → Prop
  | refl (a : Prog isa) : Fill a a
  | hole {k : Nat} {d : Prog isa} : CodeOk d k → Fill (holeStub k) d
  | seq {a b a' b' : Prog isa} : Fill a a' → Fill b b' → Fill (.seq a b) (.seq a' b')
  | ite {t e t' e' : Prog isa} (c : Cond) : Fill t t' → Fill e e' → Fill (.ite c t e) (.ite c t' e')
  | loop {b b' : Prog isa} (c : Cond) : Fill b b' → Fill (.loop b c) (.loop b' c)
  | call {b b' : Prog isa} (f g : String) : Fill b b' → Fill (.call f b) (.call g b')
  | frame {b b' : Prog isa} (i j : Instr) : Fill b b' → Fill (.frame i b j) (.frame i b' j)
  | icall {b x b' x' : Prog isa} (i : Instr) (f : String) :
      Fill b b' → Fill x x' → Fill (.icall i f b x) (.icall i f b' x')

theorem armStack_frame_le {i j : Instr} {b b' : Prog isa} (h : armStack b' ≤ armStack b) :
    armStack (.frame i b' j) ≤ armStack (.frame i b j) := by
  cases i <;> simp only [armStack] <;> omega

theorem Fill.armStack_le {a b : Prog isa} (h : Fill a b) : armStack b ≤ armStack a := by
  induction h with
  | refl => exact Nat.le_refl _
  | hole hd => simp only [holeStub, armStack, Nat.zero_add]; exact hd.1
  | seq _ _ iha ihb => simp only [armStack]; omega
  | ite _ _ _ iht ihe => simp only [armStack]; omega
  | loop _ _ ih => simp only [armStack]; exact ih
  | call _ _ _ ih => simp only [armStack]; exact ih
  | frame _ _ _ ih => exact armStack_frame_le ih
  | icall _ _ _ _ ihb ihx => simp only [armStack]; omega

theorem Fill.noIcall_of {a b : Prog isa} (h : Fill a b) (ha : noIcall a = true) : noIcall b = true := by
  induction h with
  | refl => exact ha
  | hole hd => exact hd.2
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    simp only [noIcall, Bool.and_eq_true] at ha ⊢; exact ⟨iha ha.1, ihb ha.2⟩
  | loop _ _ ih | call _ _ _ ih | frame _ _ _ ih => simp only [noIcall] at ha ⊢; exact ih ha
  | icall => simp only [noIcall, Bool.false_eq_true] at ha

/-- `CodeOk` of the code with implementations from that of the stub. -/
theorem Fill.codeOk {a b : Prog isa} {n : Nat} (h : Fill a b) (ha : CodeOk a n) : CodeOk b n :=
  ⟨Nat.le_trans h.armStack_le ha.1, h.noIcall_of ha.2⟩

/-- Proves `Fill a b` of the stub's code `a` and the code `b` with a round,
from a hypothesis `CodeOk c k` of the round's code `c`: code the two share
is matched as one term (`Fill.refl`, at reducible transparency, which
unfolds the geometries, `Impl.Dsa.Arm.Fn.geo`), and the rest is walked, its
blocks matched last; the number of hashes of `p` (`Geo.count`), which its
code recurses on, is evaluated first. -/
macro "fill_round" : tactic => `(tactic| repeat' (first
  | with_reducible exact Fill.refl _
  | exact Fill.hole (by assumption)
  | simp only [Impl.Dsa.Arm.Generation.Geo.count, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv]
  | refine Fill.seq ?_ ?_
  | refine Fill.ite _ ?_ ?_
  | refine Fill.loop _ ?_
  | refine Fill.call _ _ ?_
  | refine Fill.frame _ _ ?_
  | refine Fill.icall _ _ ?_ ?_
  | exact Fill.refl _))

theorem search_fill (umaal : Bool) (suffix : String) {round : Prog isa} (h : CodeOk round 56) :
    Fill (Impl.Dsa.Arm.Fn.search umaal "" (holeStub 56)) (Impl.Dsa.Arm.Fn.search umaal suffix round) := by
  fill_round

/-- The search's code with the stub, with either multiplication, uses at most
304 bytes of stack and makes no indirect call. -/
theorem search_stubOk (umaal : Bool) : CodeOk (Impl.Dsa.Arm.Fn.search umaal "" (holeStub 56)) 304 := by
  cases umaal
  · exact ⟨by lit_decide, by lit_decide⟩
  · exact ⟨by lit_decide, by lit_decide⟩

theorem frameOk_304 : FrameOk 304 := by decide

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
  verifiedScrubbedAll (api := Spec.Dsa.randomSignPrevalidatedApi)
    { code := RandomSign.code (PrevalidatedSign.signerName umaal) (PrevalidatedSign.sign umaal)
      verified := randomSigningPrevalidated_verified }
    (Scrub.randomSignPrevalidatedOut _) (scrubSideF_of (Scrub.randomSign_codeOk umaal) Scrub.frameOk_144 _)

/-- `vg_dsa_generate_key`. -/
theorem generateKey (umaal : Bool) :
    VerifiedScrubbed target (Impl.Dsa.Arm.Fn.generateKey umaal) (Spec.Dsa.generateKeyContract abi 144) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.generateKeyApi)
    { code := GenerateKey.code (Generate.checkName umaal) (Generate.deriveName umaal)
        (Generate.checkParameters umaal) (Generate.deriveChecked umaal)
      verified := Key.generating_verified }
    (Scrub.generateKeyOut _) (scrubSideF_of (Scrub.generateKey_codeOk umaal) Scrub.frameOk_144 _)

/-- `vg_dsa_parameter_search`, over the Miller–Rabin round `v`. -/
theorem parameterSearch (umaal : Bool) (v : Proof.MillerRabin.Arm.RoundImpl) :
    VerifiedScrubbed target (Impl.Dsa.Arm.Fn.parameterSearch umaal v.suffix v.code)
      (Spec.Dsa.parameterSearchContract abi 304) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.parameterSearchApi)
    { code := Impl.Dsa.Arm.Fn.search umaal v.suffix v.code, verified := Gen.search_params v }
    (Scrub.parameterSearchOut _)
    (scrubSideF_of ((Scrub.search_fill umaal v.suffix ⟨v.stack, v.icallFree⟩).codeOk (Scrub.search_stubOk umaal))
      Scrub.frameOk_304 _)

end VG.Proof.Dsa.Arm.Fn
