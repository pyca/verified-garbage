module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubOut
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubCode
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.RndVerified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-PKCS1-v1_5 on ARMv7, as emitted

`Impl.RsaPkcs1Enc.Arm.Fn` has each function with its cleanup; `Fn` below
has the theorem of each, for any implementation of the private CRT's
interface: it meets its contract in constant time and returns without
secret residue (`VerifiedScrubbed`), which is what its registration binds
(`Arm.Scrub.verifiedScrubbedAll`).

The frames of `vg_rsa_pkcs1_encrypt_random` use 2360 bytes, which is not a
frame size of the model (`FrameOk`), so its contract reserves the next one,
2368 (`Arm.Scrub.Verified.stack_le`, with the witness of its precondition
again). What the cleanup needs of the code (`CodeOk`: its frames within
those bytes, no indirect call) is proven once for any implementation, from
what each states of its own code (`Proof/Rsa/Arm/ScrubCode.lean`), with the
code around the call by `lit_decide`; `decRest_ok`, decryption's code but
for its call, is for `Front.lean`. Its postcondition reads the memory on
return only within `out` and `tape`, as on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Scrub

open VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm.Scrub
open VG.Proof.Rsa.Arm (CrtImpl privCodeP)

/-! ## Postconditions -/

theorem writtenRandom_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.RsaPkcs1Enc.writtenRandom m₁ o n r v) :
    Spec.RsaPkcs1Enc.writtenRandom m₂ o n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenRandom, e] using h

theorem encryptRandomOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Enc.encryptRandomContract abi stack) (Spec.RsaPkcs1Enc.encryptRandomSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [out, outLen, tape, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Enc.encryptRandomSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e' := bytesAt_of hb.1 (hp.2.1 ▸ toNat_sw_le abi ScrubAbi.plain outLen)
      rw [wordsAt_of hb.2.1]
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      revert h2
      generalize (Spec.RsaPkcs1Enc.padSearch _ _).outcome = o
      match o with
      | .accepted _ => exact fun h2 hP => writtenRandom_of e' (h2 hP)
      | .entropy .. => simp only [e']; exact id
      | .exhausted => simp only [e']; exact id

/-! ## The stacks, at frame sizes of the model -/

theorem randomSat : ∃ s, (Spec.RsaPkcs1Enc.encryptRandomContract abi 2368).pre s := by
  open Proof.RsaPkcs1Enc.Arm.Rnd in
  sig_implies_sat [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi,
    argRegs, reduceClassify, Loc.val, State.addr]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.RsaPkcs1Enc.padEntropy] using satState

theorem randomVerified (encName : String) (c : Proof.RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Impl.RsaPkcs1Enc.Arm.Random.code encName (Impl.RsaPkcs1Enc.Arm.Precomputed.code c.name c.code))
      (Spec.RsaPkcs1Enc.encryptRandomContract abi 2368) :=
  Verified.stack_le (by decide) (Proof.RsaPkcs1Enc.Arm.Rnd.code_verified encName c) randomSat

/-! ## What the cleanup needs of the code -/

theorem decRest_ok : CodeOk (.seq (.block Impl.RsaPkcs1Enc.Arm.Decrypt.dZero) (.seq Impl.Bignum.Arm.maskBytes
    (.seq (.block Impl.RsaPkcs1Enc.Arm.Decrypt.dCopy) (.seq Impl.Bignum.Arm.copyBytes
    (.seq (Impl.RsaPkcs1Enc.Arm.Decrypt.hashD Proof.RsaPkcs1Enc.Arm.decFns)
    (.seq (Impl.RsaPkcs1Enc.Arm.Decrypt.kdkMac Proof.RsaPkcs1Enc.Arm.decFns)
    (.seq (Impl.RsaPkcs1Enc.Arm.Decrypt.clLoop Proof.RsaPkcs1Enc.Arm.decFns)
    (.seq (Impl.RsaPkcs1Enc.Arm.Decrypt.amLoop Proof.RsaPkcs1Enc.Arm.decFns)
    (.seq Impl.RsaPkcs1Enc.Arm.Decrypt.alPart Impl.RsaPkcs1Enc.Arm.Decrypt.selPart)))))))) : Prog isa) 3488 := by
  lit_decide

/-- `vg_rsa_pkcs1_encrypt_precomputed`'s code, over the public operation `pd`. -/
theorem precomputed_ok {pdName : String} {pd : Prog isa} (h : CodeOk pd 104) :
    CodeOk (Impl.RsaPkcs1Enc.Arm.Precomputed.code pdName pd) 1216 := by
  refine wrap_codeOk (n := 104) (F := 1056) (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq ?_
    (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq (CodeOk.call h) ?_))))))))
  all_goals lit_decide

/-- Encryption from a random tape's code, over the call `enc`. -/
theorem random_ok {encName : String} {enc : Prog isa} (h : CodeOk enc 1216) :
    CodeOk (Impl.RsaPkcs1Enc.Arm.Random.code encName enc) 2368 := by
  refine (wrap_codeOk (n := 1216) (F := 1088) (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.ite
    (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq (CodeOk.call h) ?_)))) ?_))))).mono (by decide)
  all_goals lit_decide

theorem frameOk_2320 : FrameOk 2368 := by decide

end VG.Proof.RsaPkcs1Enc.Arm.Scrub

namespace VG.Proof.RsaPkcs1Enc.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm VG.Proof.RsaPkcs1Enc.Arm.Scrub

/-- `vg_rsa_pkcs1_encrypt_random`, calling `vg_rsa_pkcs1_encrypt_precomputed`
over `v`'s public operation, by the name `encName`. -/
theorem encryptRandom (encName : String) (v : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Enc.Arm.Fn.encryptRandom encName
        (Impl.RsaPkcs1Enc.Arm.Precomputed.code (pdOfCrt v).name (pdOfCrt v).code))
      (Spec.RsaPkcs1Enc.encryptRandomContract abi 2368) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPkcs1Enc.encryptRandomApi)
    { code := Impl.RsaPkcs1Enc.Arm.Random.code encName
        (Impl.RsaPkcs1Enc.Arm.Precomputed.code (pdOfCrt v).name (pdOfCrt v).code)
      verified := randomVerified encName (pdOfCrt v) }
    (encryptRandomOut _) (scrubSideF_of (random_ok (precomputed_ok v.pdOk)) frameOk_2320 _)

end VG.Proof.RsaPkcs1Enc.Arm.Fn
