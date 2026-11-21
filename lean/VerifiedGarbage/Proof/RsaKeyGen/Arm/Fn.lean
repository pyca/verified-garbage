module

public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubOut
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubTab
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.KeyInit
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Generate.Verified
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSA key generation on ARMv7, as emitted

`Impl.RsaKeyGen.Arm.Fn` has each function with its cleanup; `Fn` below has
the theorem of each: it meets its contract in constant time and returns
without secret residue (`VerifiedScrubbed`), which is what its registration
binds.

`vg_rsa_generate_init` has no frame (`Arm.Scrub.verifiedScrubbed`,
`Code.noFrames` by `lit_decide`). `vg_rsa_generate` zeroes the 256 bytes of
stack its contract reserves (`Arm.Scrub.verifiedScrubbedAll`), for any
implementation of the Miller–Rabin round: what the cleanup needs of its code
(`CodeOk`) is proven once by `code_okT` (`Proof/Rsa/Arm/ScrubTab.lean`), for
code whose round is a variable, from what each round states of its own code
(`RoundImpl.stack`, `RoundImpl.icallFree`). Its postcondition reads the
memory on return only within `key`, `used` and `state`, as on PPC64LE
(`Proof/RsaKeyGen/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Scrub

open VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm.Scrub

/-! ## The postcondition -/

/-- The 8 octets at `state + 48` lie in the 56 bytes of `state`. -/
theorem bytesAt48_of {m₁ m₂ : Mem} {o : Addr}
    (h : ∀ a, Region.Contains ⟨o, 7 * 8⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.bytesAt m₂ (o + 48) 8 = Spec.Rsa.bytesAt m₁ (o + 48) 8 := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  have e : o + 48 + BitVec.ofNat 64 i = o + BitVec.ofNat 64 (48 + i) := Offset.add_add o 48 i
  rw [e]
  exact (h _ (contains_of (by omega))).symm

theorem keySearchOut (stack : Nat) :
    PostOut (Spec.RsaKeyGen.keySearchContract abi stack) (Spec.RsaKeyGen.keySearchSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [key, keyLen, used, _, _, _, _, state], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaKeyGen.keySearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      rw [bytesAt_of hb.1 (by rw [← hp.2.1]; exact toNat_sw_le abi ScrubAbi.plain keyLen), wordsAt_of hb.2.1,
        wordsAt_of hb.2.2.2.2, bytesAt48_of hb.2.2.2.2]
      exact h

/-! ## What the cleanup needs of the code -/

theorem generateInit_noFrames : Impl.RsaKeyGen.Arm.KeyInit.init.noFrames = true := by lit_decide

/-- Key generation's code, for any round, the code of each call by its name. -/
theorem generate_okT {N₁ N₂ N₃ : String} {R : Prog isa} (h : CodeOk R 56) :
    CodeOkT (Impl.RsaKeyGen.Arm.Generate.code
      (.call N₁ (Impl.RsaKeyGen.Arm.Search.code (.call N₂ (Impl.RsaKeyGen.Arm.Candidate.code N₃ R))))
      (.call "vg_rsa_keygen_key" Impl.RsaKeyGen.Arm.Key.code)) 256 [] := by
  code_okT

theorem frameOk_256 : FrameOk 256 := by decide

end VG.Proof.RsaKeyGen.Arm.Scrub

namespace VG.Proof.RsaKeyGen.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm.Scrub VG.Proof.RsaKeyGen.Arm.Scrub
open VG.Proof.MillerRabin.Arm (RoundImpl)

/-- `vg_rsa_generate_init`. -/
theorem generateInit :
    VerifiedScrubbed target Impl.RsaKeyGen.Arm.Fn.generateInit (Spec.RsaKeyGen.keyInitContract abi) 32 :=
  verifiedScrubbed (api := Spec.RsaKeyGen.keyInitApi)
    { code := Impl.RsaKeyGen.Arm.KeyInit.init, verified := Proof.RsaKeyGen.Arm.KeyInit.init_verified }
    generateInit_noFrames

/-- `vg_rsa_generate`, calling the prime search over the round `v`. -/
theorem generate [Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) :
    VerifiedScrubbed target
      (Impl.RsaKeyGen.Arm.Fn.generate (.call ("vg_rsa_prime_search" ++ v.suffix) (Proof.RsaKeyGen.Arm.Search.searchCode v))
        (.call "vg_rsa_keygen_key" Impl.RsaKeyGen.Arm.Key.code))
      (Spec.RsaKeyGen.keySearchContract abi 256) 32 :=
  verifiedScrubbedAll (api := Spec.RsaKeyGen.keySearchApi)
    { code := Proof.RsaKeyGen.Arm.Generate.genCode v, verified := Proof.RsaKeyGen.Arm.Generate.gen_verified v }
    (keySearchOut _) (scrubSideF_of (generate_okT ⟨v.stack, v.icallFree⟩).toOk frameOk_256 _)

end VG.Proof.RsaKeyGen.Arm.Fn
