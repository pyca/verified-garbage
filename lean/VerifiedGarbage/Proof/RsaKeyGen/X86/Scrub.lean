module

public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInit
public import VerifiedGarbage.Proof.RsaKeyGen.X86.GenScrub
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Verified
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Fn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInit
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.GenScrub
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Verified
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# RSA key generation on x86 (32-bit), without secret residue

`vg_rsa_generate_init`, which calls nothing and has no frame, is emitted
with the tail that clears the registers (`Impl.RsaKeyGen.X86.Fn.generateInit`),
and returns without secret residue (`generateInit_scrubbed`).

`vg_rsa_generate`, generic over the implementation of the Miller–Rabin
round, is emitted with its cleanup (`Impl.RsaKeyGen.X86.Fn.generate`), which
returns without secret residue whatever the implementation
(`generate_scrubbed`), from what its cleanup needs of its code
(`GenScrub.gen_scrub`). Its postcondition reads the memory on return only
within the key's buffer, `used` and the state (`keySearchOut`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Rsa.X86.Scrub

/-- `vg_rsa_generate_init`, with its cleanup, returns without secret residue. -/
theorem generateInit_scrubbed :
    VerifiedScrubbed target Impl.RsaKeyGen.X86.Fn.generateInit (Spec.RsaKeyGen.keyInitContract abi) 32 :=
  verifiedScrubbed (api := Spec.RsaKeyGen.keyInitApi) {
    code := Impl.RsaKeyGen.X86.KeyInit.init
    verified := Proof.RsaKeyGen.X86.KeyInit.init_verified }

/-! ## `vg_rsa_generate` -/

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

theorem keySearchOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.RsaKeyGen.keySearchContract (abi.withConsts cs) stack)
      (Spec.RsaKeyGen.keySearchSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.consts cs) fun
    | [key, keyLen, used, _, _, _, _, state], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaKeyGen.keySearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have hk := toNat_sw_le _ (ScrubAbi.consts cs) keyLen
      rw [hp.2.1] at hk
      rw [bytesAt_of hb.1 hk, wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2, bytesAt48_of hb.2.2.2.2]
      exact h

open VG.Proof.MillerRabin.X86 (RoundImpl)
open VG.Proof.RsaKeyGen.X86.Generate (srchOf keyImpl genCode)

/-- `vg_rsa_generate`, with its cleanup, returns without secret residue,
whatever the implementation `v` of the Miller–Rabin round. -/
theorem generate_scrubbed (v : RoundImpl) :
    VerifiedScrubbed target (Impl.RsaKeyGen.X86.Fn.generate (srchOf v).call keyImpl.call)
      Proof.RsaKeyGen.X86.Generate.contract 32 :=
  verifiedScrubbedAll (api := Spec.RsaKeyGen.keySearchApi)
    { code := genCode v
      verified := Proof.RsaKeyGen.X86.Generate.gen_verified v
      spSafe := Proof.RsaKeyGen.X86.Generate.genCode_sp v }
    (keySearchOut Impl.RsaKeyGen.TrialTable32.consts Proof.RsaKeyGen.X86.Generate.stack)
    (hs := Proof.RsaKeyGen.X86.GenScrub.gen_scrub v)

/-- `vg_rsa_generate`, with its cleanup, writes `esp` only by its frames. -/
theorem generate_spSafe (v : RoundImpl) :
    (Impl.RsaKeyGen.X86.Fn.generate (srchOf v).call keyImpl.call).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.RsaKeyGen.X86.Generate.genCode_sp v)

end VG.Proof.RsaKeyGen.X86.Scrub
