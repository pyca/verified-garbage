module

public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Verified
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-GCM-SIV on PPC64LE, without secret residue

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`, each followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbed`), which clears the
volatile registers they may write and the whole 1632-byte frame
(`withStackScratchArgs`) that holds their working space, the derived keys
among it, which they do not wipe themselves (the functions they call need
no working space). Their postconditions read the memory on return only within the
data and the tag, as on AArch64 (`Proof/AesGcmSiv/AArch64/Stitch/Verified.lean`).

The registrations take the law of GHASH and the equation of POLYVAL's input
with GHASH's that their proofs use (`seal_framed`) as arguments, which the
registration file gives: their proofs import the field algebra, which only
leaves of the import graph may import (`ci/check_lean_speed.py`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Aes.ScrubLocal VG.Proof.AesGcmSiv.PPC64LE

/-! ## Postconditions -/

theorem sealOut (stack : Nat) :
    PostOut (Spec.GcmSiv.sealContract PPC64LE.abi stack) (Spec.GcmSiv.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [schedule, rounds, nonce, aad, aadLen, data, len, tag], _ =>
      simp only [Spec.GcmSiv.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64,
        ArgWord.addr, ArgWord.int 64, ArgWord.addr] (Spec.GcmSiv.sealPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64,
        ArgWord.addr, ArgWord.int 64, ArgWord.addr] (Spec.GcmSiv.sealPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.GcmSiv.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hl hk
      rw [h key hl hk, bytesAt_of0 hb.2.2.2.1 (by simp), bytesAt_of0 hb.2.2.2.2 (by simp)]

theorem openOut (stack : Nat) :
    PostOut (Spec.GcmSiv.openContract PPC64LE.abi stack) (Spec.GcmSiv.openSig.retBits 64) := by
  -- The postcondition is a `match` on a decryption: prove the locality
  -- by intros, so that no expected type of a `fun` is reduced to it.
  refine postOut_of_local ScrubAbi.plain ?_
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [schedule, rounds, nonce, aad, aadLen, data, len, tag], _ =>
    simp only [Spec.GcmSiv.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64,
      ArgWord.addr, ArgWord.int 64, ArgWord.addr] (Spec.GcmSiv.openPost 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64,
      ArgWord.addr, ArgWord.int 64, ArgWord.addr] (Spec.GcmSiv.openPost 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.GcmSiv.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    rw [bytesAt_of0 (n := (BitVec.setWidth 64 len).toNat) hb.2.2.2.1 (by simp)]
    exact @h

/-! ## The functions as emitted -/

/-- `vg_aes_gcm_siv_seal` as emitted (`Impl.AesGcmSiv.PPC64LE.Fn.seal`) meets its
contract in constant time and returns without secret residue. -/
theorem seal_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] (hti : TagInputEq) :
    VerifiedScrubbed PPC64LE.target Impl.AesGcmSiv.PPC64LE.Fn.seal
      (Spec.GcmSiv.sealContract PPC64LE.abi 1632) 0 :=
  verifiedScrubbed (api := Spec.GcmSiv.sealApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgs 1632 0 Impl.AesGcmSiv.PPC64LE.«seal»
      verified := Proof.AesGcmSiv.seal_keyed (seal_framed hti) }
    1632 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17,
        .v18, .v19]⟩
    (sealOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_gcm_siv_open` as emitted (`Impl.AesGcmSiv.PPC64LE.Fn.open`) meets its
contract in constant time and returns without secret residue. -/
theorem open_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] (hti : TagInputEq) :
    VerifiedScrubbed PPC64LE.target Impl.AesGcmSiv.PPC64LE.Fn.open
      (Spec.GcmSiv.openContract PPC64LE.abi 1632) 32 :=
  verifiedScrubbed (api := Spec.GcmSiv.openApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgs 1632 0 Impl.AesGcmSiv.PPC64LE.«open»
      verified := Proof.AesGcmSiv.open_keyed (open_framed hti) }
    1632 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17,
        .v18, .v19]⟩
    (openOut _)
    (by dsimp only; lit_decide)

end VG.Proof.AesGcmSiv.PPC64LE.Scrub
