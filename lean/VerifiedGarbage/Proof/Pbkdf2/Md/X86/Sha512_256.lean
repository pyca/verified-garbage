import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances

/-!
# HMAC-SHA-512/256's `init` and `finalize` and PBKDF2-HMAC-SHA-512/256's `iterate` on x86 (32-bit)

The generic proofs at SHA-512/256 (see `Instances.lean`): the taint checks of
their blocks, and their contracts moved to the shared ones (`sig_implies`).
-/

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initW initG finW finG iterW iterG countF)

theorem sha512_256_iterChecks : Iterate.Checks sha512_256M := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_256_finChecks : HmacFin.Checks sha512_256M := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_256_iterImp : (iterW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 32 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 32 234

theorem sha512_256_finImp : (finW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.finalizeScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 192 32 234
  sig_implies [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 192 32 234

theorem sha512_256_iterate : Verified X86.target sha512_256M.iterate (Spec.Hmac.sha512_256I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW sha512_256Ok sha512_256_iterChecks (by decide) sha512_256_iterImp.sat_left).of_implies sha512_256_iterImp

theorem sha512_256_finalize : Verified X86.target sha512_256M.hmacFin (Spec.Hmac.sha512_256I.finalizeScratchContract X86.abi 48) :=
  (HmacFin.verifiedW sha512_256Ok sha512_256_finChecks (by decide) sha512_256_finImp.sat_left).of_implies sha512_256_finImp

theorem sha512_256_initChecks : HmacInit.Checks sha512_256M := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_256_initImp : (initW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.initScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 234
  sig_implies [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 234

theorem sha512_256_init : Verified X86.target sha512_256M.hmacInit (Spec.Hmac.sha512_256I.initScratchContract X86.abi 48) :=
  (HmacInit.verifiedW sha512_256Ok sha512_256_initChecks (by decide) sha512_256_initImp.sat_left).of_implies sha512_256_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances
