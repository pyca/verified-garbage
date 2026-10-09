import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances

/-!
# HMAC-SHA-512's `init` and `finalize` and PBKDF2-HMAC-SHA-512's `iterate` on x86 (32-bit)

The generic proofs at SHA-512 (see `Instances.lean`): the taint checks of
their blocks, and their contracts moved to the shared ones (`sig_implies`).
-/

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initW initG finW finG iterW iterG countF)

theorem sha512_iterChecks : Iterate.Checks sha512M' := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_finChecks : HmacFin.Checks sha512M' := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_iterImp : (iterW Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 64 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 64 234

theorem sha512_finImp : (finW Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.finalizeScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 192 64 234
  sig_implies [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 192 64 234

theorem sha512_iterate : Verified X86.target sha512M'.iterate (Spec.Hmac.sha512I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW sha512Ok' sha512_iterChecks (by decide) sha512_iterImp.sat_left).of_implies sha512_iterImp

theorem sha512_finalize : Verified X86.target sha512M'.hmacFin (Spec.Hmac.sha512I.finalizeScratchContract X86.abi 48) :=
  (HmacFin.verifiedW sha512Ok' sha512_finChecks (by decide) sha512_finImp.sat_left).of_implies sha512_finImp

theorem sha512_initChecks : HmacInit.Checks sha512M' := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_initImp : (initW Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.initScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 234
  sig_implies [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 234

theorem sha512_init : Verified X86.target sha512M'.hmacInit (Spec.Hmac.sha512I.initScratchContract X86.abi 48) :=
  (HmacInit.verifiedW sha512Ok' sha512_initChecks (by decide) sha512_initImp.sat_left).of_implies sha512_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances
