module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.Scratch
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Init
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.InitCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamCrypt
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamCryptCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.FinCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Seal
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.OneCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Open
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.OpenCT
import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.X86_64.Lit

/-!
# SM4-GCM on x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementation `v` of `vg_ghash`, in AES-GCM's `GcmImpl`, of which
the code calls only `vg_ghash`), a state satisfying each precondition, and
the shared contracts of `Spec/Sm4/Gcm/Contract.lean` with the working space
as a last argument (`Proof/Sm4Gcm/Scratch.lean`), with the `stkN` bytes of
stack below the stack pointer that the calls of `vg_sm4_ctr32` use.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.Impl.Sm4Gcm.X86_64
open VG.Impl.AesGcm.X86_64 (cryptHead absorb absorbPad lens j0 recv cmp tagOut tagLenOk partWith
  firstFlush streamLoad oneAad xorLoop flush absorbHead absorbWhole absorbTail padTail ghash1 j0hash
  minLen copyLoop headPart)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

theorem ctrFn_mx : ctrFn.code.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem keyFn_mx : keyFn.code.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem ctrFn_spSafe : ctrFn.code.all (fun i => !X86_64.isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  exact congrArg Bool.not (ctr_spSafe i hi)

theorem keyFn_spSafe : keyFn.code.all (fun i => !X86_64.isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  exact congrArg Bool.not (key_spSafe i hi)

theorem ctrFn_depth : ctrFn.code.x86_64Depth ≤ 3216 := ctr_depth

theorem keyFn_depth : keyFn.code.x86_64Depth ≤ 3144 := key_depth

theorem init_mx : init.allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, Code.allInstrs]
  rw [ctrFn_mx, keyFn_mx]
  decide +kernel

theorem init_spSafe : init.all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, Code.all]
  rw [ctrFn_spSafe, keyFn_spSafe]
  decide +kernel

theorem init_xdepth : init.x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  have := keyFn_depth
  simp only [init, Code.x86_64Depth, Nat.max_le, stkN]
  omega

theorem init_correct (s : State) (hs : Proof.Sm4Gcm.initX86_64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec init_mx he hg, hp⟩

/-- A state satisfying `vg_sm4_gcm_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x3000, 2560⟩]

theorem init_verified :
    Verified X86_64.target init (Proof.Sm4Gcm.initScratchContract X86_64.abi stkN) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Proof.Sm4Gcm.initScratchContract, Proof.Sm4Gcm.initScratchSig, Spec.Sm4.Gcm.initPost,
      Proof.Sm4Gcm.initX86_64, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk,
      Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret, stkN, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [initSat] using initSat)

section
variable (v : GcmImpl)

theorem streamEncrypt_mx : (streamEncrypt v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, ctrFn_mx, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  rw [ctrFn_mx]
  decide +kernel

theorem streamEncrypt_spSafe : (streamEncrypt v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.all, ctrFn_spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  rw [ctrFn_spSafe]
  decide +kernel

theorem streamEncrypt_xdepth : (streamEncrypt v.callees).x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.x86_64Depth, v.gh.noStack, Nat.max_le, stkN]
  omega

theorem streamEncrypt_correct (s : State) (hs : Proof.Sm4Gcm.streamEncryptX86_64.pre s) :
    ∃ t s', Exec isa (streamEncrypt v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.streamEncryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamEncrypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamEncrypt_mx v) he hg, hp⟩

theorem streamDecrypt_mx : (streamDecrypt v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, ctrFn_mx, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  rw [ctrFn_mx]
  decide +kernel

theorem streamDecrypt_spSafe : (streamDecrypt v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.all, ctrFn_spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  rw [ctrFn_spSafe]
  decide +kernel

theorem streamDecrypt_xdepth : (streamDecrypt v.callees).x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.x86_64Depth, v.gh.noStack, Nat.max_le, stkN]
  omega

theorem streamDecrypt_correct (s : State) (hs : Proof.Sm4Gcm.streamDecryptX86_64.pre s) :
    ∃ t s', Exec isa (streamDecrypt v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.streamDecryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamDecrypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamDecrypt_mx v) he hg, hp⟩

theorem streamFinish_mx : (streamFinish v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, ctrFn_mx, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  rw [ctrFn_mx]
  decide +kernel

theorem streamFinish_spSafe : (streamFinish v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.all, ctrFn_spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  rw [ctrFn_spSafe]
  decide +kernel

theorem streamFinish_xdepth : (streamFinish v.callees).x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.x86_64Depth, v.gh.noStack, Nat.max_le, stkN]
  omega

theorem streamFinish_correct (s : State) (hs : Proof.Sm4Gcm.streamFinishX86_64.pre s) :
    ∃ t s', Exec isa (streamFinish v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.streamFinishX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamFinish_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamFinish_mx v) he hg, hp⟩

theorem streamVerify_mx : (streamVerify v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, ctrFn_mx, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  rw [ctrFn_mx]
  decide +kernel

theorem streamVerify_spSafe : (streamVerify v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.all, ctrFn_spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  rw [ctrFn_spSafe]
  decide +kernel

theorem streamVerify_xdepth : (streamVerify v.callees).x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.x86_64Depth, v.gh.noStack, Nat.max_le, stkN]
  omega

theorem streamVerify_correct (s : State) (hs : Proof.Sm4Gcm.streamVerifyX86_64.pre s) :
    ∃ t s', Exec isa (streamVerify v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.streamVerifyX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamVerify_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamVerify_mx v) he hg, hp⟩

theorem seal_mx : («seal» v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, ctrFn_mx, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  rw [ctrFn_mx]
  decide +kernel

theorem seal_spSafe : («seal» v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.all, ctrFn_spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  rw [ctrFn_spSafe]
  decide +kernel

theorem seal_xdepth : («seal» v.callees).x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.x86_64Depth, v.gh.noStack, Nat.max_le, stkN]
  omega

theorem seal_correct (s : State) (hs : Proof.Sm4Gcm.sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (seal_mx v) he hg, hp⟩

theorem open_mx : («open» v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, ctrFn_mx, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  rw [ctrFn_mx]
  decide +kernel

theorem open_spSafe : («open» v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.all, ctrFn_spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  rw [ctrFn_spSafe]
  decide +kernel

theorem open_xdepth : («open» v.callees).x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.x86_64Depth, v.gh.noStack, Nat.max_le, stkN]
  omega

theorem open_correct (s : State) (hs : Proof.Sm4Gcm.openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (open_mx v) he hg, hp⟩

end

/-- A state satisfying the precondition of `vg_sm4_gcm_stream_encrypt` and `_decrypt` (with no data, and
`scratch` at 0). -/
def crSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .r8 => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0, 2560⟩]

theorem streamEncrypt_verified (v : GcmImpl) :
    Verified X86_64.target (streamEncrypt v.callees)
      (Proof.Sm4Gcm.streamEncryptScratchContract X86_64.abi stkN) :=
  Verified.of_correct (streamEncrypt_correct v) (streamEncrypt_ct v) (by
    sig_implies [Proof.Sm4Gcm.streamEncryptScratchContract, Proof.Sm4Gcm.streamCryptScratchSig,
      Spec.Sm4.Gcm.streamEncryptPost, Proof.Sm4Gcm.streamEncryptX86_64, Proof.Sm4Gcm.streamCryptPre,
      Proof.Sm4Gcm.streamCryptPub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using crSat)

theorem streamDecrypt_verified (v : GcmImpl) :
    Verified X86_64.target (streamDecrypt v.callees)
      (Proof.Sm4Gcm.streamDecryptScratchContract X86_64.abi stkN) :=
  Verified.of_correct (streamDecrypt_correct v) (streamDecrypt_ct v) (by
    sig_implies [Proof.Sm4Gcm.streamDecryptScratchContract, Proof.Sm4Gcm.streamCryptScratchSig,
      Spec.Sm4.Gcm.streamDecryptPost, Proof.Sm4Gcm.streamDecryptX86_64, Proof.Sm4Gcm.streamCryptPre,
      Proof.Sm4Gcm.streamCryptPub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using crSat)

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition. -/
def finSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .r8 => 0x5000 | .r9 => 0x6000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩]

theorem streamFinish_verified (v : GcmImpl) :
    Verified X86_64.target (streamFinish v.callees)
      (Proof.Sm4Gcm.streamFinishScratchContract X86_64.abi stkN) :=
  Verified.of_correct (streamFinish_correct v) (streamFinish_ct v) (by
    sig_implies [Proof.Sm4Gcm.streamFinishScratchContract, Proof.Sm4Gcm.streamFinishScratchSig,
      Spec.Sm4.Gcm.streamFinishPost, Proof.Sm4Gcm.streamFinishX86_64, Proof.Sm4Gcm.finPre,
      X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [finSat] using finSat)

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition (with no tag, and `work` at 0). -/
def verSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .r8 => 0x5000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x3000, 80⟩, ⟨0, 2560⟩]

theorem streamVerify_verified (v : GcmImpl) :
    Verified X86_64.target (streamVerify v.callees)
      (Proof.Sm4Gcm.streamVerifyScratchContract X86_64.abi stkN) :=
  Verified.of_correct (streamVerify_correct v) (streamVerify_ct v) (by
    sig_implies [Proof.Sm4Gcm.streamVerifyScratchContract, Proof.Sm4Gcm.streamVerifyScratchSig,
      Spec.Sm4.Gcm.streamVerifyPost, Proof.Sm4Gcm.streamVerifyX86_64, Proof.Sm4Gcm.verifyPre,
      X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [verSat] using verSat)

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition (with no nonce, additional data or data, `tag`
at `0x3000` and `work` at 0). -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0, 2560⟩]

theorem seal_verified (v : GcmImpl) :
    Verified X86_64.target («seal» v.callees) (Proof.Sm4Gcm.sealScratchContract X86_64.abi stkN) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.Sm4Gcm.sealScratchContract, Proof.Sm4Gcm.sealScratchSig, Spec.Sm4.Gcm.sealPost,
      Proof.Sm4Gcm.sealX86_64, Proof.Sm4Gcm.sealPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub,
      X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [sealSat] using sealSat)

/-- A state satisfying `vg_sm4_gcm_open`'s precondition (with no nonce, additional data, data or tag, and
`work` at 0). -/
def openSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 32⟩]
  wr := [⟨0, 0⟩, ⟨0, 2560⟩]

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : GcmImpl) :
    Verified X86_64.target («open» v.callees) (Proof.Sm4Gcm.openScratchContract X86_64.abi stkN) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by sig_implies_pre [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
        Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.openLeak,
        Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
      post := by sig_implies_post [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
        Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.openLeak,
        Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.openLeak,
          Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.openLeak,
          Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
        sig_simp [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.openLeak,
          Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
          [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
        Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.openLeak,
        Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [openSat] using openSat }

end VG.Proof.Sm4Gcm.X86_64
