module

-- separate module: the function's static facts, which need none of the variants' instances (`Instances.lean`), so that a change to them does not rebuild it

public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenToSplit.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenSel
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM `open_split` on x86-64: the function

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_split`
calling any `vg_aes_gcm_encrypt_blocks` and `vg_aes_gcm_decrypt_blocks` `B`
and `vg_aes_gcm_decrypt_blocks_to` `T` loads no `mxcsr`, writes `rsp` only
in its frames and uses 56 bytes of stack (the call's arguments, its return
address and its stack), so it preserves what the ABI says
(`OpenSplitFn.of`): an internal function, which `openToSplit` calls.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenSplit

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

section
variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M)

theorem openSplit_mx :
    (OpenSplit.openSplit (v.withBlk B) T.fn).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, T.mx, OpenSplit.openSplit, openBody, OpenSplit.entry, OpenSplit.tagLen, OpenSplit.«prefix», OpenSplit.rest, oneAad, oneTag,
    oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, recv, Impl.AesGcm.X86_64.cmp, tagLenOk, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail,
    flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, ghash1, firstFlush, finTag,
    Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem openSplit_spAll :
    (OpenSplit.openSplit (v.withBlk B) T.fn).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, T.spAll, OpenSplit.openSplit, openBody, OpenSplit.entry, OpenSplit.tagLen, OpenSplit.«prefix», OpenSplit.rest, oneAad,
    oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, recv, Impl.AesGcm.X86_64.cmp, tagLenOk, absorbHead, absorbWhole, absorbTail, absorb, absorbPad,
    padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, ghash1, firstFlush,
    finTag, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem openSplit_xdepth : (OpenSplit.openSplit (v.withBlk B) T.fn).x86_64Depth ≤ 56 := by
  have e := B.encXd
  have d := B.decXd
  have t := T.xd
  simp only [OpenSplit.openSplit, openBody, OpenSplit.entry, OpenSplit.tagLen, OpenSplit.«prefix», OpenSplit.rest, oneAad, oneTag, oneCrypt,
    oneCryptG, oneCryptBlk, recv, Impl.AesGcm.X86_64.cmp, tagLenOk, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush,
    lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, ghash1, firstFlush, finTag, copyTag,
    copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons,
    List.length_nil, GcmImpl.withBlk, GcmImpl.callees, v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le,
    ↓reduceIte, Bool.false_eq_true]
  omega

end

/-- `vg_aes_gcm_open_split`, named `n`, calling `B` and `T`. -/
def _root_.VG.Proof.AesGcm.X86_64.OpenToSplit.OpenSplitFn.of (n : String) (v : GcmImpl) {M : CtxMode} (B : BlkFn M)
    (T : BlkToDecFn M) : OpenToSplit.OpenSplitFn M where
  fn := ⟨n, OpenSplit.openSplit (v.withBlk B) T.fn⟩
  ok s h := by
    obtain ⟨t, s', he, hg, hp⟩ := openSplitM_wp v B T h
    exact ⟨t, s', he, abiPreserved_of_exec (openSplit_mx v B T) he hg, hp⟩
  ct := openSplitM_ct v B T
  sp := SpSafe.of_all (openSplit_spAll v B T)
  xd := openSplit_xdepth v B T
  mx := openSplit_mx v B T
  spAll := openSplit_spAll v B T

section
variable (v : GcmImpl) {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24} (B : BlkFn (CtxMode.preparedN np hpn))
  (T : BlkToDecFn (CtxMode.preparedN np hpn)) {ks : Prog isa} (any : Bool)

theorem openSplitFast_mx (hk : (Impl.AesGcm.X86_64.FastOpen.tagP ks).allInstrs (fun i => !loadsMxcsr i) = true) :
    (FastOpen.openSplit (v.withBlk B) T.fn ks any).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, hk, T.mx, Fast.fastCond_mx, Fast.fastAad_mx, FastOpen.openSplit, FastOpen.runTo,
    FastOpen.tailKG, FastOpen.tailArgs, openRun, OpenSplit.mid, OpenSplit.entry, OpenSplit.tagLen,
    OpenSplit.«prefix», OpenSplit.rest, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte,
    Bool.false_eq_true, recv, Impl.AesGcm.X86_64.cmp, tagLenOk, absorbHead, absorbWhole, absorbTail, absorb,
    absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0,
    ghash1, firstFlush, finTag, Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr,
    v.gh.mxcsr, Bool.true_and, Bool.and_true]
  cases any <;> decide +kernel

theorem openSplitFast_spAll (hk : (Impl.AesGcm.X86_64.FastOpen.tagP ks).all (fun i => !X86_64.isa.writesSp i) = true) :
    (FastOpen.openSplit (v.withBlk B) T.fn ks any).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, hk, T.spAll, Fast.fastCond_spSafe, Fast.fastAad_spSafe, FastOpen.openSplit, FastOpen.runTo,
    FastOpen.tailKG, FastOpen.tailArgs, openRun, OpenSplit.mid, OpenSplit.entry, OpenSplit.tagLen,
    OpenSplit.«prefix», OpenSplit.rest, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte,
    Bool.false_eq_true, recv, Impl.AesGcm.X86_64.cmp, tagLenOk, absorbHead, absorbWhole, absorbTail, absorb,
    absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0,
    ghash1, firstFlush, finTag, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe,
    Bool.true_and, Bool.and_true]
  cases any <;> decide +kernel

theorem openSplitFast_xdepth (hk : (Impl.AesGcm.X86_64.FastOpen.tagP ks).x86_64Depth = 0) :
    (FastOpen.openSplit (v.withBlk B) T.fn ks any).x86_64Depth ≤ 56 := by
  have e := B.encXd
  have d := B.decXd
  have t := T.xd
  simp only [hk, Fast.fastCond_xdepth, Fast.fastAad_xdepth, FastOpen.openSplit, FastOpen.runTo, FastOpen.tailKG,
    FastOpen.tailArgs, openRun, OpenSplit.mid, OpenSplit.entry, OpenSplit.tagLen, OpenSplit.«prefix», OpenSplit.rest,
    oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, recv, Impl.AesGcm.X86_64.cmp, tagLenOk, absorbHead,
    absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG,
    crypt, cryptAl, tag, j0hash, j0, ghash1, firstFlush, finTag, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012,
    initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk,
    GcmImpl.callees, v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

end

/-- `vg_aes_gcm_open_split` on a prepared key context, named `n`, calling `B`
and `T`, with `open`'s path for TLS records (`FastOpen.openSplit`, its
keystream by `ks`) where `Fast.cond any` takes it. -/
def _root_.VG.Proof.AesGcm.X86_64.OpenToSplit.OpenSplitFn.ofFast (n : String) (hF : Short.ShortFacts) (v : GcmImpl)
    {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24} (B : BlkFn (CtxMode.preparedN np hpn)) (T : BlkToDecFn (CtxMode.preparedN np hpn))
    {ks : Prog isa} (hks : Short.KsOk ks) (hkr : Short.KsRel ks)
    (kmx : (Impl.AesGcm.X86_64.FastOpen.tagP ks).allInstrs (fun i => !loadsMxcsr i) = true)
    (ksp : (Impl.AesGcm.X86_64.FastOpen.tagP ks).all (fun i => !X86_64.isa.writesSp i) = true)
    (kxd : (Impl.AesGcm.X86_64.FastOpen.tagP ks).x86_64Depth = 0) (any : Bool) :
    OpenToSplit.OpenSplitFn (CtxMode.preparedN np hpn) where
  fn := ⟨n, FastOpen.openSplit (v.withBlk B) T.fn ks any⟩
  ok s h := by
    obtain ⟨t, s', he, hg, hp⟩ := openSplitG_wp (FastOpen.midSOk_fast (any := any) hF v B T hks) h
    exact ⟨t, s', he, abiPreserved_of_exec (openSplitFast_mx v B T any kmx) he hg, hp⟩
  ct := openSplitG_ct (FastOpen.midSRel_fast (any := any) hF v B T hks hkr)
  sp := SpSafe.of_all (openSplitFast_spAll v B T any ksp)
  xd := openSplitFast_xdepth v B T any kxd
  mx := openSplitFast_mx v B T any kmx
  spAll := openSplitFast_spAll v B T any ksp

end VG.Proof.AesGcm.X86_64.OpenSplit
