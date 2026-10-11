import VerifiedGarbage.Proof.AesGcm.X86_64.Short.KsA
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Main
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP

/-!
# AES-GCM on x86-64: `seal` ending without calls, with AES-NI

Untrusted: everything here is checked by Lean. `SealFin.seal` is the other
instances' body up to the whole blocks, then `Short.finishWith
Short.finKsA`: it leaves what `sealRun_ok` does (`Short.sealRunF_ok`, with
`finKsA_ksOk`), in two runs too (`Short.sealRunF_rel`, with `finKsA_rel`),
loads no `mxcsr`, never writes `rsp` and uses as much stack as the other
instances, and so preserves what the ABI says (`sealFM_correct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.SealFin

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Short (KsOk KsRel finKsA_ksOk finKsA_rel sealRunF_ok sealRunF_rel ShortFacts)
open Gcm.X86_64.Stitch (CtxMode)

theorem finishA_xdepth : (Impl.AesGcm.X86_64.Short.finishWith Impl.AesGcm.X86_64.Short.finKsA).x86_64Depth = 0 := by
  decide +kernel

variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M)

theorem sealFM_wp (hF : ShortFacts) {s : State} (hp : (Proof.AesGcm.sealX86_64M M).pre s) :
    WP isa (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' :=
  sealM_of hp fun C X E hNp hnl hal => sealRunF_ok hF finKsA_ksOk v B C X E hNp hnl hal

theorem sealFM_rel (hF : ShortFacts) {s₀ s₀' : State}
    (hp : (Proof.AesGcm.sealX86_64M M).pre s₀) (hp' : (Proof.AesGcm.sealX86_64M M).pre s₀')
    (hq : Proof.AesGcm.sealX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B))
      fun _ _ => True :=
  sealM_relOf hp hp' hq (fun C X E hNp hnl hal => sealRunF_ok hF finKsA_ksOk v B C X E hNp hnl hal)
    fun C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' =>
      sealRunF_rel hF finKsA_ksOk finKsA_rel v B C C' X X' hNp hnl hal hR hNp' hnl' hal' hR'

theorem sealFM_ct (hF : ShortFacts) :
    ConstantTime isa (Proof.AesGcm.sealX86_64M M).pre Proof.AesGcm.sealX86_64.pub
      (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)) :=
  ct_of_rel fun _ _ hp hp' hq => sealFM_rel v B hF hp hp' hq

theorem sealFM_mx :
    (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.SealFin.«seal», Impl.AesGcm.X86_64.SealFin.mid, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealFM_spSafe :
    (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.SealFin.«seal», Impl.AesGcm.X86_64.SealFin.mid, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealFM_xdepth : (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.SealFin.«seal», Impl.AesGcm.X86_64.SealFin.mid, finishA_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyLoop, xorLoop, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega

theorem sealFM_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.sealX86_64M M).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealFM_wp v B hF hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealFM_mx v B) he hg, hp⟩

end VG.Proof.AesGcm.X86_64.SealFin
