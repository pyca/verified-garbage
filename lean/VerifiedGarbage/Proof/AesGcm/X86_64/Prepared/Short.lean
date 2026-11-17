module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.PowP
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.KsA
import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Impl.AesGcm.X86_64.SealFin
public import VerifiedGarbage.Impl.AesGcm.X86_64.FastSeal
public import VerifiedGarbage.Impl.AesGcm.X86_64.FastOpen
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenTag
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Main
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.SealEnd
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT

/-! ### `AesGcm.X86_64.Short.VerifiedP`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.Fast.SealSel`, which this module and modules that import it used -/

section

/-!
# AES-GCM `seal`'s path for TLS records

Untrusted: everything here is checked by Lean. With a prepared key context,
`FastSeal.run` is `Short.sealLong` with `Fast.aad`, which leaves what
`oneAad` does (`Fast.aad_mid`) and branches alike in two runs
(`Fast.aad_rel`), and `Short.finishP`, which ends as `Short.finishWith` does
(`Fast.finOk_finishP`), so it leaves what `sealRunW_ok` does
(`Fast.sealRunFin_ok`), and does it in two runs with the same addresses and
branches (`Fast.sealRunP_rel`); so `FastSeal.sel`
does, with `other` for the inputs `Fast.cond` turns away: `sealSel_ok`,
`sealSel_rel`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.FastSeal

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk KsRel SealLongOk SealLongRel rel_next condS_of)
open VG.Proof.AesGcm.X86_64.Fast (IsFast aad_mid condE_ok finOk_finishP sealRunFin_ok sealRunP_rel)

variable {any : Bool}

/-- `sel`: this path for the inputs it takes, `other` for the rest. -/
theorem sealSel_ok (hF : ShortFacts) (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hpn)) {ks : Prog isa} (hks : KsOk ks)
    {other : Prog isa} (ho : SealLongOk (CtxMode.preparedN np hpn) other) :
    SealLongOk (CtxMode.preparedN np hpn) (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) other ks any) := by
  intro s s₁ Ctx W SP Np A D nl al n C X E hNp hnl hal
  unfold Impl.AesGcm.X86_64.FastSeal.sel
  refine WP.seq (WP.mono (condE_ok C E hnl hal) fun s₃ ⟨hz, E₃, _⟩ => ?_)
  refine WP.ite (decide ¬IsFast nl al n any) (eval_e hz) (fun _ => ho C X E₃ hNp hnl hal) fun h => ?_
  obtain ⟨h12, h17, -⟩ : IsFast nl al n any := Decidable.not_not.mp (of_decide_eq_false h)
  subst h12
  exact sealRunFin_ok B (finOk_finishP hF hks) C X hal (aad_mid hF C X E₃ hNp hnl hal (by omega_using [h17]))

/-- `sel` in two runs: the same path, and on it the same addresses and
branches. -/
theorem sealSel_rel (hF : ShortFacts) (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hpn)) {ks : Prog isa} (hks : KsOk ks)
    (hkr : KsRel ks) {other : Prog isa} (ho : SealLongRel (CtxMode.preparedN np hpn) other) :
    SealLongRel (CtxMode.preparedN np hpn) (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) other ks any) := by
  intro s₀ s₀' Ctx W SP Np A D nl al n R C C' X X' hNp hnl hal hR hNp' hnl' hal' hR'
  have hlt := C.data.ok.lt
  unfold Impl.AesGcm.X86_64.FastSeal.sel
  have hw : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n), (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → ∀ s, OneEntry s₀ Ctx W SP A D n s →
      WP isa (Impl.AesGcm.X86_64.Fast.cond any) s fun u => u.zf = some (decide ¬IsFast nl al n any) ∧
        OneEntry s₀ Ctx W SP A D n u :=
    fun C hnl hal s h => WP.mono (condE_ok C h hnl hal) fun _ ⟨z, E, _⟩ => ⟨z, E⟩
  have c := rel_next (Fast.cond_rel (F₁ := OneEntry s₀ Ctx W SP A D n) (F₂ := OneEntry s₀' Ctx W SP A D n)
      (fun _ h => condS_of h hnl hal) (fun _ h => condS_of h hnl' hal')
      (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _) (by omega_using [hlt]))
    (hw C hnl hal) (hw C' hnl' hal')
  refine RelCT.seq c (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    ((ho C C' X X' hNp hnl hal hR hNp' hnl' hal' hR').mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h) ?_)
  by_cases hs : IsFast nl al n any
  · obtain ⟨h12, h17, -⟩ := hs
    subst h12
    have L := C.lay
    exact (sealRunP_rel hks hkr B C C' X X' hNp hnl hal hR hNp' hnl' hal' hR'
      ((Fast.aad_rel L C.dE (M := (CtxMode.preparedN np hpn)) (R := R) (Np := Np) (A := A) (al := al) (by omega_using [h17])).mono
        (P' := fun (s₁ s₂ : State) => OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
        (fun _ _ g => ⟨g.1.aadPre C X hNp hnl hal hR, g.2.aadPre C' X' hNp' hnl' hal' hR'⟩) fun _ _ _ => trivial)
      (fun _ h => aad_mid hF C X h hNp hnl hal (by omega_using [h17]))
      (fun _ h => aad_mid hF C' X' h hNp' hnl' hal' (by omega_using [h17]))).mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h
  · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [hs] at this

end VG.Proof.AesGcm.X86_64.FastSeal

end

end

/-! ### `AesGcm.X86_64.Short.Verified`, which this module and modules that import it used -/

section

/-!
# AES-GCM's short path on x86-64: the functions verified

Untrusted: everything here is checked by Lean. `seal` and `open` with the
short path load no `mxcsr`, never write `rsp` and use as much stack as the
other instances (the short path's code and the end of the long `seal` use none: `cond_xdepth`,
`sealShort_xdepth`, `openShort_xdepth`, `finish_xdepth`), and so they preserve what the ABI
says (`sealM_correct`, `openM_correct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

theorem cond_xdepth : Impl.AesGcm.X86_64.Short.cond.x86_64Depth = 0 := by decide +kernel
theorem sealShort_xdepth : Impl.AesGcm.X86_64.Short.sealShort.x86_64Depth = 0 := by decide +kernel
theorem openShort_xdepth : Impl.AesGcm.X86_64.Short.openShort.x86_64Depth = 0 := by decide +kernel
theorem finish_xdepth : Impl.AesGcm.X86_64.Short.finish.x86_64Depth = 0 := by decide +kernel

variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M)

theorem sealM_mx : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealM_spSafe : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealM_xdepth : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, cond_xdepth, sealShort_xdepth, finish_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [e]

theorem sealM_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.sealX86_64M M).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealM_wp hF v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealM_mx v B) he hg, hp⟩

theorem openM_mx : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openM_spSafe : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openM_xdepth : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, cond_xdepth, openShort_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte,
    Bool.false_eq_true]
  omega_using [d]

theorem openM_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.openX86_64M M).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := openM_wp hF v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (openM_mx v B) he hg, hp⟩

end VG.Proof.AesGcm.X86_64.Short

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

namespace GcmImpl

/-- `vg_aes_gcm_seal`'s code calling `c`, with the short path if `v` has it,
or else ending without calls if `v` does. -/
def sealCode (v : GcmImpl) (c : Callees) : Prog isa :=
  if v.short then Impl.AesGcm.X86_64.Short.«seal» c
  else if v.fin then Impl.AesGcm.X86_64.SealFin.«seal» c else «seal» c

/-- `vg_aes_gcm_open`'s code calling `c`, with the short path if `v` has it. -/
def openCode (v : GcmImpl) (c : Callees) : Prog isa :=
  if v.short then Impl.AesGcm.X86_64.Short.«open» c else «open» c

end GcmImpl

variable (v : GcmImpl)

theorem sealCode_spSafe {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCode (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.sealCode; split
  · exact Short.sealM_spSafe v B
  · split
    · exact SealFin.sealFM_spSafe v B
    · exact sealM_spSafe v B

theorem openCode_spSafe {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.openCode (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.openCode; split
  · exact Short.openM_spSafe v B
  · exact openM_spSafe v B

/-- `vg_aes_gcm_seal`, with the short path if `v` has it, or ending without
calls if `v` does. -/
theorem sealSel_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode v.callees))
      (Proof.AesGcm.sealRoundsContract X86_64.abi 2624) := by
  unfold GcmImpl.sealCode; split
  · exact sealCode_framed (sealCode_verified (fun s hs => Short.sealM_correct v v.blkB hF s ⟨hs, trivial⟩)
      (ct_of_rel fun _ _ hp hp' hq => Short.sealM_rel hF v v.blkB ⟨hp, trivial⟩ ⟨hp', trivial⟩ hq))
      (Short.sealM_spSafe v v.blkB) (Short.sealM_xdepth v v.blkB)
  · split
    · exact sealCode_framed (sealCode_verified (fun s hs => SealFin.sealFM_correct v v.blkB hF s ⟨hs, trivial⟩)
        (ct_of_rel fun _ _ hp hp' hq => SealFin.sealFMW_rel v v.blkB (SealFin.sealLongOk_mid v v.blkB hF)
          (SealFin.sealLongRel_mid v v.blkB hF) ⟨hp, trivial⟩ ⟨hp', trivial⟩ hq))
        (SealFin.sealFM_spSafe v v.blkB) (SealFin.sealFM_xdepth v v.blkB)
    · exact seal_framed v

/-- `vg_aes_gcm_open`, with the short path if `v` has it. -/
theorem openSel_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode v.callees))
      (Proof.AesGcm.openRoundsContract X86_64.abi 2632) := by
  unfold GcmImpl.openCode; split
  · exact openCode_framed (openCode_verified (fun s hs => Short.openM_correct v v.blkB hF s ⟨hs, trivial⟩)
      (ct_of_rel fun _ _ hp hp' hq => Short.openM_rel hF v v.blkB ⟨hp, trivial⟩ ⟨hp', trivial⟩ hq))
      (Short.openM_spSafe v v.blkB) (Short.openM_xdepth v v.blkB)
  · exact open_framed v

/-- `vg_aes_gcm_seal_precomputed`, with the short path if `v` has it. -/
theorem sealSelP_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode (v.withBlk v.blkP)))
      (Proof.AesGcm.sealPrecomputedRoundsContract X86_64.abi 2624) := by
  unfold GcmImpl.sealCode; split
  · exact sealPCode_framed (sealPCode_verified (Short.sealM_correct v v.blkP hF) (Short.sealM_ct hF v v.blkP))
      (Short.sealM_spSafe v v.blkP) (Short.sealM_xdepth v v.blkP)
  · split
    · exact sealPCode_framed (sealPCode_verified (SealFin.sealFM_correct v v.blkP hF) (SealFin.sealFM_ct v v.blkP hF))
        (SealFin.sealFM_spSafe v v.blkP) (SealFin.sealFM_xdepth v v.blkP)
    · exact sealP_framed v

/-- `vg_aes_gcm_open_precomputed`, with the short path if `v` has it. -/
theorem openSelP_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode (v.withBlk v.blkP)))
      (Proof.AesGcm.openPrecomputedRoundsContract X86_64.abi 2632) := by
  unfold GcmImpl.openCode; split
  · exact openPCode_framed (openPCode_verified (Short.openM_correct v v.blkP hF) (Short.openM_ct hF v v.blkP))
      (Short.openM_spSafe v v.blkP) (Short.openM_xdepth v v.blkP)
  · exact openP_framed v

end VG.Proof.AesGcm.X86_64

end

end

/-! ### `AesGcm.X86_64.Fast.OpenSel`, which only this module used -/

section

/-!
# AES-GCM `open`'s path for TLS records: after the entry

Untrusted: everything here is checked by Lean. With a prepared key context,
`FastOpen.run` is `Short.openLong` with `Fast.aad`, which leaves what
`oneAad` does (`Fast.aad_mid`), `tagP`, which leaves what `oneTag 112` does
and `K[1]` (`tagP_okP`), and `tailK`, which decrypts the bytes left with it
(`crOk_tailK`), so it leaves what `openOk_ok` does (`openOkW_ok`), and
`FastOpen.sel` too, with `other` for the inputs `Fast.cond` turns away:
`openSel_ok`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.FastOpen

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk LongOk)
open VG.Proof.AesGcm.X86_64.Fast (IsFast aad_mid condE_ok)

variable {any : Bool}

theorem tagP_mx : (Impl.AesGcm.X86_64.FastOpen.tagP : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel
theorem tagPA_mx :
    (Impl.AesGcm.X86_64.FastOpen.tagP Impl.AesGcm.X86_64.Short.finKsA : Prog isa).allInstrs (fun i => !loadsMxcsr i) =
      true := by
  decide +kernel
theorem tagPA_spSafe :
    (Impl.AesGcm.X86_64.FastOpen.tagP Impl.AesGcm.X86_64.Short.finKsA : Prog isa).all
      (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem tagPA_xdepth : (Impl.AesGcm.X86_64.FastOpen.tagP Impl.AesGcm.X86_64.Short.finKsA : Prog isa).x86_64Depth = 0 := by
  decide +kernel
theorem tagP_spSafe : (Impl.AesGcm.X86_64.FastOpen.tagP : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem tagP_xdepth : (Impl.AesGcm.X86_64.FastOpen.tagP : Prog isa).x86_64Depth = 0 := by decide +kernel

/-- `sel`: this path for the inputs it takes, `other` for the rest. -/
theorem openSel_ok (hF : ShortFacts) (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hpn)) {ks : Prog isa} (hks : KsOk ks)
    {other : Prog isa} (ho : LongOk (CtxMode.preparedN np hpn) other) :
    LongOk (CtxMode.preparedN np hpn) (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) other ks any) := by
  intro s s₂ Ctx W SP Np A D T nl al n t C X E hNp hnl hal hTa hTar hTr oT oA htl hok
  unfold Impl.AesGcm.X86_64.FastOpen.sel
  refine WP.seq (WP.mono (condE_ok C E hnl hal) fun s₃ ⟨hz, E₃, K⟩ => ?_)
  rw [← K.mem] at htl
  refine WP.ite (decide ¬IsFast nl al n any) (eval_e hz) (fun _ => ho C X E₃ hNp hnl hal hTa hTar hTr oT oA htl hok)
    fun h => ?_
  obtain ⟨h12, h17, -⟩ : IsFast nl al n any := Decidable.not_not.mp (of_decide_eq_false h)
  subst h12
  exact openOkW_ok v B (tagP_okP hF hks) pStable_kOk crOk_tailK C X hal hTa hTar hTr oT oA htl hok
    (aad_mid hF C X E₃ hNp hnl hal (by omega_using [h17]))

/-- `openFin lng`, for `lng` that leaves what `openOk_ok` does. -/
theorem openFinW_wp {M : CtxMode} {lng : Prog isa} (hlng : LongOk M lng) {s : State}
    (hp : (Proof.AesGcm.openX86_64M M).pre s) :
    WP isa (Impl.AesGcm.X86_64.FastOpen.openFin lng) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' :=
  openM_of hp fun C X E hNp hnl hal _ hTa hTar hTr oT oA htl hok => hlng C X E hNp hnl hal hTa hTar hTr oT oA htl hok

end VG.Proof.AesGcm.X86_64.FastOpen

end

end


/-!
# AES-GCM's short path on x86-64 with a prepared key context: the functions verified

Untrusted: everything here is checked by Lean. With a prepared key context,
`seal` and `open` take their powers from it (`Short.powersP`, `Short.ghashP`):
`sealMP_correct`, `openMP_correct`, as `sealM_correct` and `openM_correct`
for `powers`, and the code of the instances with the short path
(`GcmImpl.sealCodeP`, `GcmImpl.openCodeP`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

theorem sealShortP_xdepth :
    (Impl.AesGcm.X86_64.Short.sealShort Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP).x86_64Depth = 0 := by decide +kernel
theorem finishK_xdepth : (Impl.AesGcm.X86_64.Short.finishWith Impl.AesGcm.X86_64.Short.finKs).x86_64Depth = 0 :=
  finish_xdepth
theorem finishPK_xdepth : (Impl.AesGcm.X86_64.Short.finishP Impl.AesGcm.X86_64.Short.finKs).x86_64Depth = 0 := by
  decide +kernel
theorem finishPA_xdepth : (Impl.AesGcm.X86_64.Short.finishP Impl.AesGcm.X86_64.Short.finKsA).x86_64Depth = 0 := by
  decide +kernel

theorem openShortP_xdepth :
    (Impl.AesGcm.X86_64.Short.openShort Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP).x86_64Depth = 0 := by decide +kernel

variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M)

theorem sealMP_mx : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)))).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_mx, Fast.fastAad_mx, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealMP_spSafe : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)))).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_spSafe, Fast.fastAad_spSafe, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealMP_xdepth :
    (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)))).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_xdepth, Fast.fastAad_xdepth, cond_xdepth, sealShortP_xdepth, finish_xdepth, finishK_xdepth, finishPK_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [e]

theorem openMP_mx : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))) Impl.AesGcm.X86_64.Short.ghashP).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_mx, Fast.fastAad_mx, FastOpen.tagP_mx, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openMP_spSafe : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))) Impl.AesGcm.X86_64.Short.ghashP).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_spSafe, Fast.fastAad_spSafe, FastOpen.tagP_spSafe, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openMP_xdepth :
    (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))) Impl.AesGcm.X86_64.Short.ghashP).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Impl.AesGcm.X86_64.FastOpen.tailK, Fast.fastCond_xdepth,
    Fast.fastAad_xdepth, FastOpen.tagP_xdepth, cond_xdepth, openShortP_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte,
    Bool.false_eq_true]
  omega_using [d]

theorem sealFinP_mx : (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.SealFin.mid (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.SealFin.«seal», Impl.AesGcm.X86_64.SealFin.mid, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_mx, Fast.fastAad_mx, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealFinP_spSafe : (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.SealFin.mid (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.SealFin.«seal», Impl.AesGcm.X86_64.SealFin.mid, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_spSafe, Fast.fastAad_spSafe, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealFinP_xdepth : (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.SealFin.mid (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.SealFin.«seal», Impl.AesGcm.X86_64.SealFin.mid, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_xdepth, Fast.fastAad_xdepth, SealFin.finishA_xdepth, finishPA_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [e]

theorem openFinP_mx : (Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.FastOpen.openFin, Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_mx, Fast.fastAad_mx, FastOpen.tagPA_mx, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openFinP_spSafe : (Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.FastOpen.openFin, Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_spSafe, Fast.fastAad_spSafe, FastOpen.tagPA_spSafe, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openFinP_xdepth : (Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.FastOpen.openFin, Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Impl.AesGcm.X86_64.FastOpen.tailK, Fast.fastCond_xdepth, Fast.fastAad_xdepth, FastOpen.tagPA_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [d]

section
variable (B : BlkFn CtxMode.prepared)

theorem sealMP_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.sealX86_64M CtxMode.prepared).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)))) s t s' ∧
      abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealMW_wp hF v B powOk_powersP
    (FastSeal.sealSel_ok hF v B finKs_ksOk (sealLongOk_sealLong hF v B)) hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealMP_mx v B) he hg, hp⟩

theorem openMP_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.openX86_64M CtxMode.prepared).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))) Impl.AesGcm.X86_64.Short.ghashP) s t s' ∧
      abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := openMW_wp hF v B powOk_powersP
    (FastOpen.openSel_ok hF v B finKs_ksOk (longOk_openLong v B)) hs
  exact ⟨t, s', he, abiPreserved_of_exec (openMP_mx v B) he hg, hp⟩

end

section
variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24} (B : BlkFn (CtxMode.preparedN np hpn))

theorem sealFinP_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.sealX86_64M (CtxMode.preparedN np hpn)).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.SealFin.mid (v.withBlk B))
        Impl.AesGcm.X86_64.Short.finKsA true)) s t s' ∧
      abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := SealFin.sealFMW_wp v B
    (FastSeal.sealSel_ok hF v B finKsA_ksOk (SealFin.sealLongOk_mid v B hF)) hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealFinP_mx v B) he hg, hp⟩

theorem openFinP_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.openX86_64M (CtxMode.preparedN np hpn)).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))
        Impl.AesGcm.X86_64.Short.finKsA true)) s t s' ∧
      abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := FastOpen.openFinW_wp (FastOpen.openSel_ok hF v B finKsA_ksOk (longOk_openLong v B)) hs
  exact ⟨t, s', he, abiPreserved_of_exec (openFinP_mx v B) he hg, hp⟩

end

end VG.Proof.AesGcm.X86_64.Short

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

namespace GcmImpl

/-- `vg_aes_gcm_seal_prepared`'s code calling `c`: `sealCode`, with the short
path's table of powers from the prepared key context, and the path for TLS
records (`FastSeal.sel`) when the short path does not apply, or, ending
without calls, before `SealFin.mid`, at every length (`any`), since there
it is faster than `SealFin.mid` at every length. -/
def sealCodeP (v : GcmImpl) (c : Callees) : Prog isa :=
  if v.short then
    Impl.AesGcm.X86_64.Short.«seal» c Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel c (Impl.AesGcm.X86_64.Short.sealLong c))
  else if v.fin then
    Impl.AesGcm.X86_64.SealFin.«seal» c
      (Impl.AesGcm.X86_64.FastSeal.sel c (Impl.AesGcm.X86_64.SealFin.mid c) Impl.AesGcm.X86_64.Short.finKsA true)
  else «seal» c

/-- `vg_aes_gcm_open_prepared`'s code calling `c`: `openCode`, with the short
path's table of powers from the prepared key context, and the path for TLS
records (`FastOpen.sel`) when the short path does not apply; without the
short path, at every length (`any`), since it is faster there than the other
instances' body at every length. -/
def openCodeP (v : GcmImpl) (c : Callees) : Prog isa :=
  if v.short then
    Impl.AesGcm.X86_64.Short.«open» c Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel c (Impl.AesGcm.X86_64.Short.openLong c)) Impl.AesGcm.X86_64.Short.ghashP
  else
    Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel c (Impl.AesGcm.X86_64.Short.openLong c) Impl.AesGcm.X86_64.Short.finKsA true)

end GcmImpl

variable (v : GcmImpl)

theorem sealCodeP_spSafe {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCodeP (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.sealCodeP; split
  · exact Short.sealMP_spSafe v B
  · split
    · exact Short.sealFinP_spSafe v B
    · exact sealM_spSafe v B

theorem openCodeP_spSafe {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.openCodeP (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.openCodeP; split
  · exact Short.openMP_spSafe v B
  · exact Short.openFinP_spSafe v B

end VG.Proof.AesGcm.X86_64

end

end

/-! # Prepared contexts: the short path with the context's powers

`vg_aes_gcm_seal_prepared` and `vg_aes_gcm_open_prepared` take the short
path with its table of powers copied from the prepared key context
(`GcmImpl.sealCodeP`, `GcmImpl.openCodeP`), and otherwise the code of the
other instances, which `seal` and `open` replace for TLS records with
`FastSeal.sel` and `FastOpen.sel`. -/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
variable (v : GcmImpl) (B : BlkFn CtxMode.prepared)

theorem sealSelPrepared_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCodeP (v.withBlk B)))
      (Proof.AesGcm.sealPreparedRoundsContract X86_64.abi 2624) := by
  unfold GcmImpl.sealCodeP; split
  · exact sealPreparedCode_framed (sealPreparedCode_verified (Short.sealMP_correct v B hF)
      (Short.sealMW_ct hF v B Short.powOk_powersP Short.powersP_ct
        (FastSeal.sealSel_ok hF v B Short.finKs_ksOk (Short.sealLongOk_sealLong hF v B))
        (FastSeal.sealSel_rel hF v B Short.finKs_ksOk Short.finKs_rel (Short.sealLongRel_sealLong hF v B)))) (Short.sealMP_spSafe v B)
      (Short.sealMP_xdepth v B)
  · split
    · exact sealPreparedCode_framed (sealPreparedCode_verified (Short.sealFinP_correct v B hF)
        (SealFin.sealFMW_ct v B (FastSeal.sealSel_ok hF v B Short.finKsA_ksOk (SealFin.sealLongOk_mid v B hF))
          (FastSeal.sealSel_rel hF v B Short.finKsA_ksOk Short.finKsA_rel (SealFin.sealLongRel_mid v B hF))))
        (Short.sealFinP_spSafe v B) (Short.sealFinP_xdepth v B)
    · exact sealPrepared_framed v B

/-- `vg_aes_gcm_open_prepared`, with the short path if `v` has it. -/
theorem openSelPrepared_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCodeP (v.withBlk B)))
      (Proof.AesGcm.openPreparedRoundsContract X86_64.abi 2632) := by
  unfold GcmImpl.openCodeP; split
  · exact openPreparedCode_framed (openPreparedCode_verified (Short.openMP_correct v B hF)
      (Short.openMW_ct hF v B Short.powOk_powersP Short.powersP_ct
        (FastOpen.openSel_rel hF v B Short.finKs_ksOk Short.finKs_rel (Short.longRel_openLong v B)))) (Short.openMP_spSafe v B)
      (Short.openMP_xdepth v B)
  · exact openPreparedCode_framed (openPreparedCode_verified (Short.openFinP_correct v B hF)
      (FastOpen.openFinW_ct (FastOpen.openSel_rel hF v B Short.finKsA_ksOk Short.finKsA_rel
        (Short.longRel_openLong v B)))) (Short.openFinP_spSafe v B) (Short.openFinP_xdepth v B)

end VG.Proof.AesGcm.X86_64
