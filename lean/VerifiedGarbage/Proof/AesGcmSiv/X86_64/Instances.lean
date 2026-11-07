module

public import VerifiedGarbage.Proof.AesGcmSiv.Rounds
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Verified
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.SealCT
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.VaesLoops
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.StitchAvx
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.AdjoinRoot
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem

/-!
# AES-GCM-SIV on x86-64: the code a variant's artifacts run

Untrusted: everything here is checked by Lean. As `Verified.lean` for
`Impl.AesGcmSiv.X86_64.«open»` and `«seal»`, for
`Impl.AesGcmSiv.X86_64Stitch.«open»` and `«seal»`, which interleave counter
mode and POLYVAL: correctness (`openS_wp`, `sealS_wp`), constant time
(`openS_rel`, `sealS_rel`), their contracts with the working space as their
last argument, and in a frame that allocates it, for any loops on the groups
that meet `Stitch.LoopsOk` and `Stitch.LoopsCode`. Then the code of `seal` and
`open` for the implementations a variant names (`sealCode`, `openCode`, the
interleaved code where the variant has VAES and VPCLMULQDQ, or AES-NI,
PCLMULQDQ and AVX, `loopsOf`), with its proofs, for
`Generic/AesGcm/X86_64/AesGcmSiv.lean`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

/-! ## `open` with the interleaved loop -/

section

open VG VG.X86_64 VG.Impl.AesGcmSiv.X86_64 VG.Impl.AesGcmSiv
open VG.Impl.Gcm.X86_64.Stitch (aregs storesK pregs ordE)
open VG.Impl.Gcm.X86_64.Vpclmul (powers powers16 zero acc reduce combine)
open VG.Impl.Aes.X86_64.Vaes (aesK xorDataK)
open VG.Proof.AesGcm.X86_64 (GcmImpl)
open VG.Proof.Aes.X86_64 (BlocksImpl)

section
variable (v : GcmImpl) (eb : BlocksImpl) (wide : Bool)

theorem openS_mx {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hcode : Stitch.LoopsCode lp) : (X86_64Stitch.«open» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases wide <;> simp only [X86_64Stitch.«open», X86_64Stitch.stitched, X86_64Stitch.cryptRest, X86_64Stitch.rest, X86_64Stitch.dec, X86_64Stitch.setup, X86_64Stitch.setupG, X86_64Stitch.setupC, X86_64Stitch.first, X86_64Stitch.batch, X86_64Stitch.body, X86_64Stitch.gA, X86_64Stitch.gB, X86_64Stitch.gq, X86_64Stitch.ghLoad, X86_64Stitch.ldR, X86_64Stitch.lastG, X86_64Stitch.storeCtr, X86_64Stitch.storeY, X86_64Stitch.ctrsR,  revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, entry, keys, keysS, derive, deriveBlock, expand, hkey, polyval, polyvalLong, polyvalOne, stage, stageTail, lensAt, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, tagIn, tagOut, recv, crypt, cryptChunk, ctrGen, ecbArgs, ksXor, callEcb, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.allInstrs, hcode.decMx, hcode.hashMx, hcode.ctrMx, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, eb.encMxcsr, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem openS_spSafe {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hcode : Stitch.LoopsCode lp) : (X86_64Stitch.«open» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases wide <;> simp only [X86_64Stitch.«open», X86_64Stitch.stitched, X86_64Stitch.cryptRest, X86_64Stitch.rest, X86_64Stitch.dec, X86_64Stitch.setup, X86_64Stitch.setupG, X86_64Stitch.setupC, X86_64Stitch.first, X86_64Stitch.batch, X86_64Stitch.body, X86_64Stitch.gA, X86_64Stitch.gB, X86_64Stitch.gq, X86_64Stitch.ghLoad, X86_64Stitch.ldR, X86_64Stitch.lastG, X86_64Stitch.storeCtr, X86_64Stitch.storeY, X86_64Stitch.ctrsR,  revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, entry, keys, keysS, derive, deriveBlock, expand, hkey, polyval, polyvalLong, polyvalOne, stage, stageTail, lensAt, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, tagIn, tagOut, recv, crypt, cryptChunk, ctrGen, ecbArgs, ksXor, callEcb, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.all, hcode.decSp, hcode.hashSp, hcode.ctrSp, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, eb.encSpSafe, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem openS_correct {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp) (hcode : Stitch.LoopsCode lp) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa (X86_64Stitch.«open» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := openS_wp hlp v eb wide GcmSiv.Polyval.polyvalFrom_eq hs
  exact ⟨t, s', he, abiPreserved_of_exec (openS_mx v eb wide hcode) he hg, hp⟩

theorem openS_ct {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp) : ConstantTime isa openX86_64.pre openX86_64.pub (X86_64Stitch.«open» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (openS_rel hlp v eb wide h₁ h₂ hq.1 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end

theorem openS_verified (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp)
    (hcode : Stitch.LoopsCode lp) :
    Verified X86_64.target (X86_64Stitch.«open» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) (Proof.AesGcmSiv.openScratchContract X86_64.abi 477 8) :=
  Verified.of_correct (openS_correct v eb wide hlp hcode) (openS_ct v eb wide hlp)
    { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      -- `h` and the goal match on the same outcome of `decryptWith` with
      -- different matchers (`openPost`'s and `openPost`'s of the contract):
      -- split on it rather than have `exact h` unfold both to unify them.
      post := by
        intro s s' hs h
        sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] at h
        sig_simp [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [] at h
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        sig_simp [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [openSat, sealSat] using openSat }

variable (v : GcmImpl) (eb : BlocksImpl) (wide : Bool)

theorem openS_xdepth {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hcode : Stitch.LoopsCode lp) : (X86_64Stitch.«open» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).x86_64Depth ≤ 8 := by
  cases wide <;> simp only [X86_64Stitch.«open», X86_64Stitch.stitched, X86_64Stitch.cryptRest, X86_64Stitch.rest, X86_64Stitch.dec, X86_64Stitch.setup, X86_64Stitch.setupG, X86_64Stitch.setupC, X86_64Stitch.first, X86_64Stitch.batch, X86_64Stitch.body, X86_64Stitch.gA, X86_64Stitch.gB, X86_64Stitch.gq, X86_64Stitch.ghLoad, X86_64Stitch.ldR, X86_64Stitch.lastG, X86_64Stitch.storeCtr, X86_64Stitch.storeY, X86_64Stitch.ctrsR,  revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, keys, keysS, derive, expand, polyval, polyvalLong, polyvalOne, stage, stageTail, absorb, absorbChunk, absorbTail, lens, tag, crypt, cryptChunk,
    ctrGen, ecbArgs, ksXor, callEcb, cryptTail, callCtr, callKey, callGh, Code.x86_64Depth, hcode.decDepth, hcode.hashDepth, hcode.ctrDepth, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, eb.encNoStack] <;>
  decide +kernel

theorem openS_framed {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp) (hcode : Stitch.LoopsCode lp) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (X86_64Stitch.«open» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide))
      (Proof.AesGcmSiv.openRoundsContract X86_64.abi 3856) :=
  X86_64.Verified.stackArgScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 477) (pre := Spec.GcmSiv.openPre X86_64.abi.ptrBits)
    (post := Proof.AesGcmSiv.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.GcmSiv.openLeak X86_64.abi.ptrBits)) (bytes := 3848)
    (Proof.AesGcmSiv.Verified.of_openScratch (openS_verified v eb wide hlp hcode))
    (by decide) (by decide) (by decide) (openS_spSafe v eb wide hcode) (openS_xdepth v eb wide hcode) (openPre_local _)
    (openPost_local _) openFrameSat_pre (hleak := openLeak_local _)

end

/-! ## `seal` with the interleaved loop -/

section

open VG VG.X86_64 VG.Impl.AesGcmSiv.X86_64 VG.Impl.AesGcmSiv
open VG.Impl.Gcm.X86_64.Stitch (aregs storesK pregs ordE)
open VG.Impl.Gcm.X86_64.Vpclmul (powers powers16 zero acc reduce combine)
open VG.Impl.Aes.X86_64.Vaes (aesK xorDataK)
open VG.Proof.AesGcm.X86_64 (GcmImpl)
open VG.Proof.Aes.X86_64 (BlocksImpl)

section
variable (v : GcmImpl) (eb : BlocksImpl) (wide : Bool)

theorem sealS_mx {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hcode : Stitch.LoopsCode lp) : (X86_64Stitch.«seal» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases wide <;> simp only [X86_64Stitch.«seal», X86_64Stitch.hashS, X86_64Stitch.cryptS, X86_64Stitch.hash, X86_64Stitch.ctr, X86_64Stitch.setupK, X86_64Stitch.cbody, X86_64Stitch.hbody, X86_64Stitch.loadY, X86_64Stitch.lenCmp, X86_64Stitch.groups, X86_64Stitch.cryptRest, X86_64Stitch.rest, X86_64Stitch.setupG, X86_64Stitch.batch, X86_64Stitch.ghLoad, X86_64Stitch.ldR, X86_64Stitch.lastG, X86_64Stitch.storeCtr, X86_64Stitch.storeY, X86_64Stitch.ctrsR,  revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, entry, keys, keysS, derive, deriveBlock, expand, hkey, polyval, polyvalLong, polyvalOne, stage, stageTail, lensAt, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, tagIn, tagOut, recv, crypt, cryptChunk, ctrGen, ecbArgs, ksXor, callEcb, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.allInstrs, hcode.decMx, hcode.hashMx, hcode.ctrMx, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, eb.encMxcsr, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem sealS_spSafe {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hcode : Stitch.LoopsCode lp) : (X86_64Stitch.«seal» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases wide <;> simp only [X86_64Stitch.«seal», X86_64Stitch.hashS, X86_64Stitch.cryptS, X86_64Stitch.hash, X86_64Stitch.ctr, X86_64Stitch.setupK, X86_64Stitch.cbody, X86_64Stitch.hbody, X86_64Stitch.loadY, X86_64Stitch.lenCmp, X86_64Stitch.groups, X86_64Stitch.cryptRest, X86_64Stitch.rest, X86_64Stitch.setupG, X86_64Stitch.batch, X86_64Stitch.ghLoad, X86_64Stitch.ldR, X86_64Stitch.lastG, X86_64Stitch.storeCtr, X86_64Stitch.storeY, X86_64Stitch.ctrsR,  revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, entry, keys, keysS, derive, deriveBlock, expand, hkey, polyval, polyvalLong, polyvalOne, stage, stageTail, lensAt, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, tagIn, tagOut, recv, crypt, cryptChunk, ctrGen, ecbArgs, ksXor, callEcb, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.all, hcode.decSp, hcode.hashSp, hcode.ctrSp, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, eb.encSpSafe, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem sealS_correct {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp) (hcode : Stitch.LoopsCode lp) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa (X86_64Stitch.«seal» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealS_wp hlp v eb wide GcmSiv.Polyval.polyvalFrom_eq hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealS_mx v eb wide hcode) he hg, hp⟩

theorem sealS_ct {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp) : ConstantTime isa sealX86_64.pre sealX86_64.pub (X86_64Stitch.«seal» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (sealS_rel hlp v eb wide h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end

theorem sealS_verified (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp)
    (hcode : Stitch.LoopsCode lp) :
    Verified X86_64.target (X86_64Stitch.«seal» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) (Proof.AesGcmSiv.sealScratchContract X86_64.abi 477 8) :=
  Verified.of_correct (sealS_correct v eb wide hlp hcode) (sealS_ct v eb wide hlp) (by
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Proof.AesGcmSiv.sealRoundsPost, Proof.AesGcmSiv.sealX86_64, Proof.AesGcmSiv.sealPre, Proof.AesGcmSiv.oneLay,
      Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args, Proof.AesGcmSiv.stk8,
      Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [sealSat] using sealSat)

variable (v : GcmImpl) (eb : BlocksImpl) (wide : Bool)

theorem sealS_xdepth {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hcode : Stitch.LoopsCode lp) : (X86_64Stitch.«seal» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).x86_64Depth ≤ 8 := by
  cases wide <;> simp only [X86_64Stitch.«seal», X86_64Stitch.hashS, X86_64Stitch.cryptS, X86_64Stitch.hash, X86_64Stitch.ctr, X86_64Stitch.setupK, X86_64Stitch.cbody, X86_64Stitch.hbody, X86_64Stitch.loadY, X86_64Stitch.lenCmp, X86_64Stitch.groups, X86_64Stitch.cryptRest, X86_64Stitch.rest, X86_64Stitch.setupG, X86_64Stitch.batch, X86_64Stitch.ghLoad, X86_64Stitch.ldR, X86_64Stitch.lastG, X86_64Stitch.storeCtr, X86_64Stitch.storeY, X86_64Stitch.ctrsR,  revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, keys, keysS, derive, expand, polyval, polyvalLong, polyvalOne, stage, stageTail, absorb, absorbChunk, absorbTail, lens, tag, crypt, cryptChunk,
    ctrGen, ecbArgs, ksXor, callEcb, cryptTail, callCtr, callKey, callGh, Code.x86_64Depth, hcode.decDepth, hcode.hashDepth, hcode.ctrDepth, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, eb.encNoStack] <;>
  decide +kernel

theorem sealS_framed {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp) (hcode : Stitch.LoopsCode lp) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (X86_64Stitch.«seal» lp v.callees ⟨eb.enc.name, eb.enc.code⟩ wide))
      (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 3856) :=
  X86_64.Verified.stackArgScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 477) (pre := Spec.GcmSiv.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesGcmSiv.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3848) (sealS_verified v eb wide hlp hcode) (by decide) (by decide) (by decide)
    (sealS_spSafe v eb wide hcode) (sealS_xdepth v eb wide hcode) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

end

/-! ## The code a variant runs -/

open VG.Proof.AesGcm.X86_64 (GcmImpl)

/-- The implementation of `vg_aes_encrypt_blocks` they call. -/
def ecbFn (v : GcmImpl) : Impl.AesGcm.X86_64.Fn := ⟨(ecbOf v).enc.name, (ecbOf v).enc.code⟩

/-- Whether `open` interleaves counter mode and POLYVAL on 256-bit registers:
with VAES and VPCLMULQDQ (and so AVX2) in `v`'s callees. -/
def sivStitch (v : GcmImpl) : Bool := v.ctr.features.contains "vaes" && v.gh.features.contains "vpclmulqdq"

/-- Whether `open` interleaves them on 128-bit registers
(`Impl.AesGcmSiv.X86_64StitchAvx`): without that, with AES-NI and PCLMULQDQ
in `v`'s callees, and AVX in AES-GCM's interleaved loops. -/
def sivAvx (v : GcmImpl) : Bool :=
  !sivStitch v && v.ctr.features.contains "aes" && v.gh.features.contains "pclmulqdq" &&
    v.stitch.any (·.features.contains "avx")

/-- The loops on the groups, if `open` and `seal` interleave. -/
def loopsOf (v : GcmImpl) : Option Impl.AesGcmSiv.X86_64Stitch.Loops :=
  if sivStitch v then some Impl.AesGcmSiv.X86_64Stitch.vaesLoops
  else if sivAvx v then some Impl.AesGcmSiv.X86_64StitchAvx.loops else none

theorem loopsOf_ok (v : GcmImpl) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (h : loopsOf v = some lp) :
    Stitch.LoopsOk lp ∧ Stitch.LoopsCode lp := by
  unfold loopsOf at h
  split at h
  · cases h; exact ⟨Stitch.vaesLoops_ok, Stitch.vaesLoops_code⟩
  · split at h
    · cases h; exact ⟨StitchAvx.loops_ok, StitchAvx.loops_code⟩
    · cases h

/-- The CPU features of `seal` and `open`: AVX too with the 128-bit loops. -/
def sivFeatures (v : GcmImpl) : List String := if sivAvx v then (features v ++ ["avx"]).dedup else features v

/-- `seal` and `open` with the loops `lp`, if any, for `v`'s callees. -/
def sealWith (v : GcmImpl) (wide : Bool) : Option Impl.AesGcmSiv.X86_64Stitch.Loops → Prog X86_64.isa
  | some lp => Impl.AesGcmSiv.X86_64Stitch.«seal» lp v.callees (ecbFn v) wide
  | none => Impl.AesGcmSiv.X86_64.«seal» v.callees (ecbFn v) wide

def openWith (v : GcmImpl) (wide : Bool) : Option Impl.AesGcmSiv.X86_64Stitch.Loops → Prog X86_64.isa
  | some lp => Impl.AesGcmSiv.X86_64Stitch.«open» lp v.callees (ecbFn v) wide
  | none => Impl.AesGcmSiv.X86_64.«open» v.callees (ecbFn v) wide

theorem sealWith_framed (v : GcmImpl) (wide : Bool) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (sealWith v wide (loopsOf v)))
      (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 3856) := by
  cases h : loopsOf v with
  | some lp => exact sealS_framed v (ecbOf v) wide (loopsOf_ok v h).1 (loopsOf_ok v h).2
  | none => exact seal_framed v (ecbOf v) wide

theorem sealWith_spSafe (v : GcmImpl) (wide : Bool) :
    (sealWith v wide (loopsOf v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases h : loopsOf v with
  | some lp => exact sealS_spSafe v (ecbOf v) wide (loopsOf_ok v h).2
  | none => exact seal_spSafe v (ecbOf v) wide

theorem openWith_framed (v : GcmImpl) (wide : Bool) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (openWith v wide (loopsOf v)))
      (Proof.AesGcmSiv.openRoundsContract X86_64.abi 3856) := by
  cases h : loopsOf v with
  | some lp => exact openS_framed v (ecbOf v) wide (loopsOf_ok v h).1 (loopsOf_ok v h).2
  | none => exact open_framed v (ecbOf v) wide

theorem openWith_spSafe (v : GcmImpl) (wide : Bool) :
    (openWith v wide (loopsOf v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases h : loopsOf v with
  | some lp => exact openS_spSafe v (ecbOf v) wide (loopsOf_ok v h).2
  | none => exact open_spSafe v (ecbOf v) wide

/-- The code of `open` for `v`. -/
def openCode (v : GcmImpl) : Prog X86_64.isa := openWith v (sivWide v) (loopsOf v)

/-- The code of `seal` for `v`. -/
def sealCode (v : GcmImpl) : Prog X86_64.isa := sealWith v (sivWide v) (loopsOf v)

theorem sealCode_framed (v : GcmImpl) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (sealCode v))
      (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 3856) := sealWith_framed v _

theorem sealCode_spSafe (v : GcmImpl) : (sealCode v).all (fun i => !X86_64.isa.writesSp i) = true :=
  sealWith_spSafe v _

theorem openCode_framed (v : GcmImpl) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (openCode v))
      (Proof.AesGcmSiv.openRoundsContract X86_64.abi 3856) := openWith_framed v _

theorem openCode_spSafe (v : GcmImpl) : (openCode v).all (fun i => !X86_64.isa.writesSp i) = true :=
  openWith_spSafe v _

/-- Whether `v`'s `seal` and `open` are the code of another variant's: with
VAES and VPCLMULQDQ (`sivStitch`) they run their own interleaved loops, not
`v`'s (`stitch`), so a variant whose loops need CPU features the code does
not is the variant without those loops, under another name. -/
def sivSame (v : GcmImpl) : Bool :=
  sivStitch v && v.stitch.any fun s => s.features.any fun f => !(features v).contains f

/-- Whether `v`'s `seal` and `open` have instances without the AVX2 copies:
not when their code takes those copies already (`sivWide`), whose only
instances are those named for them (`_avx2`). -/
def hasNarrow (v : GcmImpl) : Bool := !sivWide v

/-- Whether `v`'s `seal` and `open` have instances with the AVX2 copies
(`_avx2`), which the CPUs with AVX2 run at every length: not for AES-NI and
PCLMULQDQ without AVX's loops, whose instance would need AVX as well, and so
would run only where the instance with AVX's loops (`sivAvx`), which the
dispatcher prefers, runs. -/
def hasWide (v : GcmImpl) : Bool :=
  sivWide v || sivAvx v || !(v.ctr.features.contains "aes" && v.gh.features.contains "pclmulqdq")

/-- The copy/XOR variant: the code of `seal` and `open` with the AVX2
copies, which those whose callees need AVX2 already take. -/
def wideSealCode (v : GcmImpl) : Prog X86_64.isa := sealWith v true (loopsOf v)

def wideOpenCode (v : GcmImpl) : Prog X86_64.isa := openWith v true (loopsOf v)

theorem wideSeal_framed (v : GcmImpl) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (wideSealCode v))
      (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 3856) := sealWith_framed v true

theorem wideOpen_framed (v : GcmImpl) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (wideOpenCode v))
      (Proof.AesGcmSiv.openRoundsContract X86_64.abi 3856) := openWith_framed v true

theorem wideSeal_spSafe (v : GcmImpl) : (wideSealCode v).all (fun i => !X86_64.isa.writesSp i) = true :=
  sealWith_spSafe v true

theorem wideOpen_spSafe (v : GcmImpl) : (wideOpenCode v).all (fun i => !X86_64.isa.writesSp i) = true :=
  openWith_spSafe v true


/-! ## Choosing by the lengths

`bySize wide narrow` runs `wide`, the code with the AVX2 copies, when the
text (`len`, the first stack argument) or the additional data (`aad_len`,
`r8`) is 128 bytes or more, and `narrow`, which has none of their loop
checks, otherwise: `len ||| aad_len` is at least 128 exactly then. The
comparison writes only `rax` and the flags, which no contract reads
(`Same`), and leaks only the address of `len`; the branch depends only on
`len` and `aad_len`, which are public (`bySize_verified`). -/

section

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.AesGcm.X86_64 (at_)

/-- Clears the carry flag exactly when `len ||| aad_len` is 128 or more. -/
def cmpLens : List Instr :=
  [.mov .rax (.mem (at_ .rsp 8)), .alu .or .rax (.reg .r8), .alu .cmp .rax (.imm 128)]

/-- `wide` when the text or the additional data is 128 bytes or more, and
`narrow` otherwise. -/
def bySize (wide narrow : Prog isa) : Prog isa :=
  .seq (.block cmpLens) (Code.iteCold .ae wide narrow)

/-- `u` is `s` but for `rax` and the flags. -/
structure Same (s u : State) : Prop where
  gpr : ∀ r, r ≠ .rax → u.gpr r = s.gpr r
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mx : u.mxcsr = s.mxcsr

theorem Same.saa {s u : State} (h : Same s u) (i : Nat) : stackArgAddr u i = stackArgAddr s i := by
  simp only [stackArgAddr, h.gpr .rsp (by decide)]

theorem Same.sa {s u : State} (h : Same s u) (i : Nat) : stackArg u i = stackArg s i := by
  simp only [stackArg, h.saa, h.mem]

theorem Same.saF {s u : State} (h : Same s u) : stackArg u = stackArg s := funext h.sa

theorem Same.saaF {s u : State} (h : Same s u) : stackArgAddr u = stackArgAddr s := funext h.saa

theorem Same.abi {s u s' : State} (h : Same s u) (a : abiPreserved u s') : abiPreserved s s' :=
  ⟨fun r hr => by rw [a.1 r hr, h.gpr r (by rintro rfl; simp [calleeSaved] at hr)],
    by rw [← h.gpr .rsp (by decide), a.2.1, h.mem], by rw [a.2.2, h.mx]⟩

/-- The comparison. -/
theorem cmpLens_run (s : State) (hin : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) :
    ∃ u, execBlock isa cmpLens s = some (u, [.addr (stackArgAddr s 0)]) ∧ Same s u ∧
      eval .ae u = some (decide (128 ≤ (stackArg s 0 ||| s.gpr .r8).toNat)) := by
  have ea : s.ea (at_ .rsp 8) = stackArgAddr s 0 := rfl
  refine ⟨?u, ?h1, ⟨?h2, ?h3, ?h4, ?h5, ?h6⟩, ?h7⟩
  case h1 => simp [execBlock, cmpLens, exec, readSrc, ea, hin, addrs, srcAddrs, State.load64, execAlu]; rfl
  case h3 => rfl
  case h4 => rfl
  case h5 => rfl
  case h6 => rfl
  case h2 => intro r hr; simp [gpr_arithFlags, gpr_setReg, hr]
  case h7 =>
    simp only [eval, cf_arithFlags, gpr_setReg, gpr_arithFlags, ↓reduceIte, reduceCtorEq,
      Option.map_some, ← decide_not, Nat.not_lt]
    rfl

/-- `bySize wide narrow` is verified against any contract both are, whose
precondition, postcondition and public data do not read `rax` or the flags,
and which makes `len` and `aad_len` public. -/
theorem bySize_verified {k : Contract isa} {wide narrow : Prog isa}
    (hw : Verified X86_64.target wide k) (hn : Verified X86_64.target narrow k)
    (hin : ∀ s, k.pre s → InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8)
    (hpre : ∀ s u, Same s u → k.pre s → k.pre u)
    (hpost : ∀ s u s', Same s u → k.post u s' → k.post s s')
    (hpub : ∀ s u s' u', Same s u → Same s' u' → k.pub s s' → k.pub u u')
    (hargs : ∀ s s', k.pub s s' →
      stackArg s 0 = stackArg s' 0 ∧ s.gpr .r8 = s'.gpr .r8 ∧ s.gpr .rsp = s'.gpr .rsp) :
    Verified X86_64.target (bySize wide narrow) k := by
  refine Verified.entryBranch (p := fun s => decide (128 ≤ (stackArg s 0 ||| s.gpr .r8).toNat))
    (fun s => [.addr (stackArgAddr s 0)]) hw hn (fun s hs => ?_) ?_ hw.2.2
  · obtain ⟨u, e, hS, ev⟩ := cmpLens_run s (hin s hs)
    exact ⟨u, e, ev, fun _ => ⟨hpre s u hS hs, fun s' a q => ⟨hS.abi a, hpost s u s' hS q⟩⟩,
      fun _ => ⟨hpre s u hS hs, fun s' a q => ⟨hS.abi a, hpost s u s' hS q⟩⟩⟩
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, hS, -⟩ := cmpLens_run s (hin s hs)
    obtain ⟨u₀', e₀', hS', -⟩ := cmpLens_run s' (hin s' hs')
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    obtain ⟨a0, a8, asp⟩ := hargs s s' hq
    exact ⟨by simp only [stackArgAddr, asp], by rw [a0, a8],
      fun _ => hpub s u₀ s' u₀' hS hS' hq, fun _ => hpub s u₀ s' u₀' hS hS' hq⟩


/-- `seal` by the lengths, from its code with and without the AVX2 copies. -/
theorem seal_bySize {wide narrow : Prog isa}
    (hw : Verified X86_64.target wide (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 3856))
    (hn : Verified X86_64.target narrow (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 3856)) :
    Verified X86_64.target (bySize wide narrow) (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 3856) := by
  refine bySize_verified hw hn (fun s hs => ?_) (fun s u h hs => ?_) (fun s u s' h q => ?_)
    (fun s u s' u' h h' q => ?_) (fun s s' q => ?_)
  · sig_pre [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, X86_64.abi,
      X86_64.argRegs] at hs
    obtain ⟨-, -, hrd, -⟩ := hs
    refine ⟨⟨stackArgAddr s 0, 16⟩, List.mem_append_left _ ?_, ?_⟩
    · rw [hrd]; simp
    · simp [Region.Contains]
  · sig_pre [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, X86_64.abi,
      X86_64.argRegs] at hs ⊢
    simp only [h.saF, h.saaF, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
      h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.gpr .rsp (by decide), h.mem,
      h.rd, h.wr]
    exact hs
  · sig_post [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, Proof.AesGcmSiv.sealRoundsPost,
      X86_64.abi, X86_64.argRegs] at q ⊢
    simp only [h.saF, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
      h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.mem] at q
    exact q
  · sig_pub [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, X86_64.abi, X86_64.argRegs] at q ⊢
    simp only [h.saF, h.saaF, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
      h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.gpr .rsp (by decide), h.mem,
      h'.saF, h'.saaF, h'.gpr .rdi (by decide), h'.gpr .rsi (by decide), h'.gpr .rdx (by decide),
      h'.gpr .rcx (by decide), h'.gpr .r8 (by decide), h'.gpr .r9 (by decide), h'.gpr .rsp (by decide),
      h'.mem]
    exact q
  · sig_pub [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, X86_64.abi, X86_64.argRegs] at q
    obtain ⟨hsp, -, -, -, -, h8, -, h6, -⟩ := q
    exact ⟨by simpa [List.getD, List.range, List.range.loop] using h6, h8, hsp⟩


/-- `open` by the lengths, from its code with and without the AVX2 copies. -/
theorem open_bySize {wide narrow : Prog isa}
    (hw : Verified X86_64.target wide (Proof.AesGcmSiv.openRoundsContract X86_64.abi 3856))
    (hn : Verified X86_64.target narrow (Proof.AesGcmSiv.openRoundsContract X86_64.abi 3856)) :
    Verified X86_64.target (bySize wide narrow) (Proof.AesGcmSiv.openRoundsContract X86_64.abi 3856) := by
  refine bySize_verified hw hn (fun s hs => ?_) (fun s u h hs => ?_) (fun s u s' h q => ?_)
    (fun s u s' u' h h' q => ?_) (fun s s' q => ?_)
  · sig_pre [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, X86_64.abi,
      X86_64.argRegs] at hs
    obtain ⟨-, -, hrd, -⟩ := hs
    refine ⟨⟨stackArgAddr s 0, 16⟩, List.mem_append_left _ ?_, ?_⟩
    · rw [hrd]; simp
    · simp [Region.Contains]
  · sig_pre [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, X86_64.abi,
      X86_64.argRegs] at hs ⊢
    simp only [h.saF, h.saaF, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
      h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.gpr .rsp (by decide), h.mem,
      h.rd, h.wr]
    exact hs
  · sig_post [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Proof.AesGcmSiv.openRoundsPost,
      X86_64.abi, X86_64.argRegs] at q ⊢
    simp only [h.saF, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
      h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.mem] at q
    exact q
  · sig_pub [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openLeak, X86_64.abi, X86_64.argRegs] at q ⊢
    simp only [h.saF, h.saaF, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
      h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.gpr .rsp (by decide), h.mem,
      h'.saF, h'.saaF, h'.gpr .rdi (by decide), h'.gpr .rsi (by decide), h'.gpr .rdx (by decide),
      h'.gpr .rcx (by decide), h'.gpr .r8 (by decide), h'.gpr .r9 (by decide), h'.gpr .rsp (by decide),
      h'.mem]
    exact q
  · sig_pub [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openLeak, X86_64.abi, X86_64.argRegs] at q
    obtain ⟨hsp, -, -, -, -, -, h8, -, h6, -⟩ := q
    exact ⟨by simpa [List.getD, List.range, List.range.loop] using h6, h8, hsp⟩


/-- The code of `v`'s `seal` with the AVX2 copies (its `_avx2` instance):
when `v`'s code does not take them already (`sivWide`), by the lengths,
with the code without them below 128 bytes, where the copies are not used. -/
def avx2SealCode (v : GcmImpl) : Prog isa :=
  if sivWide v then Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (wideSealCode v)
  else bySize (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (wideSealCode v))
    (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (sealCode v))

/-- `open`'s, as `avx2SealCode`. -/
def avx2OpenCode (v : GcmImpl) : Prog isa :=
  if sivWide v then Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (wideOpenCode v)
  else bySize (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (wideOpenCode v))
    (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (openCode v))

theorem avx2Seal_verified (v : GcmImpl) :
    Verified X86_64.target (avx2SealCode v) (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 3856) := by
  unfold avx2SealCode
  split
  · exact wideSeal_framed v
  · exact seal_bySize (wideSeal_framed v) (sealCode_framed v)

theorem avx2Open_verified (v : GcmImpl) :
    Verified X86_64.target (avx2OpenCode v) (Proof.AesGcmSiv.openRoundsContract X86_64.abi 3856) := by
  unfold avx2OpenCode
  split
  · exact wideOpen_framed v
  · exact open_bySize (wideOpen_framed v) (openCode_framed v)

theorem avx2Seal_spSafe (v : GcmImpl) : (avx2SealCode v).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold avx2SealCode
  split
  · exact X86_64.withStackArgScratch_spSafe (wideSeal_spSafe v)
  · simp only [bySize, Code.iteCold, Code.all, X86_64.withStackArgScratch_spSafe (wideSeal_spSafe v),
      X86_64.withStackArgScratch_spSafe (sealCode_spSafe v), Bool.and_true]
    rfl

theorem avx2Open_spSafe (v : GcmImpl) : (avx2OpenCode v).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold avx2OpenCode
  split
  · exact X86_64.withStackArgScratch_spSafe (wideOpen_spSafe v)
  · simp only [bySize, Code.iteCold, Code.all, X86_64.withStackArgScratch_spSafe (wideOpen_spSafe v),
      X86_64.withStackArgScratch_spSafe (openCode_spSafe v), Bool.and_true]
    rfl

end

end VG.Proof.AesGcmSiv.X86_64
