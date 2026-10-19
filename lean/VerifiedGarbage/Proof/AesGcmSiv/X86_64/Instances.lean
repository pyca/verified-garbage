module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Verified
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.SealCT
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.AdjoinRoot
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-!
# AES-GCM-SIV on x86-64: the code a variant's artifacts run

Untrusted: everything here is checked by Lean. As `Verified.lean` for
`Impl.AesGcmSiv.X86_64.«open»` and `«seal»`, for
`Impl.AesGcmSiv.X86_64Stitch.«open»` and `«seal»`, which interleave counter
mode and POLYVAL: correctness (`openS_wp`, `sealS_wp`), constant time
(`openS_rel`, `sealS_rel`), their contracts with the working space as their
last argument, and in a frame that allocates it. Then the code of `seal` and
`open` for the implementations a variant names (`sealCode`, `openCode`, the
interleaved code where the variant has VAES and VPCLMULQDQ), with its proofs,
for `Generic/AesGcm/X86_64/AesGcmSiv.lean`.
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

theorem openS_mx : (X86_64Stitch.«open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases wide <;> simp only [X86_64Stitch.«open», X86_64Stitch.stitched, X86_64Stitch.cryptRest, X86_64Stitch.rest, X86_64Stitch.dec, X86_64Stitch.setup, X86_64Stitch.setupG, X86_64Stitch.setupC, X86_64Stitch.first, X86_64Stitch.batch, X86_64Stitch.body, X86_64Stitch.gA, X86_64Stitch.gB, X86_64Stitch.gq, X86_64Stitch.ghLoad, X86_64Stitch.ldR, X86_64Stitch.lastG, X86_64Stitch.storeCtr, X86_64Stitch.storeY, X86_64Stitch.ctrsR,  revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, entry, keys, derive, deriveBlock, expand, hkey, polyval, polyvalLong, polyvalOne, stage, stageTail, lensAt, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, tagIn, tagOut, recv, crypt, cryptChunk, ctrGen, ecbArgs, ksXor, callEcb, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.allInstrs, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, eb.encMxcsr, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem openS_spSafe : (X86_64Stitch.«open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases wide <;> simp only [X86_64Stitch.«open», X86_64Stitch.stitched, X86_64Stitch.cryptRest, X86_64Stitch.rest, X86_64Stitch.dec, X86_64Stitch.setup, X86_64Stitch.setupG, X86_64Stitch.setupC, X86_64Stitch.first, X86_64Stitch.batch, X86_64Stitch.body, X86_64Stitch.gA, X86_64Stitch.gB, X86_64Stitch.gq, X86_64Stitch.ghLoad, X86_64Stitch.ldR, X86_64Stitch.lastG, X86_64Stitch.storeCtr, X86_64Stitch.storeY, X86_64Stitch.ctrsR,  revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, entry, keys, derive, deriveBlock, expand, hkey, polyval, polyvalLong, polyvalOne, stage, stageTail, lensAt, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, tagIn, tagOut, recv, crypt, cryptChunk, ctrGen, ecbArgs, ksXor, callEcb, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.all, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, eb.encSpSafe, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem openS_correct (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa (X86_64Stitch.«open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := openS_wp v eb wide GcmSiv.Polyval.polyvalFrom_eq hs
  exact ⟨t, s', he, abiPreserved_of_exec (openS_mx v eb wide) he hg, hp⟩

theorem openS_ct : ConstantTime isa openX86_64.pre openX86_64.pub (X86_64Stitch.«open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (openS_rel v eb wide h₁ h₂ hq.1 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end

theorem openS_verified (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) :
    Verified X86_64.target (X86_64Stitch.«open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) (Proof.AesGcmSiv.openScratchContract X86_64.abi 477 8) :=
  Verified.of_correct (openS_correct v eb wide) (openS_ct v eb wide)
    { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
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
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] at h
        sig_simp [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [] at h
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        sig_simp [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [openSat, sealSat] using openSat }

variable (v : GcmImpl) (eb : BlocksImpl) (wide : Bool)

theorem openS_xdepth : (X86_64Stitch.«open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).x86_64Depth ≤ 8 := by
  cases wide <;> simp only [X86_64Stitch.«open», X86_64Stitch.stitched, X86_64Stitch.cryptRest, X86_64Stitch.rest, X86_64Stitch.dec, X86_64Stitch.setup, X86_64Stitch.setupG, X86_64Stitch.setupC, X86_64Stitch.first, X86_64Stitch.batch, X86_64Stitch.body, X86_64Stitch.gA, X86_64Stitch.gB, X86_64Stitch.gq, X86_64Stitch.ghLoad, X86_64Stitch.ldR, X86_64Stitch.lastG, X86_64Stitch.storeCtr, X86_64Stitch.storeY, X86_64Stitch.ctrsR,  revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, keys, derive, expand, polyval, polyvalLong, polyvalOne, stage, stageTail, absorb, absorbChunk, absorbTail, lens, tag, crypt, cryptChunk,
    ctrGen, ecbArgs, ksXor, callEcb, cryptTail, callCtr, callKey, callGh, Code.x86_64Depth, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, eb.encNoStack] <;>
  decide +kernel

theorem openS_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (X86_64Stitch.«open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide))
      (Spec.GcmSiv.openContract X86_64.abi 3856) :=
  X86_64.Verified.stackArgScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 477) (pre := Spec.GcmSiv.openPre X86_64.abi.ptrBits)
    (post := Spec.GcmSiv.openPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.GcmSiv.openLeak X86_64.abi.ptrBits)) (bytes := 3848)
    (Proof.AesGcmSiv.Verified.of_openScratch (openS_verified v eb wide))
    (by decide) (by decide) (by decide) (openS_spSafe v eb wide) (openS_xdepth v eb wide) (openPre_local _)
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

theorem sealS_mx : (X86_64Stitch.«seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases wide <;> simp only [X86_64Stitch.«seal», X86_64Stitch.hashS, X86_64Stitch.cryptS, X86_64Stitch.hash, X86_64Stitch.ctr, X86_64Stitch.setupK, X86_64Stitch.cbody, X86_64Stitch.hbody, X86_64Stitch.loadY, X86_64Stitch.lenCmp, X86_64Stitch.groups, X86_64Stitch.cryptRest, X86_64Stitch.rest, X86_64Stitch.setupG, X86_64Stitch.batch, X86_64Stitch.ghLoad, X86_64Stitch.ldR, X86_64Stitch.lastG, X86_64Stitch.storeCtr, X86_64Stitch.storeY, X86_64Stitch.ctrsR,  revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, entry, keys, derive, deriveBlock, expand, hkey, polyval, polyvalLong, polyvalOne, stage, stageTail, lensAt, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, tagIn, tagOut, recv, crypt, cryptChunk, ctrGen, ecbArgs, ksXor, callEcb, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.allInstrs, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, eb.encMxcsr, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem sealS_spSafe : (X86_64Stitch.«seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases wide <;> simp only [X86_64Stitch.«seal», X86_64Stitch.hashS, X86_64Stitch.cryptS, X86_64Stitch.hash, X86_64Stitch.ctr, X86_64Stitch.setupK, X86_64Stitch.cbody, X86_64Stitch.hbody, X86_64Stitch.loadY, X86_64Stitch.lenCmp, X86_64Stitch.groups, X86_64Stitch.cryptRest, X86_64Stitch.rest, X86_64Stitch.setupG, X86_64Stitch.batch, X86_64Stitch.ghLoad, X86_64Stitch.ldR, X86_64Stitch.lastG, X86_64Stitch.storeCtr, X86_64Stitch.storeY, X86_64Stitch.ctrsR,  revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, entry, keys, derive, deriveBlock, expand, hkey, polyval, polyvalLong, polyvalOne, stage, stageTail, lensAt, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, tagIn, tagOut, recv, crypt, cryptChunk, ctrGen, ecbArgs, ksXor, callEcb, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.all, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, eb.encSpSafe, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem sealS_correct (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa (X86_64Stitch.«seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealS_wp v eb wide GcmSiv.Polyval.polyvalFrom_eq hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealS_mx v eb wide) he hg, hp⟩

theorem sealS_ct : ConstantTime isa sealX86_64.pre sealX86_64.pub (X86_64Stitch.«seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (sealS_rel v eb wide h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end

theorem sealS_verified (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) :
    Verified X86_64.target (X86_64Stitch.«seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) (Proof.AesGcmSiv.sealScratchContract X86_64.abi 477 8) :=
  Verified.of_correct (sealS_correct v eb wide) (sealS_ct v eb wide) (by
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Spec.GcmSiv.sealPost, Proof.AesGcmSiv.sealX86_64, Proof.AesGcmSiv.sealPre, Proof.AesGcmSiv.oneLay,
      Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args, Proof.AesGcmSiv.stk8,
      Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [sealSat] using sealSat)

variable (v : GcmImpl) (eb : BlocksImpl) (wide : Bool)

theorem sealS_xdepth : (X86_64Stitch.«seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).x86_64Depth ≤ 8 := by
  cases wide <;> simp only [X86_64Stitch.«seal», X86_64Stitch.hashS, X86_64Stitch.cryptS, X86_64Stitch.hash, X86_64Stitch.ctr, X86_64Stitch.setupK, X86_64Stitch.cbody, X86_64Stitch.hbody, X86_64Stitch.loadY, X86_64Stitch.lenCmp, X86_64Stitch.groups, X86_64Stitch.cryptRest, X86_64Stitch.rest, X86_64Stitch.setupG, X86_64Stitch.batch, X86_64Stitch.ghLoad, X86_64Stitch.ldR, X86_64Stitch.lastG, X86_64Stitch.storeCtr, X86_64Stitch.storeY, X86_64Stitch.ctrsR,  revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, keys, derive, expand, polyval, polyvalLong, polyvalOne, stage, stageTail, absorb, absorbChunk, absorbTail, lens, tag, crypt, cryptChunk,
    ctrGen, ecbArgs, ksXor, callEcb, cryptTail, callCtr, callKey, callGh, Code.x86_64Depth, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, eb.encNoStack] <;>
  decide +kernel

theorem sealS_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (X86_64Stitch.«seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide))
      (Spec.GcmSiv.sealContract X86_64.abi 3856) :=
  X86_64.Verified.stackArgScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 477) (pre := Spec.GcmSiv.sealPre X86_64.abi.ptrBits)
    (post := Spec.GcmSiv.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3848) (sealS_verified v eb wide) (by decide) (by decide) (by decide)
    (sealS_spSafe v eb wide) (sealS_xdepth v eb wide) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

end

/-! ## The code a variant runs -/

open VG.Proof.AesGcm.X86_64 (GcmImpl)

/-- The implementation of `vg_aes_encrypt_blocks` they call. -/
def ecbFn (v : GcmImpl) : Impl.AesGcm.X86_64.Fn := ⟨(ecbOf v).enc.name, (ecbOf v).enc.code⟩

/-- Whether `open` interleaves counter mode and POLYVAL: with VAES and
VPCLMULQDQ (and so AVX2) in `v`'s callees. -/
def sivStitch (v : GcmImpl) : Bool := v.ctr.features.contains "vaes" && v.gh.features.contains "vpclmulqdq"

/-- The code of `open` for `v`. -/
def openCode (v : GcmImpl) : Prog X86_64.isa :=
  if sivStitch v then Impl.AesGcmSiv.X86_64Stitch.«open» v.callees (ecbFn v) (sivWide v)
  else Impl.AesGcmSiv.X86_64.«open» v.callees (ecbFn v) (sivWide v)

/-- The code of `seal` for `v`. -/
def sealCode (v : GcmImpl) : Prog X86_64.isa :=
  if sivStitch v then Impl.AesGcmSiv.X86_64Stitch.«seal» v.callees (ecbFn v) (sivWide v)
  else Impl.AesGcmSiv.X86_64.«seal» v.callees (ecbFn v) (sivWide v)

theorem sealCode_framed (v : GcmImpl) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (sealCode v))
      (Spec.GcmSiv.sealContract X86_64.abi 3856) := by
  unfold sealCode; split
  · exact sealS_framed v (ecbOf v) (sivWide v)
  · exact seal_framed v (ecbOf v) (sivWide v)

theorem sealCode_spSafe (v : GcmImpl) : (sealCode v).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold sealCode; split
  · exact sealS_spSafe v (ecbOf v) (sivWide v)
  · exact seal_spSafe v (ecbOf v) (sivWide v)

theorem openCode_framed (v : GcmImpl) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (openCode v))
      (Spec.GcmSiv.openContract X86_64.abi 3856) := by
  unfold openCode; split
  · exact openS_framed v (ecbOf v) (sivWide v)
  · exact open_framed v (ecbOf v) (sivWide v)

theorem openCode_spSafe (v : GcmImpl) : (openCode v).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold openCode; split
  · exact openS_spSafe v (ecbOf v) (sivWide v)
  · exact open_spSafe v (ecbOf v) (sivWide v)

end VG.Proof.AesGcmSiv.X86_64
