module

public import VerifiedGarbage.Proof.AesGcmSiv.Scratch
public import Mathlib.Data.List.Dedup
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64
public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Env
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.SealCT
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.VaesLoops
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.StitchAvx
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Verified
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.AdjoinRoot
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `AesGcmSiv.X86_64.Verified`, which only this module used -/

section

/-!
# AES-GCM-SIV on x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`, and `eb` of `vg_aes_encrypt_blocks`), states satisfying the preconditions, and the shared contracts
of `Spec/GcmSiv/Contract.lean` with the working space as a last argument
(`Proof/AesGcmSiv/Scratch.lean`, 477 words), with 8 bytes of stack: the
return address of a call of one of them, which make no calls. The last section
allocates the working space.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.Impl.AesGcmSiv.X86_64
open VG.Proof.AesGcm.X86_64 (GcmImpl)
open VG.Proof.Aes.X86_64 (BlocksImpl)

/-- The implementation of `vg_aes_encrypt_blocks` that goes with `v`'s
`vg_aes_ctr32`, needing no more CPU features: the baseline one with the
baseline, VAES's with VAES's (which needs `aes`, `avx`, `avx2` and `vaes`,
as it does), and AES-NI's, which needs only `aes`, with every other (each
needs AES-NI; the emitter checks the features of every instance). -/
def ecbOf (v : GcmImpl) : BlocksImpl :=
  if v.ctr.features = [] then .scalar else if v.ctr.features.contains "vaes" then .vaes else .aesni

/-- Whether `seal` and `open` copy and XOR four blocks at a time on 256-bit
registers (`wide`): with the instances whose `vg_aes_ctr32` or `vg_ghash`
needs AVX2, as those loops do. -/
def sivWide (v : GcmImpl) : Bool := (v.ctr.features ++ v.gh.features).contains "avx2"

/-- The CPU features of `seal` and `open`: those of the four functions they
call, and AVX and AVX2 with `sivWide` (which they include already; here, to
keep `List.dedup`'s imports out of the proofs). -/
def features (v : GcmImpl) : List String :=
  (v.ctr.features ++ v.key.features ++ v.gh.features ++ (ecbOf v).features ++
    (if sivWide v then ["avx", "avx2"] else [])).dedup

section
variable (v : GcmImpl) (eb : BlocksImpl) (wide : Bool)

theorem seal_mx : («seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases wide <;> simp only [«seal», «open», revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, entry, keys, keysS, derive, deriveBlock, expand, hkey, polyval, polyvalLong, polyvalOne, stage, stageTail, lensAt, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, tagIn, tagOut, recv, crypt, cryptChunk, ctrGen, ecbArgs, ksXor, callEcb, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.allInstrs, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, eb.encMxcsr, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem open_mx : («open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases wide <;> simp only [«seal», «open», revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, entry, keys, keysS, derive, deriveBlock, expand, hkey, polyval, polyvalLong, polyvalOne, stage, stageTail, lensAt, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, tagIn, tagOut, recv, crypt, cryptChunk, ctrGen, ecbArgs, ksXor, callEcb, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.allInstrs, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, eb.encMxcsr, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem seal_spSafe : («seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases wide <;> simp only [«seal», «open», revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, entry, keys, keysS, derive, deriveBlock, expand, hkey, polyval, polyvalLong, polyvalOne, stage, stageTail, lensAt, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, tagIn, tagOut, recv, crypt, cryptChunk, ctrGen, ecbArgs, ksXor, callEcb, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.all, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, eb.encSpSafe, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem open_spSafe : («open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases wide <;> simp only [«seal», «open», revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, entry, keys, keysS, derive, deriveBlock, expand, hkey, polyval, polyvalLong, polyvalOne, stage, stageTail, lensAt, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, tagIn, tagOut, recv, crypt, cryptChunk, ctrGen, ecbArgs, ksXor, callEcb, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.all, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, eb.encSpSafe, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem seal_correct (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp v eb wide GcmSiv.Polyval.polyvalFrom_eq hs
  exact ⟨t, s', he, abiPreserved_of_exec (seal_mx v eb wide) he hg, hp⟩

theorem open_correct (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp v eb wide GcmSiv.Polyval.polyvalFrom_eq hs
  exact ⟨t, s', he, abiPreserved_of_exec (open_mx v eb wide) he hg, hp⟩

theorem seal_ct : ConstantTime isa sealX86_64.pre sealX86_64.pub («seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seal_rel v eb wide h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem open_ct : ConstantTime isa openX86_64.pre openX86_64.pub («open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (open_rel v eb wide h₁ h₂ hq.1 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end

/-- A state satisfying the precondition of `vg_aes_gcm_siv_seal`: no
additional data, no data, the tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0, 3816⟩]

theorem seal_verified (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) :
    Verified X86_64.target («seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) (Proof.AesGcmSiv.sealScratchContract X86_64.abi 477 8) :=
  Verified.of_correct (seal_correct v eb wide) (seal_ct v eb wide) (by
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Proof.AesGcmSiv.sealRoundsPost, Proof.AesGcmSiv.sealX86_64, Proof.AesGcmSiv.sealPre, Proof.AesGcmSiv.oneLay,
      Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args, Proof.AesGcmSiv.stk8,
      Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [sealSat] using sealSat)

/-- A state satisfying the precondition of `vg_aes_gcm_siv_open`: as
`sealSat`, with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x8008, 24⟩]
  wr := [⟨0, 0⟩, ⟨0, 3816⟩] }

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) :
    Verified X86_64.target («open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) (Proof.AesGcmSiv.openScratchContract X86_64.abi 477 8) :=
  Verified.of_correct (open_correct v eb wide) (open_ct v eb wide)
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

/-! ## With the working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (above), in a frame that allocates it
(`Verified.stackArgScratchKept`): their working space is passed on the stack
after the six argument registers and two other stack arguments (`len` and
`tag`), so the frame of 3848 bytes holds the 3816 bytes of working space, a
copy of those two, the word that stands for the return address and the
address of the working space. The code's own calls use 8 bytes below it:
the return address of a call of `vg_aes_ctr32`, `vg_aes_expand_key`,
`vg_ghash` or `vg_aes_encrypt_blocks`, which use no stack (`Ctr32Impl.noStack`,
`KeyImpl.noStack`, `GhashImpl.noStack`, `BlocksImpl.encNoStack`). `open`'s leak, whether it succeeds, reads only its
buffers (`openLeak_local`).
-/

variable (v : GcmImpl) (eb : BlocksImpl) (wide : Bool)

theorem seal_xdepth : («seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).x86_64Depth ≤ 8 := by
  cases wide <;> simp only [«seal», revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, keys, keysS, derive, expand, polyval, polyvalLong, polyvalOne, stage, stageTail, absorb, absorbChunk, absorbTail, lens, tag, crypt, cryptChunk,
    ctrGen, ecbArgs, ksXor, callEcb, cryptTail, callCtr, callKey, callGh, Code.x86_64Depth, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, eb.encNoStack] <;>
  decide +kernel

theorem open_xdepth : («open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide).x86_64Depth ≤ 8 := by
  cases wide <;> simp only [«open», revSel, revLoopY, revMaskY, revQuad, rev2, revOne, quadsThenOnes, ksLoop, ksQuad, xor2, ksOne, Impl.Gcm.X86_64.Pclmul.const, ↓reduceIte, keys, keysS, derive, expand, polyval, polyvalLong, polyvalOne, stage, stageTail, absorb, absorbChunk, absorbTail, lens, tag, crypt, cryptChunk,
    ctrGen, ecbArgs, ksXor, callEcb, cryptTail, callCtr, callKey, callGh, Code.x86_64Depth, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, eb.encNoStack] <;>
  decide +kernel

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x8008, 16⟩], wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 3856).pre s := by
  implies_sat [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Proof.AesGcmSiv.sealRoundsPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 («seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide))
      (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 3856) :=
  X86_64.Verified.stackArgScratch (hpostOut := sealPostOut_local _) (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 477) (pre := Spec.GcmSiv.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesGcmSiv.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3848) (seal_verified v eb wide) (by decide) (by decide) (by decide)
    (seal_spSafe v eb wide) (seal_xdepth v eb wide) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x8008, 16⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesGcmSiv.openRoundsContract X86_64.abi 3856).pre s := by
  implies_sat [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost,
    Spec.GcmSiv.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, sealSat] using openFrameSat

theorem open_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 («open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide))
      (Proof.AesGcmSiv.openRoundsContract X86_64.abi 3856) :=
  X86_64.Verified.stackArgScratch (hpostOut := openPostOut_local _) (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 477) (pre := Spec.GcmSiv.openPre X86_64.abi.ptrBits)
    (post := Proof.AesGcmSiv.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.GcmSiv.openLeak X86_64.abi.ptrBits)) (bytes := 3848)
    (Proof.AesGcmSiv.Verified.of_openScratch (open_verified v eb wide))
    (by decide) (by decide) (by decide) (open_spSafe v eb wide) (open_xdepth v eb wide) (openPre_local _)
    (openPost_local _) openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.AesGcmSiv.X86_64

end

end


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
  X86_64.Verified.stackArgScratch (hpostOut := openPostOut_local _) (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
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
  X86_64.Verified.stackArgScratch (hpostOut := sealPostOut_local _) (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
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

/-- Whether `v`'s `seal` and `open` run the code in registers
(`Impl.AesGcmSiv.X86_64Reg`), which needs AES-NI and PCLMULQDQ: with them in
`v`'s callees. -/
def sivReg (v : GcmImpl) : Bool :=
  v.ctr.features.contains "aes" && (v.gh.features.contains "pclmulqdq" || v.gh.features.contains "vpclmulqdq")

/-- `v`'s loops are constant time in the code in registers. -/
theorem loopsOf_ct (v : GcmImpl) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (h : loopsOf v = some lp) :
    Proof.AesGcmSivReg.X86_64.LoopsCT lp := by
  unfold loopsOf at h
  split at h
  · cases h; exact Proof.AesGcmSivReg.X86_64.vaesLoops_ct
  · split at h
    · cases h; exact Proof.AesGcmSivReg.X86_64.avxLoops_ct
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

/-- Whether `v`'s `seal` and `open` have instances with the AVX2 copies
(`_avx2`), which the CPUs with AVX2 run at every length: not the code in
registers (`sivReg`), which copies nothing, nor with VAES and VPCLMULQDQ
(`sivStitch`), where the code takes those copies already. -/
def hasWide (v : GcmImpl) : Bool := !sivStitch v && !sivReg v

/-- Whether `v`'s instances without the AVX2 copies may run where those with
them (`hasWide`), which a dispatcher tries first, cannot: where they need
fewer CPU features. -/
def hasNarrow (v : GcmImpl) : Bool :=
  !hasWide v || !(features v ++ ["avx", "avx2"]).all (sivFeatures v).contains

/-- The implementations of `vs` whose instances a dispatcher trying them in
order could choose: each but one with no fewer CPU features than one before
it (`sivFeatures`), as a variant of AES-GCM that differs from another only
in what AES-GCM-SIV does not call. -/
def sivImpls (vs : List GcmImpl) : List GcmImpl :=
  vs.foldl (init := []) fun acc v =>
    if acc.any fun w => (sivFeatures w).all (sivFeatures v).contains then acc else acc ++ [v]

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
      h'.mem, h.mx, h'.mx]
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
    -- not `exact q`: elaborating `q` reduces its type, a `match` on the decryption, to see whether it is a function
    revert q; exact id
  · sig_pub [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openLeak, X86_64.abi, X86_64.argRegs] at q ⊢
    simp only [h.saF, h.saaF, h.gpr .rdi (by decide), h.gpr .rsi (by decide), h.gpr .rdx (by decide),
      h.gpr .rcx (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.gpr .rsp (by decide), h.mem,
      h'.saF, h'.saaF, h'.gpr .rdi (by decide), h'.gpr .rsi (by decide), h'.gpr .rdx (by decide),
      h'.gpr .rcx (by decide), h'.gpr .r8 (by decide), h'.gpr .r9 (by decide), h'.gpr .rsp (by decide),
      h'.mem, h.mx, h'.mx]
    exact q
  · sig_pub [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openLeak, X86_64.abi, X86_64.argRegs] at q
    obtain ⟨hsp, -, -, -, -, -, h8, -, h6, -⟩ := q
    exact ⟨by simpa [List.getD, List.range, List.range.loop] using h6, h8, hsp⟩


/-- The working space of `seal` and `open` on the stack: of the code in
registers (`sivReg`), or of the other code. -/
def sivStack (v : GcmImpl) : Nat := if sivReg v then 784 else 3856

/-- `seal` in registers, with `v`'s loops (`loopsOf`) if it has them. -/
def regSeal : Option Impl.AesGcmSiv.X86_64Stitch.Loops → Prog isa
  | some lp => Impl.AesGcmSiv.X86_64Reg.sealL lp
  | none => Impl.AesGcmSiv.X86_64Reg.seal

/-- `open` in registers, as `regSeal`. -/
def regOpen : Option Impl.AesGcmSiv.X86_64Stitch.Loops → Prog isa
  | some lp => Impl.AesGcmSiv.X86_64Reg.openL lp
  | none => Impl.AesGcmSiv.X86_64Reg.open

open VG.Proof.Gcm.Poly (φ x) in
/-- GHASH's field for the code in registers (`Proof.AesGcmSivReg.X86_64.MulFacts`),
whose proofs do not import its algebra. -/
private def mulFacts : Proof.AesGcmSivReg.X86_64.MulFacts where
  G H T := x * φ T = φ H
  P2 H T := x * φ T = φ H ^ 2
  P3 H T := x * φ T = φ H ^ 3
  P4 H T := x * φ T = φ H ^ 4
  step1 := fun H Y X₁ T₁ h => Proof.Gcm.X86_64.Pclmul.step1 H Y X₁ T₁ h
  step4 := fun H Y X₁ X₂ X₃ X₄ T₁ T₂ T₃ T₄ h₁ h₂ h₃ h₄ =>
    Proof.Gcm.X86_64.Pclmul.step4 H Y X₁ X₂ X₃ X₄ T₁ T₂ T₃ T₄ h₁ h₂ h₃ h₄
  inv := Proof.Gcm.X86_64.Pclmul.hInvImm_ok
  pows := fun _ s h1 hH => Proof.Gcm.X86_64.Pclmul.pows_ok s h1 hH
  pv := GcmSiv.Polyval.polyvalFrom_eq

/-- The code of `v`'s `seal`, in its frame: in registers where `v` has the
instructions (`sivReg`), with `v`'s loops, which interleave counter mode
and POLYVAL, from 256 bytes. -/
def framedSeal (v : GcmImpl) : Prog isa :=
  if sivReg v then Impl.StackScratch.X86_64.withStackArgScratch 776 2 (regSeal (loopsOf v))
  else Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (sealCode v)

/-- `open`'s, as `framedSeal`. -/
def framedOpen (v : GcmImpl) : Prog isa :=
  if sivReg v then Impl.StackScratch.X86_64.withStackArgScratch 776 2 (regOpen (loopsOf v))
  else Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (openCode v)

theorem framedSeal_verified (v : GcmImpl) :
    Verified X86_64.target (framedSeal v) (Proof.AesGcmSiv.sealRoundsContract X86_64.abi (sivStack v)) := by
  unfold framedSeal sivStack
  cases sivReg v with
  | true =>
    simp only [↓reduceIte]
    cases hl : loopsOf v with
    | some lp =>
      exact Proof.AesGcmSivReg.X86_64.sealL_framed mulFacts (loopsOf_ok v hl).1 (loopsOf_ok v hl).2
        (loopsOf_ct v hl)
    | none => exact Proof.AesGcmSivReg.X86_64.seal_framed mulFacts
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact sealCode_framed v

theorem framedOpen_verified (v : GcmImpl) :
    Verified X86_64.target (framedOpen v) (Proof.AesGcmSiv.openRoundsContract X86_64.abi (sivStack v)) := by
  unfold framedOpen sivStack
  cases sivReg v with
  | true =>
    simp only [↓reduceIte]
    cases hl : loopsOf v with
    | some lp =>
      exact Proof.AesGcmSivReg.X86_64.openL_framed mulFacts (loopsOf_ok v hl).1 (loopsOf_ok v hl).2
        (loopsOf_ct v hl)
    | none => exact Proof.AesGcmSivReg.X86_64.open_framed mulFacts
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact openCode_framed v

theorem framedSeal_spSafe (v : GcmImpl) : (framedSeal v).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold framedSeal
  split
  · cases hl : loopsOf v with
    | some lp =>
      exact X86_64.withStackArgScratch_spSafe (Proof.AesGcmSivReg.X86_64.sealL_spSafe (loopsOf_ok v hl).2)
    | none => exact X86_64.withStackArgScratch_spSafe Proof.AesGcmSivReg.X86_64.seal_spSafe
  · exact X86_64.withStackArgScratch_spSafe (sealCode_spSafe v)

theorem framedOpen_spSafe (v : GcmImpl) : (framedOpen v).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold framedOpen
  split
  · cases hl : loopsOf v with
    | some lp =>
      exact X86_64.withStackArgScratch_spSafe (Proof.AesGcmSivReg.X86_64.openL_spSafe (loopsOf_ok v hl).2)
    | none => exact X86_64.withStackArgScratch_spSafe Proof.AesGcmSivReg.X86_64.open_spSafe
  · exact X86_64.withStackArgScratch_spSafe (openCode_spSafe v)

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

/-! ## Without secret residue

Over the bitsliced AES (`v.ctr.features = []`), the frame of `seal` and
`open` is mostly the working space of the functions they call, which AES
writes, and is wiped whole on return, in aligned stores
(`X86_64.RScrub.withScrubAllC`); their postconditions read the memory on
return only within the data and the tag (`sealOut`, `openOut`). -/

section
open VG.X86_64.Scrub VG.X86_64.RScrub

theorem sealOut (stack : Nat) :
    PostOut (Spec.GcmSiv.sealContract X86_64.abi stack) (Spec.GcmSiv.sealSig.retBits 64) :=
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
      rw [h key hl hk, Proof.AesSiv.bytesAt_congr fun i hi => Proof.AesSiv.agree_of hb.2.2.2.1 i (by simpa using hi),
        Proof.AesSiv.bytesAt_congr fun i hi => Proof.AesSiv.agree_of hb.2.2.2.2 i hi]

theorem openOut (stack : Nat) :
    PostOut (Spec.GcmSiv.openContract X86_64.abi stack) (Spec.GcmSiv.openSig.retBits 64) := by
  -- The postcondition is a `match` on a decryption, which the elaborator evaluates (AES on symbolic
  -- bytes, 2 s) wherever it reduces a type that ends in it to see what it is a function of: for the
  -- expected type of a `fun` given to `postOut_of_local` (so `?_`), and for `h` applied or as it is (so `@h`).
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
    have e := Proof.AesSiv.bytesAt_congr (n := (BitVec.setWidth 64 len).toNat) fun i hi =>
      Proof.AesSiv.agree_of hb.2.2.2.1 i (by simpa using hi)
    rw [e]
    exact @h

/-! ### The code in registers: what its frame holds on return

The code in registers writes, of its 784 bytes of stack, the working space
`W` (at 40 bytes from their start). What only the loops write of `W`, 64
bytes at `W + 64` and 248 from `W + 496`, it either leaves as it found it
(below the length from which the loops run) or zeroes (`zeroL`): which, the
data's length decides, so two runs leave the same bytes there, and `scrub`
need not wipe them (`sivKs`). -/

section
open VG VG.X86_64
open VG.Proof.AesGcmSivReg (sealX86_64 openX86_64 arg)
open VG.Proof.AesGcmSivReg.X86_64 (fineR ZeroR fineR_kept zeroOffs_sep args_of_seal args_of_open)
open VG.Impl.AesGcmSiv.X86_64Reg (zeroOffs)
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)

/-- Where `seal` and `open` leave public words in `W`: our caller's
registers, and the slots of the nonce, the additional data, its length and
the data. -/
def pubW : List Nat := [144, 152, 160, 168, 176, 184, 208, 216, 224, 232]

/-- The granules `scrub` wipes of the 784 bytes: all but those of
`zeroOffs`, of `pubW`, and of the return address and the copies of the
arguments on the stack below `W`. -/
def sivKs : List Nat :=
  (allKs [8, 776]).filter fun k =>
    !(776 :: 8 :: 24 :: 184 :: 200 :: 216 :: 248 :: 264 :: (zeroOffs.dropLast.map (· + 40))).contains k

theorem sivKs_cov : ∀ i < 784, cov sivKs [8, 776] i = false →
    zeroOffs.any (fun o => decide (40 + o ≤ i ∧ i < 40 + o + 16)) = true ∨
    pubW.any (fun d => decide (40 + d ≤ i ∧ i < 40 + d + 8)) = true ∨ (8 ≤ i ∧ i < 16) ∨
    (List.range 3).any (fun k => decide (16 + 8 * k ≤ i ∧ i < 24 + 8 * k)) = true := by decide +kernel

/-- A byte of the 784 that `scrub` does not wipe is one that `zeroL` zeroes,
one of a public word of `W`, one of the return address, or one of the copy
of an argument. -/
theorem unwiped {p x : Addr} (hx : (⟨p - BitVec.ofNat 64 784, 784⟩ : Region).Contains x 1)
    (hn : ¬ WCov sivKs [8, 776] p x) :
    (∃ o ∈ zeroOffs, (⟨p - BitVec.ofNat 64 776 + BitVec.ofNat 64 32 + BitVec.ofNat 64 o, 16⟩ : Region).Contains x 1) ∨
    (∃ d ∈ pubW, (⟨p - BitVec.ofNat 64 776 + BitVec.ofNat 64 32 + BitVec.ofNat 64 d, 8⟩ : Region).Contains x 1) ∨
    (⟨p - BitVec.ofNat 64 776, 8⟩ : Region).Contains x 1 ∨
    ((⟨p - BitVec.ofNat 64 776 + BitVec.ofNat 64 8, 24⟩ : Region).Contains x 1 ∧
      ∃ k < 3, (⟨p - BitVec.ofNat 64 776 + BitVec.ofNat 64 (8 * (k + 1)), 8⟩ : Region).Contains x 1) := by
  have hi : (x - (p - BitVec.ofNat 64 784)).toNat < 784 := by
    simp only [Region.Contains] at hx; omega_using [hx]
  have hc : cov sivKs [8, 776] (x - (p - BitVec.ofNat 64 784)).toNat = false := by
    cases h : cov sivKs [8, 776] (x - (p - BitVec.ofNat 64 784)).toNat with
    | false => rfl
    | true => exact absurd ⟨hx, h⟩ hn
  have eW : ∀ o : Nat, p - BitVec.ofNat 64 776 + BitVec.ofNat 64 32 + BitVec.ofNat 64 o =
      p - BitVec.ofNat 64 784 + BitVec.ofNat 64 (40 + o) := fun o => by
    rw [sub_add_ofNat p (b := 776) (d := 32) (by decide), ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      sub_add_ofNat p (b := 784) (d := 40) (by decide)]
  have eA : ∀ o : Nat, p - BitVec.ofNat 64 776 + BitVec.ofNat 64 o =
      p - BitVec.ofNat 64 784 + BitVec.ofNat 64 (8 + o) := fun o => by
    rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, sub_add_ofNat p (b := 784) (d := 8) (by decide)]
  have ex : p - BitVec.ofNat 64 784 + BitVec.ofNat 64 (x - (p - BitVec.ofNat 64 784)).toNat = x := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have inB : ∀ {lo len : Nat}, lo ≤ (x - (p - BitVec.ofNat 64 784)).toNat →
      (x - (p - BitVec.ofNat 64 784)).toNat < lo + len → len ≤ 24 →
      (⟨p - BitVec.ofNat 64 784 + BitVec.ofNat 64 lo, len⟩ : Region).Contains x 1 := fun {lo len} h₁ h₂ h₃ => by
    have := VG.Offset.contains (p - BitVec.ofNat 64 784) (n := 1) h₁ (by omega_using [h₂] : _ ≤ lo + len)
      (by omega_using [h₁, h₃, hi])
    rw [ex] at this
    exact this
  rcases sivKs_cov _ hi hc with h | h | h | h
  · obtain ⟨o, ho, hb⟩ := List.any_eq_true.mp h
    obtain ⟨hb₁, hb₂⟩ := of_decide_eq_true hb
    exact .inl ⟨o, ho, by rw [eW]; exact inB hb₁ hb₂ (by decide)⟩
  · obtain ⟨d, hd, hb⟩ := List.any_eq_true.mp h
    obtain ⟨hb₁, hb₂⟩ := of_decide_eq_true hb
    exact .inr (.inl ⟨d, hd, by rw [eW]; exact inB hb₁ hb₂ (by decide)⟩)
  · refine .inr (.inr (.inl ?_))
    have := inB (lo := 8 + 0) (len := 8) h.1 h.2 (by decide)
    rw [← eA 0] at this
    simpa using this
  · obtain ⟨k, hk, hb⟩ := List.any_eq_true.mp h
    obtain ⟨hb₁, hb₂⟩ := of_decide_eq_true hb
    have hk := List.mem_range.mp hk
    refine .inr (.inr (.inr ⟨?_, k, hk, ?_⟩))
    · rw [eA]; exact inB (by omega_using [hb₁]) (by omega_using [hb₂, hk]) (by decide)
    · rw [eA]; exact inB (by omega_using [hb₁]) (by omega_using [hb₂]) (by decide)

/-- Memories with the same 64-bit word at `a` have the same bytes there. -/
theorem byte_of_readW {m₁ m₂ : Mem} {a x : Addr} (h : m₁.readW a 64 = m₂.readW a 64)
    (hx : (⟨a, 8⟩ : Region).Contains x 1) : m₁ x = m₂ x := by
  have hj : (x - a).toNat < 8 := by simp only [Region.Contains] at hx; omega_using [hx]
  have b : ∀ m : Mem, m x = (m.readW a 64).extractLsb' (8 * (x - a).toNat) 8 := fun m => by
    have := Mem.extractLsb'_read m a hj
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at this
    rw [← this]; rfl
  rw [b m₁, b m₂, h]

/-- Two runs leave the same public words in `W`. -/
theorem keptW_readW {W : Addr} {R al n : Nat} {N A D : Addr} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (k₁ : Proof.AesGcmSivReg.X86_64.KeptW W R N A D al n g₁ m₁)
    (k₂ : Proof.AesGcmSivReg.X86_64.KeptW W R N A D al n g₂ m₂)
    (hg : ∀ q, q ≠ .rax → q ≠ .rsp → g₂ q = g₁ q) :
    ∀ d ∈ pubW, m₁.readW (W + BitVec.ofNat 64 d) 64 = m₂.readW (W + BitVec.ofNat 64 d) 64 := by
  intro d hd
  simp only [pubW, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (k₁.saved (.rbx, 144) (by decide)).trans ((hg .rbx (by decide) (by decide)).symm.trans (k₂.saved (.rbx, 144) (by decide)).symm)
  · exact (k₁.saved (.rbp, 152) (by decide)).trans ((hg .rbp (by decide) (by decide)).symm.trans (k₂.saved (.rbp, 152) (by decide)).symm)
  · exact (k₁.saved (.r12, 160) (by decide)).trans ((hg .r12 (by decide) (by decide)).symm.trans (k₂.saved (.r12, 160) (by decide)).symm)
  · exact (k₁.saved (.r13, 168) (by decide)).trans ((hg .r13 (by decide) (by decide)).symm.trans (k₂.saved (.r13, 168) (by decide)).symm)
  · exact (k₁.saved (.r14, 176) (by decide)).trans ((hg .r14 (by decide) (by decide)).symm.trans (k₂.saved (.r14, 176) (by decide)).symm)
  · exact (k₁.saved (.r15, 184) (by decide)).trans ((hg .r15 (by decide) (by decide)).symm.trans (k₂.saved (.r15, 184) (by decide)).symm)
  · exact k₁.slots.nonce.trans k₂.slots.nonce.symm
  · exact k₁.slots.aad.trans k₂.slots.aad.symm
  · exact k₁.slots.alen.trans k₂.slots.alen.symm
  · exact k₁.slots.data.trans k₂.slots.data.symm

/-- The tag `seal` writes is apart from the copies of the arguments. -/
theorem tag_args {n : State} (q : (Proof.AesGcmSiv.sealScratchContract X86_64.abi 93 8).pre n)
    (P : Proof.AesGcmSivReg.sealPre n) :
    (⟨Proof.AesGcmSivReg.arg n 1, 16⟩ : Region).Disjoint ⟨n.gpr .rsp + BitVec.ofNat 64 8, 24⟩ := by
  have hk : 6 ≤ ((Proof.AesGcmSiv.sealScratchSig 93).words abi.ptrBits).length := by decide
  obtain ⟨-, -, hwr, hpw, -⟩ := (pre_args hk).mp q
  have ht : (⟨Proof.AesGcmSivReg.arg n 1, 16⟩ : Region) ∈ n.wr := by rw [P.2.1]; simp
  rw [hwr] at ht
  obtain ⟨a, ha, e⟩ := List.mem_map.mp ht
  obtain ⟨ha, hf⟩ := List.mem_filter.mp ha
  have hl : ((Proof.AesGcmSiv.sealScratchSig 93).words abi.ptrBits).length = 9 := by decide
  have hA : argArea (Proof.AesGcmSiv.sealScratchSig 93) n =
      [((⟨n.gpr .rsp + BitVec.ofNat 64 8, 24⟩ : Region), false)] := by
    simp only [argArea, hl, stackArgAddr, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.succ_ne_zero, ↓reduceIte]
  unfold allRegions at hpw ha
  have hab : a ∈ bufRegions (Proof.AesGcmSiv.sealScratchSig 93) n := by
    rcases List.mem_append.mp ha with h | h
    · exact h
    · rw [hA, List.mem_singleton] at h
      rw [h] at hf
      exact Bool.noConfusion hf
  have hd := (List.pairwise_append.mp hpw).2.2 a hab ((⟨n.gpr .rsp + BitVec.ofNat 64 8, 24⟩ : Region), false)
    (by rw [hA]; exact List.mem_singleton_self _) (by rw [hf]; rfl)
  rw [e] at hd
  exact hd

/-- A run of code in a frame of `withStackArgScratch` is its run from
`narrowS`, which leaves the memory the frame's run does. -/
theorem inner_run {sig : Sig} {nm : String} {e : Elem} {n : Nat}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {stack bytes : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (h : Verified X86_64.target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * X86_64.nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s s' : State} {t : List Leak} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (ex : Exec isa (withStackArgScratch bytes (X86_64.nStack sig) c) s t s') :
    ∃ t₃ s₃, (Sig.scratchContract abi sig nm e n pre post wa stack leak).pre (narrowS sig e n bytes s) ∧
      Exec isa c (narrowS sig e n bytes s) t₃ s₃ ∧ s'.mem = s₃.mem := by
  have hp := narrowS_pre (nm := nm) hk hb.1 hb.2.1 hpre hs
  obtain ⟨t₃, s₃, he, ha, -⟩ := h.1 _ hp
  obtain ⟨hex, -, hm, -⟩ := withStackArgScratch_runMem hk hb hst (SpSafe.of_all hsp) hd hs he ha
  obtain ⟨-, rfl⟩ := ex.det hex
  exact ⟨t₃, s₃, hp, he, hm⟩

/-- Two runs agree, on entry, on the stack below the stack pointer. -/
theorem stack_init_eq {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} (hk : 6 ≤ (sig.words abi.ptrBits).length)
    {s₁ s₂ : State} (h₁ : (sig.contract abi pre post wa (stack + 1) leak).pre s₁) (ho : Outside 0 s₁ s₂)
    {x : Addr} (hx : (⟨s₁.gpr .rsp - BitVec.ofNat 64 (stack + 1), stack + 1⟩ : Region).Contains x 1) :
    s₁.mem x = s₂.mem x := by
  rw [pre_args hk] at h₁
  obtain ⟨-, hrd, hwr, -, hres, -⟩ := h₁
  refine ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2 x fun r hr hc => ?_
  have hm : ∃ a ∈ allRegions sig s₁, a.1 = r := by
    rw [hrd, hwr] at hr
    rcases List.mem_append.mp hr with h | h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h; exact ⟨a, (List.mem_filter.mp ha).1, rfl⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h; exact ⟨a, (List.mem_filter.mp ha).1, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hm
  exact hres _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) a ha x hx hc

/-- `seal` in registers, in its frame: two runs leave the same bytes in
what `scrub` does not wipe of the stack, for code `c` that says what it
wrote (`fineR`) and zeroes what only the loops write, from `θ` bytes. -/
theorem seal_resOk {θ : Nat} {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcmSiv.sealScratchContract X86_64.abi 93 8))
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ 8)
    (hw : ∀ {s : State}, Proof.AesGcmSivReg.sealPre s → WP isa c s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcmSivReg.sealX86_64.post s s' ∧
      Frame (⟨Proof.AesGcmSivReg.arg s 1, 16⟩ :: fineR θ (Proof.AesGcmSivReg.arg s 2) (s.gpr .r9) (Proof.AesGcmSivReg.arg s 0).toNat) s.mem s'.mem ∧
      (θ ≤ (Proof.AesGcmSivReg.arg s 0).toNat → ∀ o ∈ zeroOffs, ZeroR ⟨Proof.AesGcmSivReg.arg s 2 + BitVec.ofNat 64 o, 16⟩ s'.mem) ∧
      Proof.AesGcmSivReg.X86_64.KeptW (Proof.AesGcmSivReg.arg s 2) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .rcx)
        (s.gpr .r9) (s.gpr .r8).toNat (Proof.AesGcmSivReg.arg s 0).toNat s.gpr s'.mem) :
    ResOk (withStackArgScratch 776 2 c) (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 784) 784 sivKs
      [8, 776] := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ hp₁ hp₂ hpub hout _ e₁ e₂ x hx hnc
  have hk : 6 ≤ (Spec.GcmSiv.sealSig.words abi.ptrBits).length := by decide
  have run : ∀ {s u : State} {t : List Leak}, (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 784).pre s →
      Exec isa (withStackArgScratch 776 2 c) s t u →
      (Proof.AesGcmSiv.sealScratchContract X86_64.abi 93 8).pre (narrowS Spec.GcmSiv.sealSig .u64 93 776 s) ∧
      ∃ b : State, u.mem = b.mem ∧
        Frame (⟨Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.sealSig .u64 93 776 s) 1, 16⟩ ::
          fineR θ (Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.sealSig .u64 93 776 s) 2)
            ((narrowS Spec.GcmSiv.sealSig .u64 93 776 s).gpr .r9)
            (Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.sealSig .u64 93 776 s) 0).toNat)
          (narrowS Spec.GcmSiv.sealSig .u64 93 776 s).mem b.mem ∧
        (θ ≤ (Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.sealSig .u64 93 776 s) 0).toNat → ∀ o ∈ zeroOffs,
          ZeroR ⟨Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.sealSig .u64 93 776 s) 2 + BitVec.ofNat 64 o, 16⟩ b.mem) ∧
        Proof.AesGcmSivReg.X86_64.KeptW (Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.sealSig .u64 93 776 s) 2) ((narrowS Spec.GcmSiv.sealSig .u64 93 776 s).gpr .rsi).toNat
          ((narrowS Spec.GcmSiv.sealSig .u64 93 776 s).gpr .rdx) ((narrowS Spec.GcmSiv.sealSig .u64 93 776 s).gpr .rcx) ((narrowS Spec.GcmSiv.sealSig .u64 93 776 s).gpr .r9) ((narrowS Spec.GcmSiv.sealSig .u64 93 776 s).gpr .r8).toNat
          (Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.sealSig .u64 93 776 s) 0).toNat (narrowS Spec.GcmSiv.sealSig .u64 93 776 s).gpr b.mem := by
    intro s u t hs ex
    obtain ⟨_, b, q, i, m⟩ := inner_run (nm := "work") (e := .u64) (n := 93) (stack := 8) (bytes := 776) hv hk
      (by decide) (by decide) hsp hd
      (fun vs m₁ m₂ hl hb _ => Proof.AesGcmSiv.sealPre_local _ vs m₁ m₂ hl hb) hs ex
    obtain ⟨_, b', j, -, -, fr, z, kp⟩ := hw (Proof.AesGcmSivReg.X86_64.seal_impl.pre _ q)
    obtain ⟨-, rfl⟩ := i.det j
    exact ⟨q, b, m, fr, z, kp⟩
  obtain ⟨q₁, b₁, m₁, fr₁, z₁, kp₁⟩ := run hp₁ e₁
  obtain ⟨q₂, b₂, m₂, fr₂, z₂, kp₂⟩ := run hp₂ e₂
  generalize hn₁ : narrowS Spec.GcmSiv.sealSig .u64 93 776 s₁ = n₁ at q₁ fr₁ z₁ kp₁
  generalize hn₂ : narrowS Spec.GcmSiv.sealSig .u64 93 776 s₂ = n₂ at q₂ fr₂ z₂ kp₂
  have P₁ : Proof.AesGcmSivReg.sealPre n₁ := Proof.AesGcmSivReg.X86_64.seal_impl.pre _ q₁
  have P₂ : Proof.AesGcmSivReg.sealPre n₂ := Proof.AesGcmSivReg.X86_64.seal_impl.pre _ q₂
  obtain ⟨⟨Ar₁, Tb₁⟩, -, hrT₁⟩ := Proof.AesGcmSivReg.X86_64.args_of_seal P₁
  obtain ⟨⟨Ar₂, Tb₂⟩, -, hrT₂⟩ := Proof.AesGcmSivReg.X86_64.args_of_seal P₂
  have pub : Proof.AesGcmSivReg.onePub n₁ n₂ := Proof.AesGcmSivReg.X86_64.seal_impl.pub _ _ q₁ q₂ (by
    rw [← hn₁, ← hn₂]
    exact narrowS_pub (nm := "work") (e := .u64) (n := 93) (stack := 8) (bytes := 776) hk (by decide) (by decide)
      hp₁ hp₂ hpub)
  have eW : Proof.AesGcmSivReg.arg n₂ 2 = Proof.AesGcmSivReg.arg n₁ 2 := (pub.2.2.2.2.2.2.2 2 (by decide)).symm
  have eL : Proof.AesGcmSivReg.arg n₂ 0 = Proof.AesGcmSivReg.arg n₁ 0 := (pub.2.2.2.2.2.2.2 0 (by decide)).symm
  obtain ⟨hsp₁, hg₁, -, ha₁, f₁⟩ := narrowS_facts (nm := "work") (e := .u64) (n := 93) (stack := 8) (bytes := 776)
    hk (by decide) (by decide) hp₁
  obtain ⟨hsp₂, hg₂, -, -, f₂⟩ := narrowS_facts (nm := "work") (e := .u64) (n := 93) (stack := 8) (bytes := 776)
    hk (by decide) (by decide) hp₂
  rw [hn₁] at hsp₁ hg₁ ha₁ f₁
  rw [hn₂] at hsp₂ hg₂ f₂
  have hG : ∀ q, q ≠ .rax → q ≠ .rsp → n₂.gpr q = n₁.gpr q := fun q h₁ h₂ =>
    (hg₂ q h₁ h₂).trans ((hout.2.2.1 q h₁).symm.trans (hg₁ q h₁ h₂).symm)
  have eS : n₂.gpr .rsp = n₁.gpr .rsp := by rw [hsp₂, hsp₁, hout.2.2.1 .rsp (by decide)]
  rw [eW, eL, hG .rsi (by decide) (by decide), hG .rdx (by decide) (by decide), hG .rcx (by decide) (by decide),
    hG .r9 (by decide) (by decide), hG .r8 (by decide) (by decide)] at kp₂
  have hW : Proof.AesGcmSivReg.arg n₁ 2 = s₁.gpr .rsp - BitVec.ofNat 64 776 + BitVec.ofNat 64 32 := by
    have l₁ : ((Spec.GcmSiv.sealSig.withScratch "work" Elem.u64 93).words abi.ptrBits).length = 9 := by decide
    have l₂ : (Spec.GcmSiv.sealSig.words abi.ptrBits).length = 8 := by decide
    have l₃ : X86_64.nStack Spec.GcmSiv.sealSig = 2 := by decide
    have h := congrArg (fun l => l.getD 8 0) ha₁
    simpa [allArgs, argRegs, l₁, l₂, l₃, List.range, List.range.loop] using h
  rw [m₁, m₂]
  rcases unwiped hx hnc with ⟨o, ho, hc⟩ | ⟨d, hd, hc⟩ | hc | ⟨hca, k, hk3, hc⟩
  rotate_left
  · rw [← hW] at hc
    exact byte_of_readW (keptW_readW kp₁ kp₂ hG d hd) hc
  · rw [← hsp₁] at hc
    have k₁ : b₁.mem x = n₁.mem x := fr₁ x fun q hq hq' => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hrT₁ x hc hq'
      · exact Proof.AesGcmSivReg.X86_64.fineR_apart Ar₁.retW Ar₁.retD q hq x hc hq'
    have k₂ : b₂.mem x = n₂.mem x := fr₂ x fun q hq hq' => by
      rw [← eS] at hc
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hrT₂ x hc hq'
      · exact Proof.AesGcmSivReg.X86_64.fineR_apart Ar₂.retW Ar₂.retD q hq x hc hq'
    have g₁ : n₁.mem x = s₁.mem x := f₁ x fun q hq hq' => by
      simp only [List.mem_singleton] at hq; subst hq
      exact VG.Offset.disjoint_base (n₁.gpr .rsp) (d := 8) (n := 24) (k := 8) (by decide) (by decide) x
        (by rw [hsp₁]; exact hq') hc
    have g₂ : n₂.mem x = s₂.mem x := f₂ x fun q hq hq' => by
      simp only [List.mem_singleton] at hq; subst hq
      exact VG.Offset.disjoint_base (n₁.gpr .rsp) (d := 8) (n := 24) (k := 8) (by decide) (by decide) x
        (by rw [← eS, hsp₂]; exact hq') hc
    rw [k₁, k₂, g₁, g₂]
    exact stack_init_eq (stack := 783) hk hp₁ hout hx
  · rw [← hsp₁] at hc hca
    have k₁ : b₁.mem x = n₁.mem x := fr₁ x fun q hq hq' => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact tag_args q₁ P₁ x hq' hca
      · exact Proof.AesGcmSivReg.X86_64.fineR_apart Ar₁.argsW Ar₁.argsD q hq x hca hq'
    have k₂ : b₂.mem x = n₂.mem x := fr₂ x fun q hq hq' => by
      rw [← eS] at hca
      rcases List.mem_cons.mp hq with rfl | hq
      · exact tag_args q₂ P₂ x hq' hca
      · exact Proof.AesGcmSivReg.X86_64.fineR_apart Ar₂.argsW Ar₂.argsD q hq x hca hq'
    have ea := pub.2.2.2.2.2.2.2 k hk3
    rw [show Proof.AesGcmSivReg.arg n₂ k = n₂.mem.readW (n₂.gpr .rsp + BitVec.ofNat 64 (8 * (k + 1))) 64 from rfl,
      eS] at ea
    rw [k₁, k₂]
    exact byte_of_readW ea hc
  rw [← hW] at hc
  obtain ⟨-, -, h₃⟩ := zeroOffs_sep o ho
  by_cases hθ : θ ≤ (Proof.AesGcmSivReg.arg n₁ 0).toNat
  · rw [z₁ hθ o ho x hc, z₂ (by rw [eL]; exact hθ) o ho x (by rw [eW]; exact hc)]
  · have hlt : (Proof.AesGcmSivReg.arg n₁ 0).toNat < θ := Nat.lt_of_not_le hθ
    have k₁ : b₁.mem x = n₁.mem x := fr₁ x fun q hq hq' => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (Tb₁.w.sub_right (Proof.AesGcmSivReg.X86_64.Lay.wSub h₃)).symm x hc hq'
      · exact fineR_kept Ar₁.lay Ar₁.data.w hlt ho q hq x hc hq'
    have k₂ : b₂.mem x = n₂.mem x := fr₂ x fun q hq hq' => by
      rw [← eW] at hc
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (Tb₂.w.sub_right (Proof.AesGcmSivReg.X86_64.Lay.wSub h₃)).symm x hc hq'
      · exact fineR_kept Ar₂.lay Ar₂.data.w (by rw [eL]; exact hlt) ho q hq x hc hq'
    have g₁ : n₁.mem x = s₁.mem x := f₁ x fun q hq hq' => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (Ar₁.argsW.sub_right (Proof.AesGcmSivReg.X86_64.Lay.wSub h₃)) x (by rw [hsp₁]; exact hq') hc
    have g₂ : n₂.mem x = s₂.mem x := f₂ x fun q hq hq' => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (Ar₂.argsW.sub_right (Proof.AesGcmSivReg.X86_64.Lay.wSub h₃)) x (by rw [hsp₂]; exact hq')
        (by rw [eW]; exact hc)
    rw [k₁, k₂, g₁, g₂]
    exact stack_init_eq (stack := 783) hk hp₁ hout hx

/-- `open`'s, as `seal_resOk`. -/
theorem open_resOk {θ : Nat} {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcmSiv.openScratchContract X86_64.abi 93 8))
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ 8)
    (hw : ∀ {s : State}, Proof.AesGcmSivReg.openPre s → WP isa c s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcmSivReg.openX86_64.post s s' ∧
      Frame (fineR θ (Proof.AesGcmSivReg.arg s 2) (s.gpr .r9) (Proof.AesGcmSivReg.arg s 0).toNat) s.mem s'.mem ∧
      (θ ≤ (Proof.AesGcmSivReg.arg s 0).toNat → ∀ o ∈ zeroOffs, ZeroR ⟨Proof.AesGcmSivReg.arg s 2 + BitVec.ofNat 64 o, 16⟩ s'.mem) ∧
      Proof.AesGcmSivReg.X86_64.KeptW (Proof.AesGcmSivReg.arg s 2) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .rcx)
        (s.gpr .r9) (s.gpr .r8).toNat (Proof.AesGcmSivReg.arg s 0).toNat s.gpr s'.mem) :
    ResOk (withStackArgScratch 776 2 c) (Proof.AesGcmSiv.openRoundsContract X86_64.abi 784) 784 sivKs
      [8, 776] := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ hp₁ hp₂ hpub hout _ e₁ e₂ x hx hnc
  have hk : 6 ≤ (Spec.GcmSiv.openSig.words abi.ptrBits).length := by decide
  have run : ∀ {s u : State} {t : List Leak}, (Proof.AesGcmSiv.openRoundsContract X86_64.abi 784).pre s →
      Exec isa (withStackArgScratch 776 2 c) s t u →
      (Proof.AesGcmSiv.openScratchContract X86_64.abi 93 8).pre (narrowS Spec.GcmSiv.openSig .u64 93 776 s) ∧
      ∃ b : State, u.mem = b.mem ∧
        Frame (
          fineR θ (Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.openSig .u64 93 776 s) 2)
            ((narrowS Spec.GcmSiv.openSig .u64 93 776 s).gpr .r9)
            (Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.openSig .u64 93 776 s) 0).toNat)
          (narrowS Spec.GcmSiv.openSig .u64 93 776 s).mem b.mem ∧
        (θ ≤ (Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.openSig .u64 93 776 s) 0).toNat → ∀ o ∈ zeroOffs,
          ZeroR ⟨Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.openSig .u64 93 776 s) 2 + BitVec.ofNat 64 o, 16⟩ b.mem) ∧
        Proof.AesGcmSivReg.X86_64.KeptW (Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.openSig .u64 93 776 s) 2) ((narrowS Spec.GcmSiv.openSig .u64 93 776 s).gpr .rsi).toNat
          ((narrowS Spec.GcmSiv.openSig .u64 93 776 s).gpr .rdx) ((narrowS Spec.GcmSiv.openSig .u64 93 776 s).gpr .rcx) ((narrowS Spec.GcmSiv.openSig .u64 93 776 s).gpr .r9) ((narrowS Spec.GcmSiv.openSig .u64 93 776 s).gpr .r8).toNat
          (Proof.AesGcmSivReg.arg (narrowS Spec.GcmSiv.openSig .u64 93 776 s) 0).toNat (narrowS Spec.GcmSiv.openSig .u64 93 776 s).gpr b.mem := by
    intro s u t hs ex
    obtain ⟨_, b, q, i, m⟩ := inner_run (nm := "work") (e := .u64) (n := 93) (stack := 8) (bytes := 776)
      (leak := some (Spec.GcmSiv.openLeak X86_64.abi.ptrBits)) (Proof.AesGcmSiv.Verified.of_openScratch hv) hk
      (by decide) (by decide) hsp hd
      (fun vs m₁ m₂ hl hb _ => Proof.AesGcmSiv.openPre_local _ vs m₁ m₂ hl hb) hs ex
    obtain ⟨_, b', j, -, -, fr, z, kp⟩ := hw (Proof.AesGcmSivReg.X86_64.open_impl.pre _ q)
    obtain ⟨-, rfl⟩ := i.det j
    exact ⟨q, b, m, fr, z, kp⟩
  obtain ⟨q₁, b₁, m₁, fr₁, z₁, kp₁⟩ := run hp₁ e₁
  obtain ⟨q₂, b₂, m₂, fr₂, z₂, kp₂⟩ := run hp₂ e₂
  generalize hn₁ : narrowS Spec.GcmSiv.openSig .u64 93 776 s₁ = n₁ at q₁ fr₁ z₁ kp₁
  generalize hn₂ : narrowS Spec.GcmSiv.openSig .u64 93 776 s₂ = n₂ at q₂ fr₂ z₂ kp₂
  have P₁ : Proof.AesGcmSivReg.openPre n₁ := Proof.AesGcmSivReg.X86_64.open_impl.pre _ q₁
  have P₂ : Proof.AesGcmSivReg.openPre n₂ := Proof.AesGcmSivReg.X86_64.open_impl.pre _ q₂
  obtain ⟨⟨Ar₁, Tb₁⟩, -⟩ := Proof.AesGcmSivReg.X86_64.args_of_open P₁
  obtain ⟨⟨Ar₂, Tb₂⟩, -⟩ := Proof.AesGcmSivReg.X86_64.args_of_open P₂
  have pub : Proof.AesGcmSivReg.onePub n₁ n₂ := (Proof.AesGcmSivReg.X86_64.open_impl.pub _ _ q₁ q₂ (by
    rw [← hn₁, ← hn₂]
    exact narrowS_pub (nm := "work") (e := .u64) (n := 93) (stack := 8) (bytes := 776) hk (by decide) (by decide)
      hp₁ hp₂ hpub (Sig.LeakLocal.toL (sig := Spec.GcmSiv.openSig)
        (leak := some (Spec.GcmSiv.openLeak X86_64.abi.ptrBits)) (Proof.AesGcmSiv.openLeak_local _)))).1
  have eW : Proof.AesGcmSivReg.arg n₂ 2 = Proof.AesGcmSivReg.arg n₁ 2 := (pub.2.2.2.2.2.2.2 2 (by decide)).symm
  have eL : Proof.AesGcmSivReg.arg n₂ 0 = Proof.AesGcmSivReg.arg n₁ 0 := (pub.2.2.2.2.2.2.2 0 (by decide)).symm
  obtain ⟨hsp₁, hg₁, -, ha₁, f₁⟩ := narrowS_facts (nm := "work") (e := .u64) (n := 93) (stack := 8) (bytes := 776)
    hk (by decide) (by decide) hp₁
  obtain ⟨hsp₂, hg₂, -, -, f₂⟩ := narrowS_facts (nm := "work") (e := .u64) (n := 93) (stack := 8) (bytes := 776)
    hk (by decide) (by decide) hp₂
  rw [hn₁] at hsp₁ hg₁ ha₁ f₁
  rw [hn₂] at hsp₂ hg₂ f₂
  have hG : ∀ q, q ≠ .rax → q ≠ .rsp → n₂.gpr q = n₁.gpr q := fun q h₁ h₂ =>
    (hg₂ q h₁ h₂).trans ((hout.2.2.1 q h₁).symm.trans (hg₁ q h₁ h₂).symm)
  have eS : n₂.gpr .rsp = n₁.gpr .rsp := by rw [hsp₂, hsp₁, hout.2.2.1 .rsp (by decide)]
  rw [eW, eL, hG .rsi (by decide) (by decide), hG .rdx (by decide) (by decide), hG .rcx (by decide) (by decide),
    hG .r9 (by decide) (by decide), hG .r8 (by decide) (by decide)] at kp₂
  have hW : Proof.AesGcmSivReg.arg n₁ 2 = s₁.gpr .rsp - BitVec.ofNat 64 776 + BitVec.ofNat 64 32 := by
    have l₁ : ((Spec.GcmSiv.openSig.withScratch "work" Elem.u64 93).words abi.ptrBits).length = 9 := by decide
    have l₂ : (Spec.GcmSiv.openSig.words abi.ptrBits).length = 8 := by decide
    have l₃ : X86_64.nStack Spec.GcmSiv.openSig = 2 := by decide
    have h := congrArg (fun l => l.getD 8 0) ha₁
    simpa [allArgs, argRegs, l₁, l₂, l₃, List.range, List.range.loop] using h
  rw [m₁, m₂]
  rcases unwiped hx hnc with ⟨o, ho, hc⟩ | ⟨d, hd, hc⟩ | hc | ⟨hca, k, hk3, hc⟩
  rotate_left
  · rw [← hW] at hc
    exact byte_of_readW (keptW_readW kp₁ kp₂ hG d hd) hc
  · rw [← hsp₁] at hc
    have k₁ : b₁.mem x = n₁.mem x := fr₁ x fun q hq hq' => by
      exact Proof.AesGcmSivReg.X86_64.fineR_apart Ar₁.retW Ar₁.retD q hq x hc hq'
    have k₂ : b₂.mem x = n₂.mem x := fr₂ x fun q hq hq' => by
      rw [← eS] at hc
      exact Proof.AesGcmSivReg.X86_64.fineR_apart Ar₂.retW Ar₂.retD q hq x hc hq'
    have g₁ : n₁.mem x = s₁.mem x := f₁ x fun q hq hq' => by
      simp only [List.mem_singleton] at hq; subst hq
      exact VG.Offset.disjoint_base (n₁.gpr .rsp) (d := 8) (n := 24) (k := 8) (by decide) (by decide) x
        (by rw [hsp₁]; exact hq') hc
    have g₂ : n₂.mem x = s₂.mem x := f₂ x fun q hq hq' => by
      simp only [List.mem_singleton] at hq; subst hq
      exact VG.Offset.disjoint_base (n₁.gpr .rsp) (d := 8) (n := 24) (k := 8) (by decide) (by decide) x
        (by rw [← eS, hsp₂]; exact hq') hc
    rw [k₁, k₂, g₁, g₂]
    exact stack_init_eq (stack := 783) hk hp₁ hout hx
  · rw [← hsp₁] at hc hca
    have k₁ : b₁.mem x = n₁.mem x := fr₁ x fun q hq hq' => by
      exact Proof.AesGcmSivReg.X86_64.fineR_apart Ar₁.argsW Ar₁.argsD q hq x hca hq'
    have k₂ : b₂.mem x = n₂.mem x := fr₂ x fun q hq hq' => by
      rw [← eS] at hca
      exact Proof.AesGcmSivReg.X86_64.fineR_apart Ar₂.argsW Ar₂.argsD q hq x hca hq'
    have ea := pub.2.2.2.2.2.2.2 k hk3
    rw [show Proof.AesGcmSivReg.arg n₂ k = n₂.mem.readW (n₂.gpr .rsp + BitVec.ofNat 64 (8 * (k + 1))) 64 from rfl,
      eS] at ea
    rw [k₁, k₂]
    exact byte_of_readW ea hc
  rw [← hW] at hc
  obtain ⟨-, -, h₃⟩ := zeroOffs_sep o ho
  by_cases hθ : θ ≤ (Proof.AesGcmSivReg.arg n₁ 0).toNat
  · rw [z₁ hθ o ho x hc, z₂ (by rw [eL]; exact hθ) o ho x (by rw [eW]; exact hc)]
  · have hlt : (Proof.AesGcmSivReg.arg n₁ 0).toNat < θ := Nat.lt_of_not_le hθ
    have k₁ : b₁.mem x = n₁.mem x := fr₁ x fun q hq hq' =>
      fineR_kept Ar₁.lay Ar₁.data.w hlt ho q hq x hc hq'
    have k₂ : b₂.mem x = n₂.mem x := fr₂ x fun q hq hq' => by
      rw [← eW] at hc
      exact fineR_kept Ar₂.lay Ar₂.data.w (by rw [eL]; exact hlt) ho q hq x hc hq'
    have g₁ : n₁.mem x = s₁.mem x := f₁ x fun q hq hq' => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (Ar₁.argsW.sub_right (Proof.AesGcmSivReg.X86_64.Lay.wSub h₃)) x (by rw [hsp₁]; exact hq') hc
    have g₂ : n₂.mem x = s₂.mem x := f₂ x fun q hq hq' => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (Ar₂.argsW.sub_right (Proof.AesGcmSivReg.X86_64.Lay.wSub h₃)) x (by rw [hsp₂]; exact hq')
        (by rw [eW]; exact hc)
    rw [k₁, k₂, g₁, g₂]
    exact stack_init_eq (stack := 783) hk hp₁ hout hx

/-- `seal` in registers for `v`, with its loops if it has them, in its frame. -/
theorem regSeal_framed (v : GcmImpl) :
    Verified X86_64.target (withStackArgScratch 776 2 (regSeal (loopsOf v)))
      (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 784) := by
  cases hl : loopsOf v with
  | some lp => exact Proof.AesGcmSivReg.X86_64.sealL_framed mulFacts (loopsOf_ok v hl).1 (loopsOf_ok v hl).2 (loopsOf_ct v hl)
  | none => exact Proof.AesGcmSivReg.X86_64.seal_framed mulFacts

theorem regOpen_framed (v : GcmImpl) :
    Verified X86_64.target (withStackArgScratch 776 2 (regOpen (loopsOf v)))
      (Proof.AesGcmSiv.openRoundsContract X86_64.abi 784) := by
  cases hl : loopsOf v with
  | some lp => exact Proof.AesGcmSivReg.X86_64.openL_framed mulFacts (loopsOf_ok v hl).1 (loopsOf_ok v hl).2 (loopsOf_ct v hl)
  | none => exact Proof.AesGcmSivReg.X86_64.open_framed mulFacts

theorem regSeal_sp (v : GcmImpl) :
    (withStackArgScratch 776 2 (regSeal (loopsOf v))).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases hl : loopsOf v with
  | some lp => exact X86_64.withStackArgScratch_spSafe (Proof.AesGcmSivReg.X86_64.sealL_spSafe (loopsOf_ok v hl).2)
  | none => exact X86_64.withStackArgScratch_spSafe Proof.AesGcmSivReg.X86_64.seal_spSafe

theorem regOpen_sp (v : GcmImpl) :
    (withStackArgScratch 776 2 (regOpen (loopsOf v))).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases hl : loopsOf v with
  | some lp => exact X86_64.withStackArgScratch_spSafe (Proof.AesGcmSivReg.X86_64.openL_spSafe (loopsOf_ok v hl).2)
  | none => exact X86_64.withStackArgScratch_spSafe Proof.AesGcmSivReg.X86_64.open_spSafe

theorem regSeal_resOk (v : GcmImpl) :
    ResOk (withStackArgScratch 776 2 (regSeal (loopsOf v))) (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 784) 784
      sivKs [8, 776] := by
  cases hl : loopsOf v with
  | some lp =>
    exact seal_resOk (θ := 256) (Proof.AesGcmSivReg.X86_64.sealL_verified mulFacts (loopsOf_ok v hl).1 (loopsOf_ok v hl).2 (loopsOf_ct v hl))
      (Proof.AesGcmSivReg.X86_64.sealL_spSafe (loopsOf_ok v hl).2) (Proof.AesGcmSivReg.X86_64.sealL_xdepth (loopsOf_ok v hl).2)
      fun h => Proof.AesGcmSivReg.X86_64.sealL_wp mulFacts (loopsOf_ok v hl).1 h
  | none =>
    exact seal_resOk (θ := 2 ^ 64) (Proof.AesGcmSivReg.X86_64.seal_verified mulFacts) Proof.AesGcmSivReg.X86_64.seal_spSafe Proof.AesGcmSivReg.X86_64.seal_xdepth fun h => Proof.AesGcmSivReg.X86_64.seal_wp mulFacts h

theorem regOpen_resOk (v : GcmImpl) :
    ResOk (withStackArgScratch 776 2 (regOpen (loopsOf v))) (Proof.AesGcmSiv.openRoundsContract X86_64.abi 784) 784
      sivKs [8, 776] := by
  cases hl : loopsOf v with
  | some lp =>
    exact open_resOk (θ := 256) (Proof.AesGcmSivReg.X86_64.openL_verified mulFacts (loopsOf_ok v hl).1 (loopsOf_ok v hl).2 (loopsOf_ct v hl))
      (Proof.AesGcmSivReg.X86_64.openL_spSafe (loopsOf_ok v hl).2) (Proof.AesGcmSivReg.X86_64.openL_xdepth (loopsOf_ok v hl).2)
      fun h => Proof.AesGcmSivReg.X86_64.openL_wp mulFacts (loopsOf_ok v hl).1 h
  | none =>
    exact open_resOk (θ := 2 ^ 64) (Proof.AesGcmSivReg.X86_64.open_verified mulFacts) Proof.AesGcmSivReg.X86_64.open_spSafe Proof.AesGcmSivReg.X86_64.open_xdepth fun h => Proof.AesGcmSivReg.X86_64.open_wp mulFacts h

/-- `vg_aes_gcm_siv_seal` in registers over `v`, before `scrub`. -/
def regSealReg (v : GcmImpl) : Registration Spec.GcmSiv.sealApi X86_64.target where
  suffix := v.suffix
  code := withStackArgScratch 776 2 (regSeal (loopsOf v))
  stack := 784
  verified := Proof.AesGcmSiv.seal_keyed (regSeal_framed v)
  spSafe := regSeal_sp v

/-- `vg_aes_gcm_siv_open` in registers over `v`, before `scrub`. -/
def regOpenReg (v : GcmImpl) : Registration Spec.GcmSiv.openApi X86_64.target where
  suffix := v.suffix
  code := withStackArgScratch 776 2 (regOpen (loopsOf v))
  stack := 784
  verified := Proof.AesGcmSiv.open_keyed (regOpen_framed v)
  spSafe := regOpen_sp v

end

/-- A registration of the code not in registers, its 3856 bytes of stack
wiped whole on return, in the chunks `[8, 3848]`. -/
def scrubSoft {api : Api} (r : Registration api X86_64.target)
    (hpost : PostOut r.contract (api.sig.retBits
      ((X86_64.abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) : Registration api X86_64.target :=
  withScrubAllC r hpost [8, 3848]

/-- `vg_aes_gcm_siv_seal` over `v`: in registers (`sivReg`), with what holds nothing of the keys or the
data left unwiped (`sivKs`). -/
def sealReg (v : GcmImpl) : Registration Spec.GcmSiv.sealApi X86_64.target :=
  if sivReg v then withScrubResC (regSealReg v) (sealOut _) sivKs [8, 776] (regSeal_resOk v)
  else scrubSoft {
    suffix := v.suffix
    code := framedSeal v
    stack := sivStack v
    verified := Proof.AesGcmSiv.seal_keyed (framedSeal_verified v)
    spSafe := framedSeal_spSafe v } (sealOut _)

/-- `vg_aes_gcm_siv_open` over `v`. (`@openOut`: applied without `@`, the elaborator reduces its type,
`PostOut` of a postcondition that is a `match` on a decryption, to see what it is a function of.) -/
def openReg (v : GcmImpl) : Registration Spec.GcmSiv.openApi X86_64.target :=
  if sivReg v then withScrubResC (regOpenReg v) (@openOut _) sivKs [8, 776] (regOpen_resOk v)
  else scrubSoft {
    suffix := v.suffix
    code := framedOpen v
    stack := sivStack v
    verified := Proof.AesGcmSiv.open_keyed (framedOpen_verified v)
    spSafe := framedOpen_spSafe v } (@openOut _)

/-- `vg_aes_gcm_siv_seal` over `v`, with the AVX2 copies. -/
def wideSealReg (v : GcmImpl) : Registration Spec.GcmSiv.sealApi X86_64.target :=
  scrubSoft {
    suffix := v.suffix ++ "_avx2"
    code := avx2SealCode v
    stack := 3856
    verified := Proof.AesGcmSiv.seal_keyed (avx2Seal_verified v)
    spSafe := avx2Seal_spSafe v } (sealOut _)

/-- `vg_aes_gcm_siv_open` over `v`, with the AVX2 copies. -/
def wideOpenReg (v : GcmImpl) : Registration Spec.GcmSiv.openApi X86_64.target :=
  scrubSoft {
    suffix := v.suffix ++ "_avx2"
    code := avx2OpenCode v
    stack := 3856
    verified := Proof.AesGcmSiv.open_keyed (avx2Open_verified v)
    spSafe := avx2Open_spSafe v } (@openOut _)

end

end VG.Proof.AesGcmSiv.X86_64
