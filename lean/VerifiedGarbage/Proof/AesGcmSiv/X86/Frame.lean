module

public import VerifiedGarbage.Proof.AesGcmSiv.Scratch
import VerifiedGarbage.Proof.AesGcmSiv.X86.FnCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Open
import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Proof.AesGcm.X86.Frame
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.ScrubLocal
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Scrub
public import VerifiedGarbage.Impl.AesGcmSiv.X86

/-! ### `AesGcmSiv.X86.Verified`, which only this module used -/

section

/-!
# AES-GCM-SIV on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32_to`, `vg_aes_expand_key` and
`vg_ghash`), given that the tag input computed with GHASH is the RFC's
(`TagInputEq`, which the registration file has from
`Proof.GcmSiv.Polyval.tagInput_eq_tagInputG`, so that no proof here imports
its algebra), a state satisfying each
precondition, and the shared contracts with the working space as a last
argument (`Proof/AesGcmSiv/Scratch.lean`), with 32 bytes of stack: a call of
`vg_aes_ctr32_to` in place (its seven arguments and return address), which
makes no calls.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86
open VG.Proof.AesGcm.X86 (GcmImpl)

/-- The return value: the low word of `edx:eax`. -/
theorem setWidth_ret (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.zero_or, Nat.mod_eq_of_lt this]

section
variable (v : GcmImpl)

theorem blocks_spSafe : (blocks v.callees).all (fun i => !isa.writesSp i) = true := by
  unfold blocks
  split
  · decide +kernel
  · simp only [cryptBlock, callCtr, Impl.AesGcm.X86.ctrCall, GcmImpl.callees, Code.all, v.ctr.spSafe, Bool.true_and,
      Bool.and_true]
    decide +kernel

theorem rev_spSafe : (rev v.callees).all (fun i => !isa.writesSp i) = true := by
  unfold rev
  split <;> decide +kernel

theorem seal_spSafe : («seal» v.callees).all (fun i => !isa.writesSp i) = true := by
  have hb := blocks_spSafe v
  have hr := rev_spSafe v
  simp only [GcmImpl.callees] at hb hr
  simp only [«seal», sivEntry, tagOut, Impl.AesGcm.X86.entry, keys, derive, deriveBlock, derivePost, expand, hkey, polyval,
    absorb, chunk, chunkPre, absTail, absTailPre, lens, onStr, tag, crypt, cryptTail, callCtr, callKey, callGh,
    Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees, Code.all, hb, hr, v.ctr.spSafe, v.ctr.expandSpSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem open_spSafe : («open» v.callees).all (fun i => !isa.writesSp i) = true := by
  have hb := blocks_spSafe v
  have hr := rev_spSafe v
  simp only [GcmImpl.callees] at hb hr
  simp only [«open», sivEntry, recvTag, Impl.AesGcm.X86.entry, keys, derive, deriveBlock, derivePost, expand, hkey, polyval,
    absorb, chunk, chunkPre, absTail, absTailPre, lens, onStr, tag, crypt, cryptTail, mask, callCtr, callKey,
    callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees, Code.all,
    hb, hr, v.ctr.spSafe, v.ctr.expandSpSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

end

/-- A state satisfying the precondition of `vg_aes_gcm_siv_seal`: the key
schedule at `0x1000`, 10 rounds, the nonce at `0x2000`, no additional data
(at `0x2100`), no data (at `0x3000`), the tag at `0x4000` and `work` at
`0x5000`, as stack arguments at `0x8004`. -/
def sealSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8011 then 0x21 else if a = 0x8019 then 0x30 else if a = 0x8021 then 0x40
    else if a = 0x8025 then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 16⟩, ⟨0x5000, 2816⟩, ⟨0x8004, 36⟩]

/-- As `sealSat`, with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x4000, 16⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x5000, 2816⟩, ⟨0x8004, 36⟩] }

theorem sealSat_args : arg sealSat 0 = 0x1000 ∧ arg sealSat 1 = 10 ∧ arg sealSat 2 = 0x2000 ∧
    arg sealSat 3 = 0x2100 ∧ arg sealSat 4 = 0 ∧ arg sealSat 5 = 0x3000 ∧ arg sealSat 6 = 0 ∧
    arg sealSat 7 = 0x4000 ∧ arg sealSat 8 = 0x5000 ∧ argAddr sealSat 0 = 0x8004 := by
  decide

theorem openSat_args : arg openSat 0 = 0x1000 ∧ arg openSat 1 = 10 ∧ arg openSat 2 = 0x2000 ∧
    arg openSat 3 = 0x2100 ∧ arg openSat 4 = 0 ∧ arg openSat 5 = 0x3000 ∧ arg openSat 6 = 0 ∧
    arg openSat 7 = 0x4000 ∧ arg openSat 8 = 0x5000 ∧ argAddr openSat 0 = 0x8004 :=
  sealSat_args

theorem seal_verified (v : GcmImpl) (hti : TagInputEq) :
    Verified X86.target («seal» v.callees) (Proof.AesGcmSiv.sealScratchContract X86.abi 352 32) :=
  Verified.of_correct (fun _ hs => seal_wp v hti hs) (seal_ct v) (by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, e⟩ := sealSat_args
    have esp : sealSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Proof.AesGcmSiv.sealRoundsPost, sealX86, sealPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
      stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using sealSat)

theorem open_verified (v : GcmImpl) (hti : TagInputEq) :
    Verified X86.target («open» v.callees) (Proof.AesGcmSiv.openScratchContract X86.abi 352 32) :=
  Verified.of_correct (fun _ hs => open_wp v hti hs) (open_ct v)
    { pre := by
        sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openX86, openResult, openPost, openPre, oneLay, onePub,
          schR, nonceR, aadR, dataR, tagR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes]
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openX86, openResult, openPost, openPre, oneLay, onePub,
          schR, nonceR, aadR, dataR, tagR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, setWidth_ret]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openX86, openResult, openPost, openPre, oneLay, onePub,
          schR, nonceR, aadR, dataR, tagR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, setWidth_ret] at h
        sig_simp [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openX86, openResult, openPost, openPre, oneLay, onePub,
          schR, nonceR, aadR, dataR, tagR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, setWidth_ret] [] at h
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openX86, openResult, openPost, openPre, oneLay, onePub,
          schR, nonceR, aadR, dataR, tagR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes] at h
        sig_split h
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openX86, openResult, openPost, openPre, oneLay, onePub,
          schR, nonceR, aadR, dataR, tagR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes]
        sig_simp [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openX86, openResult, openPost, openPre, oneLay, onePub,
          schR, nonceR, aadR, dataR, tagR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
      sat := by
        obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, e⟩ := openSat_args
        have esp : openSat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openX86, openResult, openPost, openPre,
          oneLay, onePub, schR, nonceR, aadR, dataR, tagR, workR, argsR', retR, stackR, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using openSat }

end VG.Proof.AesGcmSiv.X86

end

end


/-!
# AES-GCM-SIV on x86, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the eight argument slots, the address of the working space and its 2816
bytes, 2856 bytes. The code's own calls use 32 bytes below it. The copies
are read only where the pre- and postconditions read the buffers, and
`open`'s leak, whether it succeeds, reads only its buffers
(`Proof/AesGcmSiv/Scratch.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86
open VG.Proof.AesGcm.X86 (GcmImpl)

private theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (v : GcmImpl)

theorem blocks_noEsp : (blocks v.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  unfold blocks
  split
  · decide +kernel
  · simp only [cryptBlock, callCtr, Impl.AesGcm.X86.ctrCall, GcmImpl.callees, Code.allInstrs, noEsp_of v.ctr.nosp,
      Bool.true_and, Bool.and_true]
    decide +kernel

theorem blocks_stackUse : stackUse (blocks v.callees) ≤ 32 := by
  unfold blocks
  split
  · decide +kernel
  · simp only [cryptBlock, callCtr, Impl.AesGcm.X86.ctrCall, GcmImpl.callees, stackUse, v.ctr.stack]
    decide +kernel

theorem rev_noEsp : (rev v.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  unfold rev
  split <;> decide +kernel

theorem rev_stackUse : stackUse (rev v.callees) = 0 := by
  unfold rev
  split <;> decide +kernel

theorem seal_noEsp : («seal» v.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  have hb := blocks_noEsp v
  have hr := rev_noEsp v
  simp only [GcmImpl.callees] at hb hr
  simp only [«seal», sivEntry, Impl.AesGcm.X86.entry, tagOut, keys, derive, deriveBlock, derivePost, expand, hkey,
    polyval, absorb, chunk, chunkPre, absTail, absTailPre, lens, onStr, tag, crypt, cryptTail, callCtr, callKey,
    callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees,
    Code.allInstrs, hb, hr, noEsp_of v.ctr.nosp, noEsp_of v.ctr.expandNosp, noEsp_of v.gh.nosp, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem open_noEsp : («open» v.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  have hb := blocks_noEsp v
  have hr := rev_noEsp v
  simp only [GcmImpl.callees] at hb hr
  simp only [«open», sivEntry, Impl.AesGcm.X86.entry, recvTag, keys, derive, deriveBlock, derivePost, expand, hkey,
    polyval, absorb, chunk, chunkPre, absTail, absTailPre, lens, onStr, tag, crypt, cryptTail, mask, callCtr,
    callKey, callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees,
    Code.allInstrs, hb, hr, noEsp_of v.ctr.nosp, noEsp_of v.ctr.expandNosp, noEsp_of v.gh.nosp, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem seal_stackUse : stackUse («seal» v.callees) ≤ 32 := by
  have hb := blocks_stackUse v
  have hr := rev_stackUse v
  simp only [GcmImpl.callees] at hb hr
  simp only [«seal», sivEntry, Impl.AesGcm.X86.entry, tagOut, keys, derive, deriveBlock, derivePost, expand, hkey,
    polyval, absorb, chunk, chunkPre, absTail, absTailPre, lens, onStr, tag, crypt, cryptTail, callCtr, callKey,
    callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees, stackUse,
    hr, v.ctr.stack, v.ctr.expandStack, v.gh.stack]
  generalize stackUse (blocks _) = x at hb ⊢
  revert x
  decide +kernel

theorem open_stackUse : stackUse («open» v.callees) ≤ 32 := by
  have hb := blocks_stackUse v
  have hr := rev_stackUse v
  simp only [GcmImpl.callees] at hb hr
  simp only [«open», sivEntry, Impl.AesGcm.X86.entry, recvTag, keys, derive, deriveBlock, derivePost, expand, hkey,
    polyval, absorb, chunk, chunkPre, absTail, absTailPre, lens, onStr, tag, crypt, cryptTail, mask, callCtr,
    callKey, callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees,
    stackUse, hr, v.ctr.stack, v.ctr.expandStack, v.gh.stack]
  generalize stackUse (blocks _) = x at hb ⊢
  revert x
  decide +kernel

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space: as `sealSat`, with eight stack arguments. -/
def sealFrameSat : State :=
  { sealSat with wr := [⟨0x3000, 0⟩, ⟨0x4000, 16⟩, ⟨0x8004, 32⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesGcmSiv.sealRoundsContract X86.abi 2888).pre s := by
  implies_sat [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Proof.AesGcmSiv.sealRoundsPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [sealFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using sealFrameSat

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space: as `sealFrameSat`, with the tag read only. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x4000, 16⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x8004, 32⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesGcmSiv.openRoundsContract X86.abi 2888).pre s := by
  implies_sat [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost,
    Spec.GcmSiv.openLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [openFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using openFrameSat

theorem seal_framed (hti : TagInputEq) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2856 8 («seal» v.callees))
      (Proof.AesGcmSiv.sealRoundsContract X86.abi 2888) :=
  X86.Verified.stackScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64) (n := 352)
    (pre := Spec.GcmSiv.sealPre X86.abi.ptrBits) (post := Proof.AesGcmSiv.sealRoundsPost X86.abi.ptrBits)
    (wa := true) (stack := 32) (bytes := 2856) (seal_verified v hti) (by decide) (seal_noEsp v)
    (seal_stackUse v) (Proof.AesGcmSiv.sealPre_local _) (Proof.AesGcmSiv.sealPost_local _) (fun vs m m₁ m₂ r hl _ => Proof.AesGcmSiv.sealPostOut_local _ vs m m₁ m₂ r hl) sealFrameSat_pre

theorem open_framed (hti : TagInputEq) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2856 8 («open» v.callees))
      (Proof.AesGcmSiv.openRoundsContract X86.abi 2888) :=
  X86.Verified.stackScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64) (n := 352)
    (pre := Spec.GcmSiv.openPre X86.abi.ptrBits) (post := Proof.AesGcmSiv.openRoundsPost X86.abi.ptrBits)
    (wa := true) (stack := 32) (leak := some (Spec.GcmSiv.openLeak X86.abi.ptrBits)) (bytes := 2856)
    (Proof.AesGcmSiv.Verified.of_openScratch (open_verified v hti)) (by decide) (open_noEsp v)
    (open_stackUse v) (Proof.AesGcmSiv.openPre_local _)
    (Proof.AesGcmSiv.openPost_local _) (fun vs m m₁ m₂ r hl _ => Proof.AesGcmSiv.openPostOut_local _ vs m m₁ m₂ r hl) openFrameSat_pre (hleak := Proof.AesGcmSiv.openLeak_local _)

end VG.Proof.AesGcmSiv.X86

/-!
# AES-GCM-SIV on x86, without secret residue

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` over any implementations
`v` of `vg_aes_ctr32_to`, `vg_aes_expand_key` and `vg_ghash`, each followed
by the zeroing of the 2888 bytes of stack below `esp` that they and their
callees use (the 2856-byte frame of `withStackScratch`, which holds the
derived keys and the callees' working space, and the 32 bytes of a call
of `vg_aes_ctr32_to`) and by `tail`, as emitted
(`Impl.AesGcmSiv.X86.Fn`), return without secret residue
(`X86.Scrub.verifiedScrubbedAll`: `seal_scrubbed`, `open_scrubbed`). What the scrub
needs of their code is `seal_scrub` and `open_scrub`
(`Proof/AesGcmSiv/X86/Scrub.lean`), for every `v`; their postconditions
read the memory on return only within the data and the tag (`sealOut`,
`openOut`).

These theorems take the equation of POLYVAL's input with GHASH's
(`TagInputEq`) as an argument, which the registration file gives: its
proof imports the field algebra, which only leaves of the import graph may
import (`ci/check_lean_speed.py`). They are in this module, which only the
registration file imports, rather than in one of their own: this module
imports GHASH's field algebra (through `vg_ghash_pclmul`'s proof), and
another module importing it would count against the same limit.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86.Scrub

open VG VG.X86 VG.X86.Scrub VG.Impl.AesGcmSiv.X86 VG.Proof.Aes.ScrubLocal VG.Proof.AesGcmSiv.X86
open VG.Proof.AesGcm.X86 (GcmImpl)

variable (v : GcmImpl)

/-! ## Postconditions -/

theorem sealOut (stack : Nat) :
    PostOut (Spec.GcmSiv.sealContract X86.abi stack) (Spec.GcmSiv.sealSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [schedule, rounds, nonce, aad, aadLen, data, len, tag], _ =>
      simp only [Spec.GcmSiv.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.addr, ArgWord.int 32,
        ArgWord.addr, ArgWord.int 32, ArgWord.addr] (Spec.GcmSiv.sealPost 32) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.addr, ArgWord.int 32,
        ArgWord.addr, ArgWord.int 32, ArgWord.addr] (Spec.GcmSiv.sealPost 32) _ m m₂ r
      dsimp only [Curry.apply, Spec.GcmSiv.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hl hk
      rw [h key hl hk, bytesAt_of0 hb.2.2.2.1 (by simp [Nat.mod_le]), bytesAt_of0 hb.2.2.2.2 (by simp)]

theorem openOut (stack : Nat) :
    PostOut (Spec.GcmSiv.openContract X86.abi stack) (Spec.GcmSiv.openSig.retBits 32) := by
  -- The postcondition is a `match` on a decryption: prove the locality
  -- by intros, so that no expected type of a `fun` is reduced to it.
  refine postOut_of_local ScrubAbi.plain ?_
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [schedule, rounds, nonce, aad, aadLen, data, len, tag], _ =>
    simp only [Spec.GcmSiv.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.addr, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 32, ArgWord.addr] (Spec.GcmSiv.openPost 32) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.addr, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 32, ArgWord.addr] (Spec.GcmSiv.openPost 32) _ m m₂ r
    dsimp only [Curry.apply, Spec.GcmSiv.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    rw [bytesAt_of0 (n := (BitVec.setWidth 32 len).toNat) hb.2.2.2.1 (by simp [Nat.mod_le])]
    exact @h

/-! ## The functions as emitted -/

/-- `vg_aes_gcm_siv_seal` over `v` as emitted (`Impl.AesGcmSiv.X86.Fn.«seal»`)
meets its contract in constant time and returns without secret residue. -/
theorem seal_scrubbed (hti : TagInputEq) :
    VerifiedScrubbed X86.target (Impl.AesGcmSiv.X86.Fn.«seal» v.callees)
      (Spec.GcmSiv.sealContract X86.abi 2888) 0 :=
  verifiedScrubbedAll (api := Spec.GcmSiv.sealApi) {
      suffix := v.suffix
      code := Impl.StackScratch.X86.withStackScratch 2856 8 («seal» v.callees)
      verified := Proof.AesGcmSiv.seal_keyed (seal_framed v hti)
      spSafe := Proof.AesGcm.X86.withStackScratch_spSafe (seal_spSafe v) }
    (sealOut _) (W := 2888) (hs := seal_scrub v)

/-- `vg_aes_gcm_siv_open` over `v` as emitted (`Impl.AesGcmSiv.X86.Fn.«open»`)
meets its contract in constant time and returns without secret residue.
(`@openOut`, as on x86-64: applied without `@`, the elaborator reduces its
type to see what it is a function of.) -/
theorem open_scrubbed (hti : TagInputEq) :
    VerifiedScrubbed X86.target (Impl.AesGcmSiv.X86.Fn.«open» v.callees)
      (Spec.GcmSiv.openContract X86.abi 2888) 32 :=
  verifiedScrubbedAll (api := Spec.GcmSiv.openApi) {
      suffix := v.suffix
      code := Impl.StackScratch.X86.withStackScratch 2856 8 («open» v.callees)
      verified := Proof.AesGcmSiv.open_keyed (open_framed v hti)
      spSafe := Proof.AesGcm.X86.withStackScratch_spSafe (open_spSafe v) }
    (@openOut _) (W := 2888) (hs := open_scrub v)

/-- `Impl.AesGcmSiv.X86.Fn.«seal»` writes `esp` only in its frames and calls. -/
theorem seal_fnSpSafe :
    (Impl.AesGcmSiv.X86.Fn.«seal» v.callees).all (fun i => !X86.isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.AesGcm.X86.withStackScratch_spSafe (seal_spSafe v))

/-- `Impl.AesGcmSiv.X86.Fn.«open»` writes `esp` only in its frames and calls. -/
theorem open_fnSpSafe :
    (Impl.AesGcmSiv.X86.Fn.«open» v.callees).all (fun i => !X86.isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.AesGcm.X86.withStackScratch_spSafe (open_spSafe v))

end VG.Proof.AesGcmSiv.X86.Scrub
