module

public import VerifiedGarbage.Proof.AesGcmSiv.Scratch
import VerifiedGarbage.Proof.AesGcmSiv.X86.FnCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Open
import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import Mathlib.Data.List.Dedup
import VerifiedGarbage.Proof.AesGcm.X86.Frame

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

theorem seal_spSafe : («seal» v.callees).all (fun i => !isa.writesSp i) = true := by
  simp only [«seal», sivEntry, tagOut, Impl.AesGcm.X86.entry, keys, derive, deriveBlock, derivePost, expand, hkey, polyval,
    absorb, chunk, absTail, absTailPre, lens, onStr, tag, crypt, cryptBlock, cryptTail, callCtr, callKey, callGh,
    Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees, Code.all, v.ctr.spSafe, v.ctr.expandSpSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem open_spSafe : («open» v.callees).all (fun i => !isa.writesSp i) = true := by
  simp only [«open», sivEntry, recvTag, Impl.AesGcm.X86.entry, keys, derive, deriveBlock, derivePost, expand, hkey, polyval,
    absorb, chunk, absTail, absTailPre, lens, onStr, tag, crypt, cryptBlock, cryptTail, mask, callCtr, callKey,
    callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees, Code.all,
    v.ctr.spSafe, v.ctr.expandSpSafe, v.gh.spSafe, Bool.true_and,
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

theorem seal_noEsp : («seal» v.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«seal», sivEntry, Impl.AesGcm.X86.entry, tagOut, keys, derive, deriveBlock, derivePost, expand, hkey,
    polyval, absorb, chunk, absTail, absTailPre, lens, onStr, tag, crypt, cryptBlock, cryptTail, callCtr, callKey,
    callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees,
    Code.allInstrs, noEsp_of v.ctr.nosp, noEsp_of v.ctr.expandNosp, noEsp_of v.gh.nosp, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem open_noEsp : («open» v.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«open», sivEntry, Impl.AesGcm.X86.entry, recvTag, keys, derive, deriveBlock, derivePost, expand, hkey,
    polyval, absorb, chunk, absTail, absTailPre, lens, onStr, tag, crypt, cryptBlock, cryptTail, mask, callCtr,
    callKey, callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees,
    Code.allInstrs, noEsp_of v.ctr.nosp, noEsp_of v.ctr.expandNosp, noEsp_of v.gh.nosp, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem seal_stackUse : stackUse («seal» v.callees) ≤ 32 := by
  simp only [«seal», sivEntry, Impl.AesGcm.X86.entry, tagOut, keys, derive, deriveBlock, derivePost, expand, hkey,
    polyval, absorb, chunk, absTail, absTailPre, lens, onStr, tag, crypt, cryptBlock, cryptTail, callCtr, callKey,
    callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees, stackUse,
    v.ctr.stack, v.ctr.expandStack, v.gh.stack]
  decide +kernel

theorem open_stackUse : stackUse («open» v.callees) ≤ 32 := by
  simp only [«open», sivEntry, Impl.AesGcm.X86.entry, recvTag, keys, derive, deriveBlock, derivePost, expand, hkey,
    polyval, absorb, chunk, absTail, absTailPre, lens, onStr, tag, crypt, cryptBlock, cryptTail, mask, callCtr,
    callKey, callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees,
    stackUse, v.ctr.stack, v.ctr.expandStack, v.gh.stack]
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
