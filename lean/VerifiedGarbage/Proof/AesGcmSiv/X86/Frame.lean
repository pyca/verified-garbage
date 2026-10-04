import VerifiedGarbage.Proof.AesGcmSiv.X86.Verified
import VerifiedGarbage.Proof.AesGcm.X86.Frame
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-!
# AES-GCM-SIV on x86, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the eight argument slots, the address of the working space and its 2816
bytes, 2856 bytes. The code's own calls use 28 bytes below it. The copies
are read only where the pre- and postconditions read the buffers, and
`open`'s leak, whether it succeeds, reads only its buffers
(`Proof/AesGcmSiv/Scratch.lean`).
-/

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

theorem seal_stackUse : stackUse («seal» v.callees) ≤ 28 := by
  simp only [«seal», sivEntry, Impl.AesGcm.X86.entry, tagOut, keys, derive, deriveBlock, derivePost, expand, hkey,
    polyval, absorb, chunk, absTail, absTailPre, lens, onStr, tag, crypt, cryptBlock, cryptTail, callCtr, callKey,
    callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees, stackUse,
    v.ctr.stack, v.ctr.expandStack, v.gh.stack]
  decide +kernel

theorem open_stackUse : stackUse («open» v.callees) ≤ 28 := by
  simp only [«open», sivEntry, Impl.AesGcm.X86.entry, recvTag, keys, derive, deriveBlock, derivePost, expand, hkey,
    polyval, absorb, chunk, absTail, absTailPre, lens, onStr, tag, crypt, cryptBlock, cryptTail, mask, callCtr,
    callKey, callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees,
    stackUse, v.ctr.stack, v.ctr.expandStack, v.gh.stack]
  decide +kernel

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space: as `sealSat`, with eight stack arguments. -/
def sealFrameSat : State :=
  { sealSat with wr := [⟨0x3000, 0⟩, ⟨0x4000, 16⟩, ⟨0x8004, 32⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.GcmSiv.sealContract X86.abi 2884).pre s := by
  implies_sat [Spec.GcmSiv.sealContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [sealFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using sealFrameSat

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space: as `sealFrameSat`, with the tag read only. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x4000, 16⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x8004, 32⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.GcmSiv.openContract X86.abi 2884).pre s := by
  implies_sat [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Spec.GcmSiv.openPost,
    Spec.GcmSiv.openLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [openFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using openFrameSat

theorem seal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2856 8 («seal» v.callees))
      (Spec.GcmSiv.sealContract X86.abi 2884) :=
  X86.Verified.stackScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64) (n := 352)
    (pre := Spec.GcmSiv.sealPre X86.abi.ptrBits) (post := Spec.GcmSiv.sealPost X86.abi.ptrBits)
    (wa := true) (stack := 28) (bytes := 2856) (seal_verified v) (by decide) (seal_noEsp v)
    (seal_stackUse v) (Proof.AesGcmSiv.sealPre_local _) (Proof.AesGcmSiv.sealPost_local _) sealFrameSat_pre

theorem open_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2856 8 («open» v.callees))
      (Spec.GcmSiv.openContract X86.abi 2884) :=
  X86.Verified.stackScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64) (n := 352)
    (pre := Spec.GcmSiv.openPre X86.abi.ptrBits) (post := Spec.GcmSiv.openPost X86.abi.ptrBits)
    (wa := true) (stack := 28) (leak := some (Spec.GcmSiv.openLeak X86.abi.ptrBits)) (bytes := 2856)
    (open_verified v) (by decide) (open_noEsp v) (open_stackUse v) (Proof.AesGcmSiv.openPre_local _)
    (Proof.AesGcmSiv.openPost_local _) openFrameSat_pre (hleak := Proof.AesGcmSiv.openLeak_local _)

end VG.Proof.AesGcmSiv.X86
