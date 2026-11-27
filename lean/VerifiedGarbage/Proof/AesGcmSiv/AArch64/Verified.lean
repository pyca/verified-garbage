module

public import VerifiedGarbage.Proof.AesGcmSiv.Scratch
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.FnCT
import VerifiedGarbage.Proof.GcmSiv.Polyval
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM-SIV on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`), with the tag input computed with GHASH equal to the RFC's
(`tagInput_eq`, from `Proof.GcmSiv.Polyval`, imported here only so that the
other proofs need not import its algebra), a state satisfying each
precondition, and the shared contracts of `Spec/GcmSiv/Contract.lean` with
the working space as a last argument (`Proof/AesGcmSiv/Scratch.lean`, 476
words), with no stack: the calls keep the return address in `x30`, which
each function saves in the working space. The last section allocates the
working space.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.Impl.AesGcmSiv.AArch64
open VG.Proof.AesGcm.AArch64 (GcmImpl)

/-- RFC 8452 Appendix A: POLYVAL with `H` is GHASH with `H · x`. -/
theorem tagInput_eq : TagInputEq := fun a n pt d => by
  rw [GcmSiv.tagInput_eq, Spec.GcmSiv.polyval, GcmSiv.Polyval.polyvalFrom_eq]
  rfl

/-! ## v8–v15 -/

theorem seal_keepsV (v : GcmImpl) : («seal» v.callees).allInstrs keepsV = true := by
  simp only [«seal», keys, derive, expand, polyval, absorb, absTail, absTailPre, chunk, chunkPre, chunkLen, revLoop,
    lens, tag, tagOut, crypt, cryptBlock, cryptTail, callCtr, callKey, callGh, Impl.AesGcm.AArch64.copyLoop,
    Impl.AesGcm.AArch64.xorLoop, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

theorem open_keepsV (v : GcmImpl) : («open» v.callees).allInstrs keepsV = true := by
  simp only [«open», keys, derive, expand, polyval, absorb, absTail, absTailPre, chunk, chunkPre, chunkLen, revLoop,
    lens, tag, recv, crypt, cryptBlock, cryptTail, mask, callCtr, callKey, callGh, Impl.AesGcm.AArch64.copyLoop,
    Impl.AesGcm.AArch64.xorLoop, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

/-! ## Correctness -/

/-- The working space of `seal` and `open` over `v`: the 1760 bytes the code
uses itself, then what its callees need: key expansion's 512 bytes over an
implementation of counter mode that needs none (`Ctr32Impl.scratch`), else
counter mode's 2048. -/
def gsivWn (v : GcmImpl) : Nat := if v.ctr.scratch = 0 then 2272 else 3808

theorem gsivWn_cases (v : GcmImpl) : gsivWn v = 2272 ∨ gsivWn v = 3808 := by
  unfold gsivWn; split <;> simp

theorem gsivWn_hv (v : GcmImpl) : v.ctr.scratch ≤ gsivWn v - 1760 := by
  rcases v.ctr.scratch_ok with h | h <;> simp [gsivWn, h]

theorem seal_correct (v : GcmImpl) {Wn : Nat} (hWn : 2272 ≤ Wn ∧ Wn ≤ 3808) (hv : v.ctr.scratch ≤ Wn - 1760)
    (s : State) (hs : (sealAArch64 Wn).pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ (sealAArch64 Wn).post s s' :=
  WP.withPreservedV (seal_wp v tagInput_eq hs) (seal_keepsV v)

theorem open_correct (v : GcmImpl) {Wn : Nat} (hWn : 2272 ≤ Wn ∧ Wn ≤ 3808) (hv : v.ctr.scratch ≤ Wn - 1760)
    (s : State) (hs : (openAArch64 Wn).pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ (openAArch64 Wn).post s s' :=
  WP.withPreservedV (open_wp v tagInput_eq hs) (open_keepsV v)

/-! ## States satisfying the preconditions (with empty buffers) -/

/-- `seal`'s: the tag at `0x5000`, and `F` bytes of `work` at `0x8000`, its
address at `sp`. -/
def sealSatW (F : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x7 => 0x5000 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10001 then 0x80 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x10000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x8000, F⟩]

/-- `open`'s: as `seal`'s, with the tag read only. -/
def openSatW (F : Nat) : State := { sealSatW F with
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x10000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x8000, F⟩] }

/-! ## The shared contracts, with `Wn / 8` words of working space as an argument -/

theorem seal_verified (v : GcmImpl) {Wn : Nat} (h : Wn = 2272 ∨ Wn = 3808) (hv : v.ctr.scratch ≤ Wn - 1760) :
    Verified AArch64.target («seal» v.callees) (Proof.AesGcmSiv.sealScratchContract AArch64.abi (Wn / 8)) := by
  have hWn : 2272 ≤ Wn ∧ Wn ≤ 3808 := by omega
  have ok := seal_correct v hWn hv
  have ct := seal_ct (Wn := Wn) v
  rcases h with rfl | rfl
  · exact Verified.of_correct ok ct (by
      sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
        Proof.AesGcmSiv.sealRoundsPost, sealAArch64, sealPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
        AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        [sealSatW] using sealSatW 2272)
  · exact Verified.of_correct ok ct (by
      sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
        Proof.AesGcmSiv.sealRoundsPost, sealAArch64, sealPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
        AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        [sealSatW] using sealSatW 3808)

theorem open_verified (v : GcmImpl) {Wn : Nat} (h : Wn = 2272 ∨ Wn = 3808) (hv : v.ctr.scratch ≤ Wn - 1760) :
    Verified AArch64.target («open» v.callees) (Proof.AesGcmSiv.openScratchContract AArch64.abi (Wn / 8)) := by
  have hWn : 2272 ≤ Wn ∧ Wn ≤ 3808 := by omega
  have ok := open_correct v hWn hv
  have ct := open_ct (Wn := Wn) v
  rcases h with rfl | rfl
  · exact Verified.of_correct ok ct
      { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
          openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        -- `h` and the goal match on the same outcome of `decryptWith` with
        -- different matchers (`openPost`'s and `openContract`'s): split on it
        -- rather than have `exact h` unfold both to unify them.
        post := by
          intro s s' _ h
          sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
            Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
            openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
            AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
          sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
            Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
            openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
            AArch64.stackArgAddr, List.getD, List.range, List.range.loop] at h
          intro _
          split at h <;> rename_i heq <;> rw [heq] <;> exact h
        pub := by sig_implies_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
          openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
          openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [openSatW, sealSatW] using openSatW 2272 }
  · exact Verified.of_correct ok ct
      { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
          openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        -- `h` and the goal match on the same outcome of `decryptWith` with
        -- different matchers (`openPost`'s and `openContract`'s): split on it
        -- rather than have `exact h` unfold both to unify them.
        post := by
          intro s s' _ h
          sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
            Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
            openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
            AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
          sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
            Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
            openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
            AArch64.stackArgAddr, List.getD, List.range, List.range.loop] at h
          intro _
          split at h <;> rename_i heq <;> rw [heq] <;> exact h
        pub := by sig_implies_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
          openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
          openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [openSatW, sealSatW] using openSatW 3808 }

/-! ## With the working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (above), in a frame that allocates it
(`Verified.stackArgScratch`): their working space is their first stack
argument, as the eight argument registers are taken, so the frame of
`gsivWn v + 16` bytes (2288, or 3824 over an implementation of counter mode
that needs working space) holds the address of the working space and the
working space, at the next 16-byte boundary. The code itself uses no stack:
its calls keep the return address in `x30`. `open`'s leak, whether it
succeeds, reads only its buffers (`openLeak_local`).
-/

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space. -/
def sealFrameSat : State :=
  { sealSatW 0 with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩], wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩] }

theorem sealFrameSat_pre2288 : ∃ s, (Proof.AesGcmSiv.sealRoundsContract AArch64.abi 2288).pre s := by
  implies_sat [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Proof.AesGcmSiv.sealRoundsPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSatW, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem sealFrameSat_pre3824 : ∃ s, (Proof.AesGcmSiv.sealRoundsContract AArch64.abi 3824).pre s := by
  implies_sat [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Proof.AesGcmSiv.sealRoundsPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSatW, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch (gsivWn v + 16) 0 («seal» v.callees))
      (Proof.AesGcmSiv.sealRoundsContract AArch64.abi (gsivWn v + 16)) := by
  obtain hv := seal_verified v (gsivWn_cases v) (gsivWn_hv v)
  rcases gsivWn_cases v with h | h <;> rw [h] at hv ⊢ <;> simp only [Nat.reduceDiv, Nat.reduceAdd] at hv ⊢
  · exact AArch64.Verified.stackArgScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
      (n := 284) (pre := Spec.GcmSiv.sealPre AArch64.abi.ptrBits)
      (post := Proof.AesGcmSiv.sealRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2288)
      hv (by decide) (by decide) (sealPre_local _) (sealPost_local _)
      (fun vs m m₁ m₂ r hl _ => Proof.AesGcmSiv.sealPostOut_local _ vs m m₁ m₂ r hl) sealFrameSat_pre2288
  · exact AArch64.Verified.stackArgScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
      (n := 476) (pre := Spec.GcmSiv.sealPre AArch64.abi.ptrBits)
      (post := Proof.AesGcmSiv.sealRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3824)
      hv (by decide) (by decide) (sealPre_local _) (sealPost_local _)
      (fun vs m m₁ m₂ r hl _ => Proof.AesGcmSiv.sealPostOut_local _ vs m m₁ m₂ r hl) sealFrameSat_pre3824

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space. -/
def openFrameSat : State :=
  { sealSatW 0 with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x5000, 16⟩], wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre2288 : ∃ s, (Proof.AesGcmSiv.openRoundsContract AArch64.abi 2288).pre s := by
  implies_sat [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost,
    Spec.GcmSiv.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD,
    List.range, List.range.loop] [openFrameSat, sealSatW, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem openFrameSat_pre3824 : ∃ s, (Proof.AesGcmSiv.openRoundsContract AArch64.abi 3824).pre s := by
  implies_sat [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost,
    Spec.GcmSiv.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD,
    List.range, List.range.loop] [openFrameSat, sealSatW, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch (gsivWn v + 16) 0 («open» v.callees))
      (Proof.AesGcmSiv.openRoundsContract AArch64.abi (gsivWn v + 16)) := by
  obtain hv := open_verified v (gsivWn_cases v) (gsivWn_hv v)
  rcases gsivWn_cases v with h | h <;> rw [h] at hv ⊢ <;> simp only [Nat.reduceDiv, Nat.reduceAdd] at hv ⊢
  · exact AArch64.Verified.stackArgScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
      (n := 284) (pre := Spec.GcmSiv.openPre AArch64.abi.ptrBits)
      (post := Proof.AesGcmSiv.openRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2288)
      (leak := some (Spec.GcmSiv.openLeak AArch64.abi.ptrBits))
      (Proof.AesGcmSiv.Verified.of_openScratch hv) (by decide) (by decide) (openPre_local _)
      (openPost_local _) (fun vs m m₁ m₂ r hl _ => Proof.AesGcmSiv.openPostOut_local _ vs m m₁ m₂ r hl)
      openFrameSat_pre2288 (hleak := openLeak_local _)
  · exact AArch64.Verified.stackArgScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
      (n := 476) (pre := Spec.GcmSiv.openPre AArch64.abi.ptrBits)
      (post := Proof.AesGcmSiv.openRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3824)
      (leak := some (Spec.GcmSiv.openLeak AArch64.abi.ptrBits))
      (Proof.AesGcmSiv.Verified.of_openScratch hv) (by decide) (by decide) (openPre_local _)
      (openPost_local _) (fun vs m m₁ m₂ r hl _ => Proof.AesGcmSiv.openPostOut_local _ vs m m₁ m₂ r hl)
      openFrameSat_pre3824 (hleak := openLeak_local _)

end VG.Proof.AesGcmSiv.AArch64
