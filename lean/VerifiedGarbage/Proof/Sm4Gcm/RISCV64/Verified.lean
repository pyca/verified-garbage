module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Sm4Gcm.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Init
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.InitCT
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTCryptFn
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTFin
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTVerify
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Seal
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTSeal
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Open
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTOpen
import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs

/-!
# SM4-GCM on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Sm4/Gcm/Contract.lean` with the working space as a last argument
(`Proof/Sm4Gcm/Scratch.lean`), with the 3232 bytes of stack that
`vg_sm4_ctr32`'s frame takes (the deepest of the callees'). Then each
function in a frame that allocates its working space, as AES-GCM's
(`Proof/AesGcm/RISCV64/Verified.lean`); `vg_sm4_gcm_stream_init` and
`vg_sm4_gcm_stream_aad` are AES-GCM's.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Proof.AesGcm.RISCV64 (args onePub)

theorem init_correct (s : State) (hs : initRISCV64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initRISCV64.post s s' :=
  init_wp hs

theorem streamEncrypt_correct (s : State) (hs : streamEncryptRISCV64.pre s) :
    ∃ t s', Exec isa streamEncrypt s t s' ∧ abiPreserved s s' ∧ streamEncryptRISCV64.post s s' :=
  streamEncrypt_wp hs

theorem streamDecrypt_correct (s : State) (hs : streamDecryptRISCV64.pre s) :
    ∃ t s', Exec isa streamDecrypt s t s' ∧ abiPreserved s s' ∧ streamDecryptRISCV64.post s s' :=
  streamDecrypt_wp hs

theorem streamFinish_correct (s : State) (hs : streamFinishRISCV64.pre s) :
    ∃ t s', Exec isa streamFinish s t s' ∧ abiPreserved s s' ∧ streamFinishRISCV64.post s s' :=
  streamFinish_wp hs

theorem streamVerify_correct (s : State) (hs : streamVerifyRISCV64.pre s) :
    ∃ t s', Exec isa streamVerify s t s' ∧ abiPreserved s s' ∧ streamVerifyRISCV64.post s s' :=
  streamVerify_wp hs

theorem seal_correct (s : State) (hs : sealRISCV64.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealRISCV64.post s s' :=
  seal_wp hs

theorem open_correct (s : State) (hs : openRISCV64.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openRISCV64.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions (with empty buffers) -/

def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a4 => 0x2000 | .a6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩]

def finSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a4 => 0x5000 | .a5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩]

def verSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a4 => 0x5000 | .a6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

/-! ## The shared contracts -/

theorem init_verified :
    Verified RISCV64.target init (Proof.Sm4Gcm.initScratchContract RISCV64.abi 3232) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Proof.Sm4Gcm.initScratchContract, Proof.Sm4Gcm.initScratchSig, Spec.Sm4.Gcm.initPost,
      initRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true] [initSat] using initSat)

theorem streamEncrypt_verified :
    Verified RISCV64.target streamEncrypt (Proof.Sm4Gcm.streamEncryptScratchContract RISCV64.abi 3232) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    sig_implies [Proof.Sm4Gcm.streamEncryptScratchContract, Proof.Sm4Gcm.streamCryptScratchSig,
      Spec.Sm4.Gcm.streamEncryptPost, streamEncryptRISCV64, streamCryptPre, streamCryptPub, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true] [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified :
    Verified RISCV64.target streamDecrypt (Proof.Sm4Gcm.streamDecryptScratchContract RISCV64.abi 3232) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    sig_implies [Proof.Sm4Gcm.streamDecryptScratchContract, Proof.Sm4Gcm.streamCryptScratchSig,
      Spec.Sm4.Gcm.streamDecryptPost, streamDecryptRISCV64, streamCryptPre, streamCryptPub, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true] [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified :
    Verified RISCV64.target streamFinish (Proof.Sm4Gcm.streamFinishScratchContract RISCV64.abi 3232) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    sig_implies [Proof.Sm4Gcm.streamFinishScratchContract, Proof.Sm4Gcm.streamFinishScratchSig,
      Spec.Sm4.Gcm.streamFinishPost, streamFinishRISCV64, finPre, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true] [finSat] using finSat)

theorem streamVerify_verified :
    Verified RISCV64.target streamVerify (Proof.Sm4Gcm.streamVerifyScratchContract RISCV64.abi 3232) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    sig_implies [Proof.Sm4Gcm.streamVerifyScratchContract, Proof.Sm4Gcm.streamVerifyScratchSig,
      Spec.Sm4.Gcm.streamVerifyPost, streamVerifyRISCV64, verPre, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true] [verSat] using verSat)

/-- The working space at `0x6000`, the stack argument. -/
def sealSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | .a5 => 0x4000 | .a7 => 0x5000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩]

theorem seal_verified :
    Verified RISCV64.target «seal» (Proof.Sm4Gcm.sealScratchContract RISCV64.abi 3232) :=
  Verified.of_correct seal_correct seal_ct (by
    sig_implies [Proof.Sm4Gcm.sealScratchContract, Proof.Sm4Gcm.sealScratchSig, Spec.Sm4.Gcm.sealPost,
      sealRISCV64, sealPre, onePub, args, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true,
      stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

/-- `tag_len` 0 and the working space at `0x6000`, the stack arguments. -/
def openSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | .a5 => 0x4000 | .a7 => 0x5000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9009 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 2560⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low 32 bits
of `a0`; and `open`'s public data include its leak, whether it succeeds. -/
theorem open_verified :
    Verified RISCV64.target «open» (Proof.Sm4Gcm.openScratchContract RISCV64.abi 3232) :=
  Verified.of_correct open_correct open_ct
    { pre := by
        sig_implies_pre [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          openRISCV64, openPre, onePub, args, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig, Spec.Sm4.Gcm.openPost,
          RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
        simp only [openRISCV64] at h
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig, Spec.Sm4.Gcm.openLeak,
          openRISCV64, openPre, onePub, args, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, leak_bool hl⟩
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · exact a0
        · exact a1
      sat := by
        sig_implies_sat [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig, Spec.Sm4.Gcm.openPost,
          openRISCV64, openPre, onePub, args, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
          [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

/-! ## With the working space on the stack

Each function runs its code, proved with the working space as an argument,
in a frame that allocates it: the functions whose arguments all arrive in
registers in a frame of 2560 bytes, the working space in the next register
(`Verified.stackScratchL`); `seal` and `open`, whose last arguments arrive
on the stack, in a frame that copies them and then passes the working
space's address (`Verified.stackScratchArgs`): `seal`'s first, as its only
stack argument.
-/

/-- A state satisfying `vg_sm4_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract RISCV64.abi 5792).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost,
    RISCV64.abi, RISCV64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a2 init)
      (Spec.Sm4.Gcm.initContract RISCV64.abi 5792) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.initPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 3232) (bytes := 2560) init_verified (by decide) (by decide) initFrameSat_pre

/-- A state satisfying the preconditions of `vg_sm4_gcm_stream_encrypt` and
`vg_sm4_gcm_stream_decrypt`, without the working space. -/
def streamCryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamEncryptContract RISCV64.abi 5792).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamEncryptContract, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost,
    RISCV64.abi, RISCV64.argRegs] [streamCryptFrameSat, streamCryptSat] using streamCryptFrameSat

theorem streamEncrypt_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 streamEncrypt)
      (Spec.Sm4.Gcm.streamEncryptContract RISCV64.abi 5792) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Curry.const (fun _ => True) _)
    (post := Spec.Sm4.Gcm.streamEncryptPost RISCV64.abi.ptrBits) (wa := true) (stack := 3232)
    (bytes := 2560) streamEncrypt_verified (by decide) (by decide) streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamDecryptContract RISCV64.abi 5792).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamDecryptContract, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost,
    RISCV64.abi, RISCV64.argRegs] [streamCryptFrameSat, streamCryptSat] using streamCryptFrameSat

theorem streamDecrypt_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 streamDecrypt)
      (Spec.Sm4.Gcm.streamDecryptContract RISCV64.abi 5792) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Curry.const (fun _ => True) _)
    (post := Spec.Sm4.Gcm.streamDecryptPost RISCV64.abi.ptrBits) (wa := true) (stack := 3232)
    (bytes := 2560) streamDecrypt_verified (by decide) (by decide) streamDecryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishContract RISCV64.abi 5792).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishContract, Spec.Sm4.Gcm.streamFinishSig,
    Spec.Sm4.Gcm.streamFinishPost, RISCV64.abi, RISCV64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 streamFinish)
      (Spec.Sm4.Gcm.streamFinishContract RISCV64.abi 5792) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Curry.const (fun _ => True) _)
    (post := Spec.Sm4.Gcm.streamFinishPost RISCV64.abi.ptrBits) (wa := true) (stack := 3232)
    (bytes := 2560) streamFinish_verified (by decide) (by decide) finFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifyContract RISCV64.abi 5792).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifyContract, Spec.Sm4.Gcm.streamVerifySig,
    Spec.Sm4.Gcm.streamVerifyPost, RISCV64.abi, RISCV64.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 streamVerify)
      (Spec.Sm4.Gcm.streamVerifyContract RISCV64.abi 5792) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Curry.const (fun _ => True) _)
    (post := Spec.Sm4.Gcm.streamVerifyPost RISCV64.abi.ptrBits) (wa := true) (stack := 3232)
    (bytes := 2560) streamVerify_verified (by decide) (by decide) verFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition, without the working
space: no stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩], wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract RISCV64.abi 5808).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost, RISCV64.abi,
    RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

/-- `seal`, whose working space is its only stack argument: the frame passes
its address above its stack pointer (`Verified.stackScratchArgs`). -/
theorem seal_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2576 0 «seal»)
      (Spec.Sm4.Gcm.sealContract RISCV64.abi 5808) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.sealPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 3232) (bytes := 2576) (m := 0) seal_verified (by decide) (by decide)
    (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_open`'s precondition, without the working
space: `tag_len` alone on the stack. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 8⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract RISCV64.abi 5808).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak,
    RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

/-- `open`, whose `tag_len` arrives on the stack before the working space. -/
theorem open_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2576 1 «open»)
      (Spec.Sm4.Gcm.openContract RISCV64.abi 5808) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.openPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 3232) (bytes := 2576) (m := 1)
    (leak := some (Spec.Sm4.Gcm.openLeak RISCV64.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.openPost_local _)
    openFrameSat_pre (hleak := Proof.Sm4Gcm.openLeak_local _)

end VG.Proof.Sm4Gcm.RISCV64
