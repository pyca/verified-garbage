module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealFused
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Init
import VerifiedGarbage.Proof.AesGcm.PPC64LE.InitCT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamAad
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCryptFn
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTSeal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Open
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOpen
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs

/-! ### `AesGcm.PPC64LE.Verified`, which only this module used -/

section

/-!
# AES-GCM on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`; with no stack: a call keeps the return address
in the link register, which each function saves in the working space).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE

theorem init_correct (s : State) (hs : initPPC64LE.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initPPC64LE.post s s' :=
  init_wp hs

theorem streamInit_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamInitPPC64LE.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ streamInitPPC64LE.post s s' :=
  streamInit_wp hs

theorem streamAad_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamAadPPC64LE.pre s) :
    ∃ t s', Exec isa streamAad s t s' ∧ abiPreserved s s' ∧ streamAadPPC64LE.post s s' :=
  streamAad_wp hs

theorem streamEncrypt_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamEncryptPPC64LE.pre s) :
    ∃ t s', Exec isa streamEncrypt s t s' ∧ abiPreserved s s' ∧ streamEncryptPPC64LE.post s s' :=
  streamEncrypt_wp hs

theorem streamDecrypt_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamDecryptPPC64LE.pre s) :
    ∃ t s', Exec isa streamDecrypt s t s' ∧ abiPreserved s s' ∧ streamDecryptPPC64LE.post s s' :=
  streamDecrypt_wp hs

theorem streamFinish_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamFinishPPC64LE.pre s) :
    ∃ t s', Exec isa streamFinish s t s' ∧ abiPreserved s s' ∧ streamFinishPPC64LE.post s s' :=
  streamFinish_wp hs

theorem streamVerify_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamVerifyPPC64LE.pre s) :
    ∃ t s', Exec isa streamVerify s t s' ∧ abiPreserved s s' ∧ streamVerifyPPC64LE.post s s' :=
  streamVerify_wp hs

theorem sealFused_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (s : State) (hs : sealPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.AesGcm.PPC64LE.SealFused.seal s t s' ∧
      abiPreserved s s' ∧ sealPPC64LE.post s s' :=
  sealFused_wp hs

theorem open_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : openPPC64LE.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openPPC64LE.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions (with empty buffers) -/

def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

def streamInitSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamAadSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r6 => 0x2000 | .r8 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x3000 | .r8 => 0x2000 | .r10 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩]

def finSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x3000 | .r8 => 0x5000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩]

def verSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x3000 | .r8 => 0x5000 | .r10 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

/-! ## The shared contracts -/

theorem init_verified :
    Verified PPC64LE.target init (Proof.AesGcm.initScratchContract PPC64LE.abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre,
      Spec.Gcm.initPost, initPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [initSat] using initSat)

theorem streamInit_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamInit (Proof.AesGcm.streamInitScratchContract PPC64LE.abi) :=
  Verified.of_correct streamInit_correct streamInit_ct (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig,
      Spec.Gcm.streamInitPost, streamInitPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [streamInitSat] using streamInitSat)

theorem streamAad_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamAad (Proof.AesGcm.streamAadScratchContract PPC64LE.abi) :=
  Verified.of_correct streamAad_correct streamAad_ct (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig,
      Spec.Gcm.streamAadPost, streamAadPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [streamAadSat] using streamAadSat)

theorem streamEncrypt_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamEncrypt (Proof.AesGcm.streamEncryptScratchContract PPC64LE.abi) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig,
      Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, streamEncryptPPC64LE, streamCryptPre,
      streamCryptPub, rounds, PPC64LE.abi, PPC64LE.argRegs] [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamDecrypt (Proof.AesGcm.streamDecryptScratchContract PPC64LE.abi) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig,
      Spec.Gcm.streamTextPre, Proof.AesGcm.streamDecryptRoundsPost, streamDecryptPPC64LE, streamCryptPre,
      streamCryptPub, rounds, PPC64LE.abi, PPC64LE.argRegs] [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamFinish (Proof.AesGcm.streamFinishScratchContract PPC64LE.abi) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig,
      Spec.Gcm.streamFinishPre, Proof.AesGcm.streamFinishRoundsPost, streamFinishPPC64LE, finPre, rounds, PPC64LE.abi,
      PPC64LE.argRegs] [finSat] using finSat)

theorem streamVerify_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamVerify (Proof.AesGcm.streamVerifyScratchContract PPC64LE.abi) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    sig_implies [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
      Spec.Gcm.streamVerifyPre, Proof.AesGcm.streamVerifyRoundsPost, streamVerifyPPC64LE, verPre, rounds, PPC64LE.abi,
      PPC64LE.argRegs] [verSat] using verSat)

/-- `tag` at `0x5000` and the working space at `0x6000`, the stack arguments. -/
def sealSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9061 then 0x50 else bif Nat.beq a.toNat 0x9069 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9060, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩]

theorem sealFused_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target Impl.AesGcm.PPC64LE.SealFused.seal
      (Proof.AesGcm.sealScratchContract PPC64LE.abi) :=
  Verified.of_correct sealFused_correct sealFused_ct (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Proof.AesGcm.sealRoundsPost, sealPPC64LE, sealPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
      stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

/-- `tag` at `0x5000`, `tag_len` 0 and the working space at `0x6000`, the stack arguments. -/
def openSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9061 then 0x50 else bif Nat.beq a.toNat 0x9071 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9060, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 2560⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low 32 bits
of `r3`; and `open`'s public data include its leak, whether it succeeds (for
`rounds` of 10, 12 or 14). -/
theorem open_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target «open» (Proof.AesGcm.openScratchContract PPC64LE.abi) :=
  Verified.of_correct open_correct open_ct
    { pre := by
        sig_implies_pre [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          openPPC64LE, openPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Proof.AesGcm.openRoundsPost, PPC64LE.abi,
          PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
        simp only [openPPC64LE] at h
        intro _
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openLeak, openPPC64LE,
          openPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD,
          List.range, List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
          · exact a0
          · exact a1
          · exact a2
        · have e₁ : ¬((s₁.gpr .r4).toNat = 10 ∨ (s₁.gpr .r4).toNat = 12 ∨ (s₁.gpr .r4).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .r4).toNat = 10 ∨ (s₂.gpr .r4).toNat = 12 ∨ (s₂.gpr .r4).toNat = 14) ↔ False :=
            ⟨fun x => x (h4 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := by
        sig_implies_sat [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          openPPC64LE, openPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
          [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.AesGcm.PPC64LE

end

end


/-!
# AES-GCM on PPC64LE, with its working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of 2592 bytes that allocates it
(`Verified.stackScratch`): its arguments all arrive in registers, the
working space in the next one.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    PPC64LE.abi, PPC64LE.argRegs] [initFrameSat] using initFrameSat

theorem init_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 init)
      (Spec.Gcm.initContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratchKept (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre PPC64LE.abi.ptrBits) (post := Spec.Gcm.initPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2592) init_verified (by decide) (by decide)
    (Proof.AesGcm.initPre_local _) (Proof.AesGcm.initPost_local _) initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩]

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    PPC64LE.abi, PPC64LE.argRegs] [streamInitFrameSat] using streamInitFrameSat

theorem streamInit_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r7 streamInit)
      (Spec.Gcm.streamInitContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratchKept (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamInit_verified (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.AesGcm.streamInitPost_local _)
    streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r6 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩]

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    PPC64LE.abi, PPC64LE.argRegs] [streamAadFrameSat] using streamAadFrameSat

theorem streamAad_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8 streamAad)
      (Spec.Gcm.streamAadContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratchKept (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamAad_verified (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.AesGcm.streamAadPost_local _)
    streamAadFrameSat_pre

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space. -/
def streamCryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Proof.AesGcm.streamEncryptRoundsContract PPC64LE.abi 2592).pre s := by
  implies_sat [Proof.AesGcm.streamEncryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Proof.AesGcm.streamEncryptRoundsPost, PPC64LE.abi, PPC64LE.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamEncrypt_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 streamEncrypt)
      (Proof.AesGcm.streamEncryptRoundsContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratchKept (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre PPC64LE.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamEncrypt_verified (by decide) (by decide)
    (Proof.AesGcm.streamTextPre_local _) (Proof.AesGcm.streamEncryptPost_local _) streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Proof.AesGcm.streamDecryptRoundsContract PPC64LE.abi 2592).pre s := by
  implies_sat [Proof.AesGcm.streamDecryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Proof.AesGcm.streamDecryptRoundsPost, PPC64LE.abi, PPC64LE.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamDecrypt_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 streamDecrypt)
      (Proof.AesGcm.streamDecryptRoundsContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratchKept (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre PPC64LE.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamDecrypt_verified (by decide) (by decide)
    (Proof.AesGcm.streamTextPre_local _) (Proof.AesGcm.streamDecryptPost_local _) streamDecryptFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Proof.AesGcm.streamFinishRoundsContract PPC64LE.abi 2592).pre s := by
  implies_sat [Proof.AesGcm.streamFinishRoundsContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Proof.AesGcm.streamFinishRoundsPost, PPC64LE.abi, PPC64LE.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9 streamFinish)
      (Proof.AesGcm.streamFinishRoundsContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratchKept (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamFinishPre PPC64LE.abi.ptrBits)
    (post := Proof.AesGcm.streamFinishRoundsPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamFinish_verified (by decide) (by decide)
    (Proof.AesGcm.streamFinishPre_local _) (Proof.AesGcm.streamFinishPost_local _) finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Proof.AesGcm.streamVerifyRoundsContract PPC64LE.abi 2592).pre s := by
  implies_sat [Proof.AesGcm.streamVerifyRoundsContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Proof.AesGcm.streamVerifyRoundsPost, PPC64LE.abi, PPC64LE.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 streamVerify)
      (Proof.AesGcm.streamVerifyRoundsContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratchKept (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamVerifyPre PPC64LE.abi.ptrBits)
    (post := Proof.AesGcm.streamVerifyRoundsPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamVerify_verified (by decide) (by decide)
    (Proof.AesGcm.streamVerifyPre_local _) (Proof.AesGcm.streamVerifyPost_local _) verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, without the working
space: `tag` alone on the stack. -/
def sealFrameSat : State where
  gpr := sealSat.gpr
  lr := 0
  sp := 0x9000
  mem := sealSat.mem
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9060, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩]

theorem sealFrameSat_pre : ∃ s, (Proof.AesGcm.sealRoundsContract PPC64LE.abi 2672).pre s := by
  implies_sat [Proof.AesGcm.sealRoundsContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Proof.AesGcm.sealRoundsPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

/-- `seal`, whose `tag` arrives on the stack: the frame copies it, then the
working space's address, above its stack pointer (`Verified.stackScratchArgs`). -/
theorem seal_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 1 Impl.AesGcm.PPC64LE.SealFused.seal)
      (Proof.AesGcm.sealRoundsContract PPC64LE.abi 2672) :=
  PPC64LE.Verified.stackScratchArgsKept (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.sealPre PPC64LE.abi.ptrBits) (post := Proof.AesGcm.sealRoundsPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2672) (m := 1) sealFused_verified (by decide) (by decide)
    (Proof.AesGcm.sealPre_local _) (Proof.AesGcm.sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def openFrameSat : State where
  gpr := openSat.gpr
  lr := 0
  sp := 0x9000
  mem := openSat.mem
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9060, 16⟩]
  wr := [⟨0x4000, 0⟩]

theorem openFrameSat_pre : ∃ s, (Proof.AesGcm.openRoundsContract PPC64LE.abi 2688).pre s := by
  implies_sat [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak,
    PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

/-- `open`, whose `tag` and `tag_len` arrive on the stack, as `seal`'s `tag` does. -/
theorem open_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 «open»)
      (Proof.AesGcm.openRoundsContract PPC64LE.abi 2688) :=
  PPC64LE.Verified.stackScratchArgsKept (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.openPre PPC64LE.abi.ptrBits) (post := Proof.AesGcm.openRoundsPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2688) (m := 2) (leak := some (Spec.Gcm.openLeak PPC64LE.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesGcm.openPre_local _) (Proof.AesGcm.openPost_local _)
    openFrameSat_pre (hleak := Proof.AesGcm.openLeak_local _)

end VG.Proof.AesGcm.PPC64LE
