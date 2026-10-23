module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesGcm.PPC64LE
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

theorem streamInit_correct (s : State) (hs : streamInitPPC64LE.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ streamInitPPC64LE.post s s' :=
  streamInit_wp hs

theorem streamAad_correct (s : State) (hs : streamAadPPC64LE.pre s) :
    ∃ t s', Exec isa streamAad s t s' ∧ abiPreserved s s' ∧ streamAadPPC64LE.post s s' :=
  streamAad_wp hs

theorem streamEncrypt_correct (s : State) (hs : streamEncryptPPC64LE.pre s) :
    ∃ t s', Exec isa streamEncrypt s t s' ∧ abiPreserved s s' ∧ streamEncryptPPC64LE.post s s' :=
  streamEncrypt_wp hs

theorem streamDecrypt_correct (s : State) (hs : streamDecryptPPC64LE.pre s) :
    ∃ t s', Exec isa streamDecrypt s t s' ∧ abiPreserved s s' ∧ streamDecryptPPC64LE.post s s' :=
  streamDecrypt_wp hs

theorem streamFinish_correct (s : State) (hs : streamFinishPPC64LE.pre s) :
    ∃ t s', Exec isa streamFinish s t s' ∧ abiPreserved s s' ∧ streamFinishPPC64LE.post s s' :=
  streamFinish_wp hs

theorem streamVerify_correct (s : State) (hs : streamVerifyPPC64LE.pre s) :
    ∃ t s', Exec isa streamVerify s t s' ∧ abiPreserved s s' ∧ streamVerifyPPC64LE.post s s' :=
  streamVerify_wp hs

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

theorem streamInit_verified :
    Verified PPC64LE.target streamInit (Proof.AesGcm.streamInitScratchContract PPC64LE.abi) :=
  Verified.of_correct streamInit_correct streamInit_ct (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig,
      Spec.Gcm.streamInitPost, streamInitPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [streamInitSat] using streamInitSat)

theorem streamAad_verified :
    Verified PPC64LE.target streamAad (Proof.AesGcm.streamAadScratchContract PPC64LE.abi) :=
  Verified.of_correct streamAad_correct streamAad_ct (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig,
      Spec.Gcm.streamAadPost, streamAadPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [streamAadSat] using streamAadSat)

theorem streamEncrypt_verified :
    Verified PPC64LE.target streamEncrypt (Proof.AesGcm.streamEncryptScratchContract PPC64LE.abi) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig,
      Spec.Gcm.streamTextPre, Spec.Gcm.streamEncryptPost, streamEncryptPPC64LE, streamCryptPre,
      streamCryptPub, rounds, PPC64LE.abi, PPC64LE.argRegs] [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified :
    Verified PPC64LE.target streamDecrypt (Proof.AesGcm.streamDecryptScratchContract PPC64LE.abi) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig,
      Spec.Gcm.streamTextPre, Spec.Gcm.streamDecryptPost, streamDecryptPPC64LE, streamCryptPre,
      streamCryptPub, rounds, PPC64LE.abi, PPC64LE.argRegs] [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified :
    Verified PPC64LE.target streamFinish (Proof.AesGcm.streamFinishScratchContract PPC64LE.abi) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig,
      Spec.Gcm.streamFinishPre, Spec.Gcm.streamFinishPost, streamFinishPPC64LE, finPre, rounds, PPC64LE.abi,
      PPC64LE.argRegs] [finSat] using finSat)

theorem streamVerify_verified :
    Verified PPC64LE.target streamVerify (Proof.AesGcm.streamVerifyScratchContract PPC64LE.abi) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    sig_implies [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
      Spec.Gcm.streamVerifyPre, Spec.Gcm.streamVerifyPost, streamVerifyPPC64LE, verPre, rounds, PPC64LE.abi,
      PPC64LE.argRegs] [verSat] using verSat)

end VG.Proof.AesGcm.PPC64LE
