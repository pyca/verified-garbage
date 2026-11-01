module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesGcm.RISCV64
import VerifiedGarbage.Proof.AesGcm.RISCV64.Init
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamInit
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamAad
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTCryptFn
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTFin
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTVerify
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
import VerifiedGarbage.Proof.AesGcm.RISCV64.Open
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTOpen
import VerifiedGarbage.Proof.Framework.SigEval

/-!
# AES-GCM on RISCV64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`), with the 2048 bytes of stack `vg_ghash`'s
frame takes (but for `init`, which does not call it).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

theorem init_correct (s : State) (hs : initRISCV64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initRISCV64.post s s' :=
  init_wp hs

theorem streamInit_correct (s : State) (hs : streamInitRISCV64.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ streamInitRISCV64.post s s' :=
  streamInit_wp hs

theorem streamAad_correct (s : State) (hs : streamAadRISCV64.pre s) :
    ∃ t s', Exec isa streamAad s t s' ∧ abiPreserved s s' ∧ streamAadRISCV64.post s s' :=
  streamAad_wp hs

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
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x2000 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

def streamInitSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamAadSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a3 => 0x2000 | .a5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x3000 | .a5 => 0x2000 | .a7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩]

def finSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x3000 | .a5 => 0x5000 | .a6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩]

def verSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x3000 | .a5 => 0x5000 | .a7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

/-! ## The shared contracts -/

theorem init_verified :
    Verified RISCV64.target init (Proof.AesGcm.initScratchContract RISCV64.abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre,
      Spec.Gcm.initPost, initRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [initSat] using initSat)

theorem streamInit_verified :
    Verified RISCV64.target streamInit (Proof.AesGcm.streamInitScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamInit_correct streamInit_ct (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig,
      Spec.Gcm.streamInitPost, streamInitRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true]
      [streamInitSat] using streamInitSat)

theorem streamAad_verified :
    Verified RISCV64.target streamAad (Proof.AesGcm.streamAadScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamAad_correct streamAad_ct (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig,
      Spec.Gcm.streamAadPost, streamAadRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true]
      [streamAadSat] using streamAadSat)

theorem streamEncrypt_verified :
    Verified RISCV64.target streamEncrypt (Proof.AesGcm.streamEncryptScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig,
      Spec.Gcm.streamTextPre, Spec.Gcm.streamEncryptPost, streamEncryptRISCV64, streamCryptPre,
      streamCryptPub, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified :
    Verified RISCV64.target streamDecrypt (Proof.AesGcm.streamDecryptScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig,
      Spec.Gcm.streamTextPre, Spec.Gcm.streamDecryptPost, streamDecryptRISCV64, streamCryptPre,
      streamCryptPub, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified :
    Verified RISCV64.target streamFinish (Proof.AesGcm.streamFinishScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig,
      Spec.Gcm.streamFinishPre, Spec.Gcm.streamFinishPost, streamFinishRISCV64, finPre, rounds, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [finSat] using finSat)

theorem streamVerify_verified :
    Verified RISCV64.target streamVerify (Proof.AesGcm.streamVerifyScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    sig_implies [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
      Spec.Gcm.streamVerifyPre, Spec.Gcm.streamVerifyPost, streamVerifyRISCV64, verPre, rounds, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [verSat] using verSat)

/-- `tag` at `0x5000` and the working space at `0x6000`, the stack arguments. -/
def sealSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x50 else bif Nat.beq a.toNat 0x9009 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9000, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩]

theorem seal_verified :
    Verified RISCV64.target «seal» (Proof.AesGcm.sealScratchContract RISCV64.abi 2048) :=
  Verified.of_correct seal_correct seal_ct (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Spec.Gcm.sealPost, sealRISCV64, sealPre, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true,
      stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

/-- `tag` at `0x5000`, `tag_len` 0 and the working space at `0x6000`, the stack arguments. -/
def openSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x50 else bif Nat.beq a.toNat 0x9011 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 2560⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low 32 bits
of `a0`; and `open`'s public data include its leak, whether it succeeds (for
`rounds` of 10, 12 or 14). -/
theorem open_verified :
    Verified RISCV64.target «open» (Proof.AesGcm.openScratchContract RISCV64.abi 2048) :=
  Verified.of_correct open_correct open_ct
    { pre := by
        sig_implies_pre [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          openRISCV64, openPre, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPost, RISCV64.abi,
          RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
        simp only [openRISCV64] at h
        intro _
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openLeak, openRISCV64,
          openPre, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD,
          List.range, List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
          · exact a0
          · exact a1
          · exact a2
        · have e₁ : ¬((s₁.gpr .a1).toNat = 10 ∨ (s₁.gpr .a1).toNat = 12 ∨ (s₁.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .a1).toNat = 10 ∨ (s₂.gpr .a1).toNat = 12 ∨ (s₂.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x (h4 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := by
        sig_implies_sat [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          openRISCV64, openPre, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
          [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.AesGcm.RISCV64
