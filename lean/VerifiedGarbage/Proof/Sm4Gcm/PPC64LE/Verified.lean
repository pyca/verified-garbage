module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Init
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.InitCT
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTCryptFn
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTFin
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTVerify
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Seal
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTSeal
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Open
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTOpen
import VerifiedGarbage.Proof.Framework.SigEval

/-!
# SM4-GCM on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Sm4/Gcm/Contract.lean` with AES-GCM's working space (320 doublewords)
and SM4's (`sm4`, 408) as the last two arguments (`scratch2`; with no
stack: the code calls nothing, and each function saves the link register in
`W`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE

/-- The shared contract of `sig`, with AES-GCM's working space `nm` and
SM4's `sm4` as two more arguments, whatever they hold. -/
abbrev scratch2 (sig : Sig) (nm : String) (pre : Curry (sig.words PPC64LE.abi.ptrBits) (Mem → Prop))
    (post : sig.Post PPC64LE.abi.ptrBits)
    (leak : Option (Curry (sig.words PPC64LE.abi.ptrBits) (Mem → List Nat)) := none) : Contract isa :=
  Sig.scratchContract PPC64LE.abi (sig.withScratch nm .u64 320) "sm4" .u64 408
    (Curry.withScratch PPC64LE.abi.ptrBits nm .u64 320 sig.params pre)
    (Curry.withScratch PPC64LE.abi.ptrBits nm .u64 320 sig.params post) true 0
    (leak.map (Curry.withScratch PPC64LE.abi.ptrBits nm .u64 320 sig.params))

theorem init_correct (s : State) (hs : initPPC64LE.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initPPC64LE.post s s' :=
  init_wp hs

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

theorem seal_correct (s : State) (hs : sealPPC64LE.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealPPC64LE.post s s' :=
  seal_wp hs

theorem open_correct (s : State) (hs : openPPC64LE.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openPPC64LE.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions (with empty buffers) -/

def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | .r6 => 0x6000 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩, ⟨0x6000, 3264⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r7 => 0x2000 | .r9 => 0x4000 | .r10 => 0x6000 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩, ⟨0x6000, 3264⟩]

def finSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r7 => 0x5000 | .r8 => 0x4000 | .r9 => 0x6000 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩, ⟨0x6000, 3264⟩]

def verSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r7 => 0x5000 | .r9 => 0x4000 | .r10 => 0x6000 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩, ⟨0x6000, 3264⟩]

/-! ## The shared contracts -/

theorem init_verified :
    Verified PPC64LE.target init (scratch2 Spec.Sm4.Gcm.initSig "scratch" (Curry.const (fun _ => True) _)
      (Spec.Sm4.Gcm.initPost PPC64LE.abi.ptrBits)) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.initSig,
      Spec.Sm4.Gcm.initPost, initPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [initSat] using initSat)

theorem streamEncrypt_verified :
    Verified PPC64LE.target streamEncrypt (scratch2 Spec.Sm4.Gcm.streamCryptSig "scratch"
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamEncryptPost PPC64LE.abi.ptrBits)) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    sig_implies [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.streamCryptSig,
      Spec.Sm4.Gcm.streamEncryptPost, streamEncryptPPC64LE, streamCryptPre, streamCryptPub, PPC64LE.abi,
      PPC64LE.argRegs] [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified :
    Verified PPC64LE.target streamDecrypt (scratch2 Spec.Sm4.Gcm.streamCryptSig "scratch"
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamDecryptPost PPC64LE.abi.ptrBits)) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    sig_implies [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.streamCryptSig,
      Spec.Sm4.Gcm.streamDecryptPost, streamDecryptPPC64LE, streamCryptPre, streamCryptPub, PPC64LE.abi,
      PPC64LE.argRegs] [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified :
    Verified PPC64LE.target streamFinish (scratch2 Spec.Sm4.Gcm.streamFinishSig "work"
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamFinishPost PPC64LE.abi.ptrBits)) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    sig_implies [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.streamFinishSig,
      Spec.Sm4.Gcm.streamFinishPost, streamFinishPPC64LE, finPre, PPC64LE.abi, PPC64LE.argRegs]
      [finSat] using finSat)

theorem streamVerify_verified :
    Verified PPC64LE.target streamVerify (scratch2 Spec.Sm4.Gcm.streamVerifySig "work"
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamVerifyPost PPC64LE.abi.ptrBits)) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    sig_implies [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.streamVerifySig,
      Spec.Sm4.Gcm.streamVerifyPost, streamVerifyPPC64LE, verPre, PPC64LE.abi, PPC64LE.argRegs]
      [verSat] using verSat)

/-- The working space at `0x6000` and SM4's at `0x7000`, the stack arguments. -/
def sealSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | .r8 => 0x2800 | .r10 => 0x5000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9061 then 0x60 else bif Nat.beq a.toNat 0x9069 then 0x70 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9060, 16⟩]
  wr := [⟨0x2800, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩, ⟨0x7000, 3264⟩]

theorem seal_verified :
    Verified PPC64LE.target «seal» (scratch2 Spec.Sm4.Gcm.sealSig "work" (Curry.const (fun _ => True) _)
      (Spec.Sm4.Gcm.sealPost PPC64LE.abi.ptrBits)) :=
  Verified.of_correct seal_correct seal_ct (by
    sig_implies [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.sealSig,
      Spec.Sm4.Gcm.sealPost, sealPPC64LE, sealPre, onePub, args, PPC64LE.abi, PPC64LE.argRegs,
      stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

/-- `tag_len` 0, the working space at `0x6000` and SM4's at `0x7000`, the stack arguments. -/
def openSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | .r8 => 0x2800 | .r10 => 0x5000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9069 then 0x60 else bif Nat.beq a.toNat 0x9071 then 0x70 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9060, 24⟩]
  wr := [⟨0x2800, 0⟩, ⟨0x6000, 2560⟩, ⟨0x7000, 3264⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low 32 bits
of `r3`; and `open`'s public data include its leak, whether it succeeds. -/
theorem open_verified :
    Verified PPC64LE.target «open» (scratch2 Spec.Sm4.Gcm.openSig "work" (Curry.const (fun _ => True) _)
      (Spec.Sm4.Gcm.openPost PPC64LE.abi.ptrBits) (some (Spec.Sm4.Gcm.openLeak PPC64LE.abi.ptrBits))) :=
  Verified.of_correct open_correct open_ct
    { pre := by
        sig_implies_pre [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.openSig,
          openPPC64LE, openPre, onePub, args, PPC64LE.abi, PPC64LE.argRegs,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.openSig,
          Spec.Sm4.Gcm.openPost, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range,
          List.range.loop]
        simp only [openPPC64LE] at h
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.openSig,
          Spec.Sm4.Gcm.openLeak, openPPC64LE, openPre, onePub, args, PPC64LE.abi, PPC64LE.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, leak_bool hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
      sat := by
        sig_implies_sat [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.openSig,
          openPPC64LE, openPre, onePub, args, PPC64LE.abi, PPC64LE.argRegs,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
          [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.Sm4Gcm.PPC64LE
