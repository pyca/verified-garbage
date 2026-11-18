module

public import VerifiedGarbage.Proof.Gcm.Arm.Ghash
import VerifiedGarbage.Proof.Sm4Gcm.Arm.InitCT
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTStream
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTCryptFn
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTOpen
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.Impl.Sm4Gcm.Arm
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Fn
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamInit
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamAad
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Seal
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamCrypt
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-! ### `Sm4Gcm.Arm.Verified`, which only this module used -/

section

/-! ### `Sm4Gcm.Arm.Scratch`, which only this module used -/

section

/-!
# SM4-GCM on ARMv7: the functions with their working space as an argument

The ARMv7 SM4-GCM functions keep their 768-byte working space in a frame of
their own (`Verified.stackScratch`, `Verified.regScratch`), around code
proved with the working space as a last argument: `initScratchContract`, …,
`openScratchContract` are the shared contracts with a 768-byte `scratch` (or
`work`) buffer appended, whatever it holds (`Proof/Sm4Gcm/Scratch.lean` has
x86-64's, with 2560 bytes).

The frames also hold a copy of the arguments passed on the stack, which needs
the postconditions to read the memory on entry only within the function's
buffers: `Proof/Sm4Gcm/Scratch.lean` proves it, and
`Proof/AesGcm/Scratch.lean` of `vg_sm4_gcm_stream_init`'s and
`vg_sm4_gcm_stream_aad`'s, which are AES-GCM's.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG.Spec.Sm4.Gcm

/-- `vg_sm4_gcm_init` with `scratch: *mut [u64; 96]`. -/
def initScratchSig : Sig where
  params := initSig.params ++ [("scratch", .array true .u64 96)]

/-- `initContract`, whatever `scratch` is. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSig.contract A
    (post := fun key ctx _scratch => initPost A.ptrBits key ctx)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_init` with `scratch: *mut [u64; 96]`. -/
def streamInitScratchSig : Sig where
  params := Spec.Gcm.streamInitSig.params ++ [("scratch", .array true .u64 96)]

/-- `Spec.Gcm.streamInitContract`, whatever `scratch` is. -/
def streamInitScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamInitScratchSig.contract A
    (post := fun ctx nonce nonceLen state _scratch =>
      Spec.Gcm.streamInitPost A.ptrBits ctx nonce nonceLen state)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_aad` with `scratch: *mut [u64; 96]`. -/
def streamAadScratchSig : Sig where
  params := Spec.Gcm.streamAadSig.params ++ [("scratch", .array true .u64 96)]

/-- `Spec.Gcm.streamAadContract`, whatever `scratch` is. -/
def streamAadScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamAadScratchSig.contract A
    (post := fun ctx state aadLen data len _scratch =>
      Spec.Gcm.streamAadPost A.ptrBits ctx state aadLen data len)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt` with
`scratch: *mut [u64; 96]`. -/
def streamCryptScratchSig : Sig where
  params := streamCryptSig.params ++ [("scratch", .array true .u64 96)]

/-- `streamEncryptContract`, whatever `scratch` is. -/
def streamEncryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptScratchSig.contract A
    (post := fun ctx state aadLen textLen data len _scratch =>
      streamEncryptPost A.ptrBits ctx state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-- `streamDecryptContract`, whatever `scratch` is. -/
def streamDecryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptScratchSig.contract A
    (post := fun ctx state aadLen textLen data len _scratch =>
      streamDecryptPost A.ptrBits ctx state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_finish` with `work: *mut [u64; 96]`. -/
def streamFinishScratchSig : Sig where
  params := streamFinishSig.params ++ [("work", .array true .u64 96)]

/-- `streamFinishContract`, whatever `work` is. -/
def streamFinishScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamFinishScratchSig.contract A
    (post := fun ctx state aadLen textLen tag _work =>
      streamFinishPost A.ptrBits ctx state aadLen textLen tag)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_verify` with `work: *mut [u64; 96]`. -/
def streamVerifyScratchSig : Sig where
  params := streamVerifySig.params ++ [("work", .array true .u64 96)]
  ret := some .u32

/-- `streamVerifyContract`, whatever `work` is. -/
def streamVerifyScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamVerifyScratchSig.contract A
    (post := fun ctx state aadLen textLen tag tagLen _work =>
      streamVerifyPost A.ptrBits ctx state aadLen textLen tag tagLen)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_seal` with `work: *mut [u64; 96]`. -/
def sealScratchSig : Sig where
  params := sealSig.params ++ [("work", .array true .u64 96)]

/-- `sealContract`, whatever `work` is. -/
def sealScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealScratchSig.contract A
    (post := fun ctx nonce nonceLen aad aadLen data len tag _work =>
      sealPost A.ptrBits ctx nonce nonceLen aad aadLen data len tag)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_open` with `work: *mut [u64; 96]`. -/
def openScratchSig : Sig where
  params := openSig.params ++ [("work", .array true .u64 96)]
  ret := some .u32

/-- `openContract`, whatever `work` is. -/
def openScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openScratchSig.contract A
    (post := fun ctx nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPost A.ptrBits ctx nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx nonce nonceLen aad aadLen data len tag tagLen _work =>
      openLeak A.ptrBits ctx nonce nonceLen aad aadLen data len tag tagLen)

end VG.Proof.Sm4Gcm.Arm

end

end


/-!
# SM4-GCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Sm4/Gcm/Contract.lean` with the working space as a last argument
(`Proof/Sm4Gcm/Arm/Scratch.lean`), with 1520 bytes of stack: those of
`vg_sm4_ctr32`'s frame, the most any call uses (`vg_sm4_expand_key` uses
1456, and each call of `vg_ghash` pushes two words).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Impl.Sm4Gcm.Arm

/-- A state with the given registers, the stack pointer at `0x8000`, memory
of zeros (so stack arguments of 0) and the given regions. -/
def mkSat (g : Reg → BitVec 32) (rd wr : List Region) : State where
  gpr := g
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := rd
  wr := wr

/-- A state satisfying `vg_sm4_gcm_init`'s precondition. -/
def initSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 256⟩, ⟨0x3000, 768⟩]

theorem init_verified : Verified Arm.target init (Proof.Sm4Gcm.Arm.initScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.initScratchContract, Proof.Sm4Gcm.Arm.initScratchSig, Spec.Sm4.Gcm.initSig,
      Spec.Sm4.Gcm.initPost, initArm, bel, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [initSat, mkSat] using initSat)

/-- A state satisfying `vg_sm4_gcm_stream_init`'s precondition (with no nonce). -/
def siSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x8000, 4⟩] [⟨0x3000, 80⟩, ⟨0, 768⟩]

theorem streamInit_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamInit (Proof.Sm4Gcm.Arm.streamInitScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamInit_wp hs) streamInit_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.streamInitScratchContract, Proof.Sm4Gcm.Arm.streamInitScratchSig,
      Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost, streamInitArm, bel, arg, args, arg64,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [siSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using siSat)

/-- A state satisfying `vg_sm4_gcm_stream_aad`'s precondition (with no data). -/
def saSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 12⟩] [⟨0x3000, 80⟩, ⟨0, 768⟩]

theorem streamAad_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamAad (Proof.Sm4Gcm.Arm.streamAadScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamAad_wp hs) streamAad_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.streamAadScratchContract, Proof.Sm4Gcm.Arm.streamAadScratchSig,
      Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost, streamAadArm, bel, arg, args, arg64,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [saSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using saSat)

/-- A state satisfying the precondition of `vg_sm4_gcm_stream_encrypt` and `_decrypt` (with no
data, and `scratch` at 0). -/
def scSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 20⟩] [⟨0x3000, 80⟩, ⟨0, 0⟩, ⟨0, 768⟩]

theorem streamEncrypt_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamEncrypt (Proof.Sm4Gcm.Arm.streamEncryptScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamEncrypt_wp hs) streamEncrypt_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.streamEncryptScratchContract, Proof.Sm4Gcm.Arm.streamCryptScratchSig,
      Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, streamEncryptArm, streamCryptPre,
      streamCryptPub, bel, arg, args, arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scSat)

theorem streamDecrypt_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamDecrypt (Proof.Sm4Gcm.Arm.streamDecryptScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamDecrypt_wp hs) streamDecrypt_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.streamDecryptScratchContract, Proof.Sm4Gcm.Arm.streamCryptScratchSig,
      Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, streamDecryptArm, streamCryptPre,
      streamCryptPub, bel, arg, args, arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scSat)

/-- `mkSat`, with the stack argument 2 (at `0x8008`) `0x4000`. -/
def mkSat2 (g : Reg → BitVec 32) (rd wr : List Region) : State :=
  { mkSat g rd wr with mem := fun a => if a = 0x8009 then 0x40 else 0 }

/-- `mkSat`, with the stack argument 3 (at `0x800c`) `0x4000`. -/
def mkSat3 (g : Reg → BitVec 32) (rd wr : List Region) : State :=
  { mkSat g rd wr with mem := fun a => if a = 0x800D then 0x40 else 0 }

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition (with `tag` at `0x4000` and `work`
at 0). -/
def fSat : State :=
  mkSat2 (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 16⟩] [⟨0x3000, 80⟩, ⟨0x4000, 16⟩, ⟨0, 768⟩]

theorem streamFinish_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamFinish (Proof.Sm4Gcm.Arm.streamFinishScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamFinish_wp hs) streamFinish_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.streamFinishScratchContract, Proof.Sm4Gcm.Arm.streamFinishScratchSig,
      Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, streamFinishArm, streamFinishPreArm,
      finPub, bel, arg, args, arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fSat, mkSat2, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using fSat)

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition (with no tag, and `work` at 0). -/
def vSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0x3000, 80⟩, ⟨0, 768⟩]

/-- The postconditions match; the result is the low word of `r1:r0`. -/
theorem streamVerify_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamVerify (Proof.Sm4Gcm.Arm.streamVerifyScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamVerify_wp hs) streamVerify_ct
    { pre := by
        sig_implies_pre [Proof.Sm4Gcm.Arm.streamVerifyScratchContract, Proof.Sm4Gcm.Arm.streamVerifyScratchSig,
          Spec.Sm4.Gcm.streamVerifySig, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args,
          arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.Sm4Gcm.Arm.streamVerifyScratchContract, Proof.Sm4Gcm.Arm.streamVerifyScratchSig,
          Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [streamVerifyArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro iv a c hs ha hc
        rw [e]
        exact h iv a c hs ha hc
      pub := by
        sig_implies_pub [Proof.Sm4Gcm.Arm.streamVerifyScratchContract, Proof.Sm4Gcm.Arm.streamVerifyScratchSig,
          Spec.Sm4.Gcm.streamVerifySig, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args,
          arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Proof.Sm4Gcm.Arm.streamVerifyScratchContract, Proof.Sm4Gcm.Arm.streamVerifyScratchSig,
          Spec.Sm4.Gcm.streamVerifySig, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args,
          arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [vSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using vSat }

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition (with no nonce, additional data or
data, `tag` at `0x4000` and `work` at 0). -/
def oSat : State :=
  mkSat3 (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0, 0⟩, ⟨0x4000, 16⟩, ⟨0, 768⟩]

theorem seal_verified [VG.Proof.Gcm.Arm.GhashLaw] : Verified Arm.target «seal» (Proof.Sm4Gcm.Arm.sealScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => seal_wp hs) seal_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.sealScratchContract, Proof.Sm4Gcm.Arm.sealScratchSig, Spec.Sm4.Gcm.sealSig,
      Spec.Sm4.Gcm.sealPost, sealArm, sealPreArm, onePub, bel, arg, args, arg64, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [oSat, mkSat3, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using oSat)

/-- A state satisfying `vg_sm4_gcm_open`'s precondition (with no nonce, additional data, data
or tag, and `work` at 0). -/
def opSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] [⟨0, 0⟩, ⟨0, 768⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low word of
`r1:r0`; and `open`'s public data include its leak, whether it succeeds. -/
theorem open_verified [VG.Proof.Gcm.Arm.GhashLaw] : Verified Arm.target «open» (Proof.Sm4Gcm.Arm.openScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => open_wp hs) open_ct
    { pre := by
        sig_implies_pre [Proof.Sm4Gcm.Arm.openScratchContract, Proof.Sm4Gcm.Arm.openScratchSig,
          Spec.Sm4.Gcm.openSig, openArm, openPreArm, onePub, bel, arg, args, arg64, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.Sm4Gcm.Arm.openScratchContract, Proof.Sm4Gcm.Arm.openScratchSig, Spec.Sm4.Gcm.openSig,
          Spec.Sm4.Gcm.openPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [openArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.Sm4Gcm.Arm.openScratchContract, Proof.Sm4Gcm.Arm.openScratchSig, Spec.Sm4.Gcm.openSig,
          Spec.Sm4.Gcm.openLeak, openArm, openPreArm, onePub, bel, arg, args, arg64, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, leak_bool hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with
          rfl | rfl | rfl | rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
        · exact a3
        · exact a4
        · exact a5
      sat := by
        sig_implies_sat [Proof.Sm4Gcm.Arm.openScratchContract, Proof.Sm4Gcm.Arm.openScratchSig,
          Spec.Sm4.Gcm.openSig, openArm, openPreArm, onePub, bel, arg, args, arg64, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [opSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using opSat }

end VG.Proof.Sm4Gcm.Arm

end

end


/-!
# SM4-GCM on ARMv7, with its working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it.
`init`'s working space is its third argument, in `r2`: its frame is the 768
bytes of working space (`Verified.regScratch`). That of the others is passed
on the stack: the frames of 784 bytes of `stream_init` and `stream_aad` hold
the copies of the other arguments passed on the stack (none for
`stream_init`, `data` and `len` for `stream_aad`), the buffer's address and
the saved `lr` too (`Verified.stackScratch`); so do the frames of 800 bytes
of `stream_encrypt` and `stream_decrypt`, with copies of their four words of
stack arguments (`text_len`, `data` and `len`), of `stream_finish` (three:
`text_len` and `tag`), of `stream_verify` and `seal` (four) and of `open`
(five). The copies are read only where the postconditions read the buffers
(`Proof/Sm4Gcm/Scratch.lean`, `Arm/Scratch.lean`). Each frame sits on the
1520 bytes of stack the code needs below it.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Impl.Sm4Gcm.Arm

/-- A state satisfying `vg_sm4_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 256⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract Arm.abi 2288).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, mkSat] using initFrameSat

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 768 .r2 init)
    (Spec.Sm4.Gcm.initContract Arm.abi 2288) :=
  Arm.Verified.regScratch (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.initPost Arm.abi.ptrBits)
    (wa := true) (stack := 1520) init_verified (by decide) (by decide) (by decide)
    (fun vs mm m₁ m₂ r hl _ => initPostOut_local _ vs mm m₁ m₂ r hl) initFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩] [⟨0x3000, 80⟩]

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract Arm.abi 2304).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [streamInitFrameSat, mkSat] using streamInitFrameSat

theorem streamInit_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 784 0 streamInit)
      (Spec.Gcm.streamInitContract Arm.abi 2304) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Gcm.streamInitPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 0) streamInit_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.AesGcm.streamInitPost_local _)
    (fun vs mm m₁ m₂ r hl _ => Proof.AesGcm.streamInitPostOut_local _ vs mm m₁ m₂ r hl)
    streamInitFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 8⟩] [⟨0x3000, 80⟩]

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract Arm.abi 2304).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [streamAadFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using streamAadFrameSat

theorem streamAad_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 784 2 streamAad)
      (Spec.Gcm.streamAadContract Arm.abi 2304) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Gcm.streamAadPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 2) streamAad_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.AesGcm.streamAadPost_local _)
    (fun vs mm m₁ m₂ r hl _ => Proof.AesGcm.streamAadPostOut_local _ vs mm m₁ m₂ r hl)
    streamAadFrameSat_pre

/-- A state satisfying the preconditions of `vg_sm4_gcm_stream_encrypt` and
`vg_sm4_gcm_stream_decrypt`, without the working space: their four words of
stack arguments at `0x8000`. -/
def crFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 16⟩] [⟨0x3000, 80⟩, ⟨0, 0⟩]

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamEncryptContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamEncryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamEncryptPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [crFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using crFrameSat

theorem streamEncrypt_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 4 streamEncrypt)
      (Spec.Sm4.Gcm.streamEncryptContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamEncryptPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 4) streamEncrypt_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamEncryptPost_local _)
    (fun vs mm m₁ m₂ r hl _ => streamEncryptPostOut_local _ vs mm m₁ m₂ r hl)
    streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamDecryptContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamDecryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamDecryptPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [crFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using crFrameSat

theorem streamDecrypt_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 4 streamDecrypt)
      (Spec.Sm4.Gcm.streamDecryptContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamDecryptPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 4) streamDecrypt_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamDecryptPost_local _)
    (fun vs mm m₁ m₂ r hl _ => streamDecryptPostOut_local _ vs mm m₁ m₂ r hl)
    streamDecryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition, without the
working space: its three words of stack arguments at `0x8000`. -/
def finFrameSat : State :=
  mkSat2 (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 12⟩] [⟨0x3000, 80⟩, ⟨0x4000, 16⟩]

theorem finFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishContract, Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, mkSat2, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat

theorem streamFinish_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 3 streamFinish)
      (Spec.Sm4.Gcm.streamFinishContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamFinishPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 3) streamFinish_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamFinishPost_local _)
    (fun vs mm m₁ m₂ r hl _ => streamFinishPostOut_local _ vs mm m₁ m₂ r hl) finFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition, without the
working space: its four words of stack arguments at `0x8000`. -/
def verFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 16⟩] [⟨0x3000, 80⟩]

theorem verFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifyContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifyContract, Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [verFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using verFrameSat

theorem streamVerify_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 4 streamVerify)
      (Spec.Sm4.Gcm.streamVerifyContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamVerifyPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 4) streamVerify_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamVerifyPost_local _)
    (fun vs mm m₁ m₂ r hl _ => streamVerifyPostOut_local _ vs mm m₁ m₂ r hl) verFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition, without the working
space: its four words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  mkSat3 (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 16⟩] [⟨0, 0⟩, ⟨0x4000, 16⟩]

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, mkSat3, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 4 «seal»)
      (Spec.Sm4.Gcm.sealContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.sealPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 4) seal_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (sealPost_local _)
    (fun vs mm m₁ m₂ r hl _ => sealPostOut_local _ vs mm m₁ m₂ r hl) sealFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_open`'s precondition, without the working
space: its five words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0, 0⟩]

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost,
    Spec.Sm4.Gcm.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 5 «open»)
      (Spec.Sm4.Gcm.openContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.openPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (leak := some (Spec.Sm4.Gcm.openLeak Arm.abi.ptrBits))
    (m := 5) open_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (openPost_local _)
    (fun vs mm m₁ m₂ r hl _ => openPostOut_local _ vs mm m₁ m₂ r hl) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.Sm4Gcm.Arm
