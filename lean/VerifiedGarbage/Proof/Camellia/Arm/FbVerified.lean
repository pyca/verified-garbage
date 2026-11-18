module

public import VerifiedGarbage.Proof.Camellia.Arm.Keyed
public import VerifiedGarbage.Proof.Camellia.FbScratch
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
public import VerifiedGarbage.Impl.Camellia.Arm.Fb
public import VerifiedGarbage.Proof.Modes.Arm.Cbc
public import VerifiedGarbage.Proof.Modes.Arm.WideModes
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Camellia.Arm.Keyed
meta import VerifiedGarbage.Proof.Camellia.FbScratch
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Impl.Camellia.Arm.Fb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Modes.Arm.WideModes
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# Camellia-OFB and Camellia-CFB128 on ARMv7 meet their contracts

The generic OFB and CFB encryption one block at a time, over the two
functions that split Camellia's ECB encryption, the table of subkeys built
once in the scratch buffer (`Proof.Modes.Arm.seqK_verified` with
`keyedSpec .encrypt`, `Keyed.lean`), meet the contracts with a scratch
buffer of 349 words (`Proof.Camellia.ofbScratchContract`, …), which holds
their working space, with the 8 bytes of stack of the call's push; the
`_framed` theorems keep the buffer on the stack, zeroed on return: 2816
bytes more. CFB decryption is a group of blocks at a time over the ECB
function itself (`Proof.Modes.Arm.seqW_verified` with `ecbSpec .encrypt`, a
core taking the number of rounds), with a scratch buffer of 9 words, the
2816 bytes of stack the ECB function uses and the 128 bytes of the groups'
buffer.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Impl.Camellia.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- A state satisfying the precondition with the scratch buffer (no blocks):
the schedule at `0x1000`, 18 rounds, the IV at `0x2000`, the data at
`0x3000`, and `n = 0` and the scratch buffer's address `0` (the stack
arguments, in memory that is zero). -/
def fbSat (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 18 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩, ⟨0, 72⟩]

/-- A state satisfying the functions' precondition (no blocks). -/
def fbFrameSat (len : Nat) : State :=
  { fbSat len with rd := [⟨0x1000, 272⟩, ⟨0x8000, 4⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩] }

/-- `fbSat`, with the scratch buffer of the functions that keep the table of
subkeys in it. -/
def fbSatK (len : Nat) : State := { fbSat len with wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩, ⟨0, 2792⟩] }

theorem ofbTaint : SeqTaintK (scrCore .encrypt) VG.Impl.Modes.Arm.ofb :=
  ⟨⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩,
    ⟨_, by native_taint_decide⟩⟩, ⟨_, by native_taint_decide⟩⟩

theorem ofb_implies : (seqArm (scrCore .encrypt) (scrSpec .encrypt) VG.Impl.Modes.Arm.ofb).Implies
    (Proof.Camellia.ofbScratchContract Arm.abi 349 8) where
  pre s h := seqArm_pre_rwR rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbSig, Spec.Camellia.ofbPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Proof.Camellia.ofbPostSk, Spec.Camellia.ofbSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro hR
    have e := ofb_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := scrCore .encrypt) rfl s
    simp only [show (scrCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [scrSpec, dirCipher, rsel_eq hR, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbSig, Spec.Camellia.ofbPre, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fbSatK, fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSatK 0

theorem ofb_verified : Verified Arm.target ofb (Proof.Camellia.ofbScratchContract Arm.abi 349 8) :=
  seqK_verified (keyedSpec .encrypt) (ofb_ok _) ofbTaint ofb_implies

theorem ofbFrameSat : ∃ s, (Proof.Camellia.ofbContractSk Arm.abi 2824).pre s := by
  implies_sat [Proof.Camellia.ofbContractSk, Spec.Camellia.ofbSig, Spec.Camellia.ofbPre, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using fbFrameSat 0

/-- `ofb`, with its scratch buffer on the stack (zeroed on return). -/
theorem ofb_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 ofb)
      (Spec.Camellia.ofbContract Arm.abi 2824) :=
  Proof.Camellia.ofb_of_sk <|
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.ofbSig) (nm := "scratch") (e := .u64) (n := 349)
    (pre := Spec.Camellia.ofbPre Arm.abi.ptrBits) (post := Proof.Camellia.ofbPostSk Arm.abi.ptrBits)
    (wa := true) (stack := 8) (m := 1) (bytes := 2816)
    ofb_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.ofbPre_local _) (Proof.Camellia.ofbPost_local _) (Proof.Camellia.ofbPostOut_local _) ofbFrameSat

theorem cfbEncryptTaint : SeqTaintK (scrCore .encrypt) cfbEnc :=
  ⟨⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩,
    ⟨_, by native_taint_decide⟩⟩, ⟨_, by native_taint_decide⟩⟩

theorem cfbEncrypt_implies : (seqArm (scrCore .encrypt) (scrSpec .encrypt) cfbEnc).Implies
    (Proof.Camellia.cfbEncScratchContract Arm.abi 349 8) where
  pre s h := seqArm_pre_rwR rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Proof.Camellia.cfbEncryptPostSk, Spec.Camellia.cfbSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro hR
    have e := cfbEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := scrCore .encrypt) rfl s
    simp only [show (scrCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [scrSpec, dirCipher, rsel_eq hR, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fbSatK, fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSatK 0

theorem cfbEncrypt_verified : Verified Arm.target cfbEncrypt (Proof.Camellia.cfbEncScratchContract Arm.abi 349 8) :=
  seqK_verified (keyedSpec .encrypt) (cfbEnc_ok _) cfbEncryptTaint cfbEncrypt_implies

theorem cfbEncryptFrameSat : ∃ s, (Proof.Camellia.cfbEncryptContractSk Arm.abi 2824).pre s := by
  implies_sat [Proof.Camellia.cfbEncryptContractSk, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using fbFrameSat 0

/-- `cfbEncrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 cfbEncrypt)
      (Spec.Camellia.cfbEncryptContract Arm.abi 2824) :=
  Proof.Camellia.cfbEncrypt_of_sk <|
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64) (n := 349)
    (pre := Spec.Camellia.cfbPre Arm.abi.ptrBits) (post := Proof.Camellia.cfbEncryptPostSk Arm.abi.ptrBits)
    (wa := true) (stack := 8) (m := 1) (bytes := 2816)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.cfbPre_local _) (Proof.Camellia.cfbEncryptPost_local _) (Proof.Camellia.cfbEncryptPostOut_local _) cfbEncryptFrameSat

theorem cfbDecryptTaint : SeqTaint (ecbCore .encrypt) cfbDec :=
  ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

/-- The taint checks of the code between the calls of the groups. -/
theorem cfbDecryptWideTaint : WideTaint (ecbCore .encrypt) cfbDecW wideLevels wideBuf :=
  ⟨fun lg h => by
      simp only [wideLevels, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;>
        exact ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩,
    ⟨_, by native_taint_decide⟩⟩

theorem cfbDecrypt_implies :
    (seqArm (ecbCore .encrypt) ((ecbSpec .encrypt).deeper wideBuf rfl) cfbDec).Implies
      (Proof.Camellia.cfbDecScratchContract Arm.abi 9 2944) where
  pre s h := seqArm_pre_rwR rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Proof.Camellia.cfbDecryptPostSk, Spec.Camellia.cfbSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro hR
    have e := cfbDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, CoreSpec.deeper, dirCipher, rsel_eq hR, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbSat 0

/-- `cfbDecrypt`, in groups of blocks: the 2816 bytes of stack of the ECB function and the 128 of the groups' buffer. -/
theorem cfbDecrypt_verified : Verified Arm.target cfbDecrypt (Proof.Camellia.cfbDecScratchContract Arm.abi 9 2944) :=
  seqW_verified rfl (ecbSpec .encrypt) (cfbDec_ok _) cfbDecryptTaint wideBuf_ok (cfbDecW_levels rfl) cfbDecryptWideTaint cfbDecrypt_implies

theorem cfbDecryptFrameSat : ∃ s, (Proof.Camellia.cfbDecryptContractSk Arm.abi 3032).pre s := by
  implies_sat [Proof.Camellia.cfbDecryptContractSk, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using fbFrameSat 0

/-- `cfbDecrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 cfbDecrypt)
      (Spec.Camellia.cfbDecryptContract Arm.abi 3032) :=
  Proof.Camellia.cfbDecrypt_of_sk <|
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Spec.Camellia.cfbPre Arm.abi.ptrBits) (post := Proof.Camellia.cfbDecryptPostSk Arm.abi.ptrBits)
    (wa := true) (stack := 2944) (m := 1) (bytes := 88)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.cfbPre_local _) (Proof.Camellia.cfbDecryptPost_local _) (Proof.Camellia.cfbDecryptPostOut_local _) cfbDecryptFrameSat

end VG.Proof.Camellia.Arm
