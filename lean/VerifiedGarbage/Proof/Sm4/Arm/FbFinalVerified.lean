module

public import VerifiedGarbage.Proof.Modes.Arm.Core
public import VerifiedGarbage.Proof.Sm4.Arm.EcbCall
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Proof.Sm4.Arm.Ecb
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Modes.Arm.SeqFinalCT
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Impl.Sm4.Arm.FbFinal
public import VerifiedGarbage.Spec.Sm4.CfbFinal
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Modes.Arm.Core
meta import VerifiedGarbage.Proof.Sm4.Arm.EcbCall
meta import VerifiedGarbage.Spec.Sm4.Cbc
meta import VerifiedGarbage.Proof.Sm4.Arm.Ecb
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Modes.Arm.SeqFinalCT
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Impl.Sm4.Arm.FbFinal
meta import VerifiedGarbage.Spec.Sm4.CfbFinal
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# SM4-CFB128 of a message's last piece on ARMv7 meets its contracts

The generic CFB over a message's last piece (`Proof.Modes.Arm.seqFinal_verified`)
over Sm4's ECB function (`ecbSpec .encrypt`) meets the contracts with a scratch
buffer of 9 words, with the 1480 bytes of stack the ECB function uses, with
the specification's results (`Proof.Modes.Arm.cfbEncFinal_post`, …); the
`_framed` theorems keep the buffer on the stack, zeroed on return: 80 bytes
more.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)

/-- The cipher of a direction, on blocks as lists. -/
def dirCipher : Dir → Spec.Sm4.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.Sm4.cipher
  | .decrypt => Spec.Sm4.invCipher

theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) :
    blocksOf 16 m p n = (Spec.Sm4.blocksAt m p n).map Vector.toList := by
  simp only [VG.Proof.Modes.blocksOf, Spec.Sm4.blocksAt, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  apply List.ext_getElem (by simp [bytesAt])
  intro j h₁ _
  simp [bytesAt, Spec.Sm4.blockAt]

theorem ofFn_getD (v : Spec.Sm4.Block) : (Vector.ofFn fun i : Fin 16 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi; simp [List.getD_eq_getElem?_getD]

/-- The block function of a direction. -/
def dirBlock : Dir → Spec.Sm4.Schedule → Spec.Sm4.Block → Spec.Sm4.Block
  | .encrypt => Spec.Sm4.encryptBlock
  | .decrypt => Spec.Sm4.decryptBlock

theorem dirCipher_toList (dir : Dir) (k : Spec.Sm4.Schedule) (v : Spec.Sm4.Block) :
    dirCipher dir k v.toList = (dirBlock dir k v).toList := by
  cases dir <;> simp only [dirCipher, dirBlock, Spec.Sm4.cipher, Spec.Sm4.invCipher, ofFn_getD]

theorem ecb_dir (dir : Dir) (k : Spec.Sm4.Schedule) (xs : List Spec.Sm4.Block) :
    Spec.Sm4.ecb k (specDirArm dir) xs = xs.map (dirBlock dir k) := by
  cases dir <;> rfl

theorem ecb_stack (dir : Dir) : VG.Arm.FrameStack.armStack (ecbCall dir) ≤ 1480 := by
  cases dir <;> decide +kernel

/-- SM4's ECB function in the direction `dir`, as the modes' core. -/
def ecbSpec (dir : Dir) : CoreSpec (ecbCore dir) where
  keyLen := 128
  stack := 1480
  ciphAt m K _ := dirCipher dir (Spec.Sm4.scheduleAt m K)
  contract := Spec.Sm4.ecbContract Arm.abi (specDirArm dir) 1480
  correct := (ecbCall_verified dir).1
  ct := (ecbCall_verified dir).2.1
  depth := ecb_stack dir
  pre_of _ s h := by
    obtain ⟨stk, rd, wr, kd, bk, bd, fK, fD, -⟩ := h
    sig_pre [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨stk, by have := s.sp.isLt; omega, rd, wr, kd, bk, bd, fK, fD⟩
  post_of _ s s' _ h := by
    sig_post [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    show blocksOf 16 _ _ _ = (blocksOf 16 _ _ _).map _
    rw [show (ecbCore dir).dReg = .r1 from rfl, show (ecbCore dir).nReg = .r2 from rfl]
    simp only [State.addr]
    rw [blocksOf_eq, blocksOf_eq, h, ecb_dir, List.map_map, List.map_map]
    exact List.map_congr_left fun v _ => (dirCipher_toList dir _ v).symm
  pub_of _ s₁ s₂ h0 h1 h2 h3 _ := by
    sig_pub [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h0, h1, h2, h3⟩
  ciphAt_congr h := by simp only [Proof.Sm4.scheduleAt_congr h]
  ciphAt_R _ _ _ _ _ := rfl
  cipher_len m K _ b _ := by cases dir <;> (simp [dirCipher, Spec.Sm4.cipher, Spec.Sm4.invCipher]; rfl)
  bw_pos := by cases dir <;> decide
  bw_le := by cases dir <;> decide
  bs_enc := by cases dir <;> decide

/-- A state satisfying the precondition with the scratch buffer (one block at
`0x3000`), the IV read and written. -/
def fbSat (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩, ⟨0, 72⟩]

/-- A state satisfying the functions' precondition. -/
def fbFrameSat (len : Nat) : State := { fbSat len with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩] }


/-- Sm4's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.Sm4.cipher (Spec.Sm4.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 128 16

theorem ciphAt_congr {m₁ m₂ : Mem} {k : Addr}
    (h : ∀ i < 128 * Elem.size .u8, m₂ (k + BitVec.ofNat 64 i) = m₁ (k + BitVec.ofNat 64 i)) :
    ciphAt m₂ k = ciphAt m₁ k := by
  simp only [ciphAt, Proof.Sm4.scheduleAt_congr (m := m₁) (m' := m₂) h]

theorem cfbEncryptFinalTaint : FinalTaint (ecbCore .encrypt) cfbEnc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbEncryptFinal_implies : (seqFinalArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbEnc).Implies
    (Sig.scratchContract Arm.abi finalSig "scratch" .u64 9 (Curry.const (fun _ => True) _)
      (Proof.Modes.encFinalPost ciphAt 16 Arm.abi.ptrBits) true 1480) where
  pre s h := seqArm_pre_rw (M := byteMode) rfl (len := fun n => n) (fun n => (Nat.mul_one n).symm) (by
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbEncFinal_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := (ecbCore .encrypt)) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub (M := byteMode) rfl h
  sat := by
    sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using fbSat 1

theorem cfbEncryptFinal_verified : Verified Arm.target cfbEncryptFinal
    (Sig.scratchContract Arm.abi finalSig "scratch" .u64 9 (Curry.const (fun _ => True) _)
      (Proof.Modes.encFinalPost ciphAt 16 Arm.abi.ptrBits) true 1480) :=
  seqFinal_verified (ecbSpec .encrypt) (cfbEnc_finalOk _ (by decide) (by decide) (by decide)) cfbEncryptFinalTaint
    cfbEncryptFinal_implies

theorem cfbDecryptFinalTaint : FinalTaint (ecbCore .encrypt) cfbDecF :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbDecryptFinal_implies : (seqFinalArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbDecF).Implies
    (Sig.scratchContract Arm.abi finalSig "scratch" .u64 9 (Curry.const (fun _ => True) _)
      (Proof.Modes.decFinalPost ciphAt 16 Arm.abi.ptrBits) true 1480) where
  pre s h := seqArm_pre_rw (M := byteMode) rfl (len := fun n => n) (fun n => (Nat.mul_one n).symm) (by
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbDecFinal_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := (ecbCore .encrypt)) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub (M := byteMode) rfl h
  sat := by
    sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using fbSat 1

theorem cfbDecryptFinal_verified : Verified Arm.target cfbDecryptFinal
    (Sig.scratchContract Arm.abi finalSig "scratch" .u64 9 (Curry.const (fun _ => True) _)
      (Proof.Modes.decFinalPost ciphAt 16 Arm.abi.ptrBits) true 1480) :=
  seqFinal_verified (ecbSpec .encrypt) (cfbDecF_finalOk _ (by decide) (by decide) (by decide)) cfbDecryptFinalTaint
    cfbDecryptFinal_implies

theorem cfbEncryptFinalFrameSat : ∃ s, (Spec.Sm4.cfbEncryptFinalContract Arm.abi 1560).pre s := by
  implies_sat [Spec.Sm4.cfbEncryptFinalContract, Spec.Sm4.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

/-- `cfbEncryptFinal`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cfbEncryptFinal)
      (Spec.Sm4.cfbEncryptFinalContract Arm.abi 1560) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.cfbFinalSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Modes.encFinalPost ciphAt 16 Arm.abi.ptrBits) (wa := true) (stack := 1480) (m := 0) (bytes := 80)
    cfbEncryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Modes.encFinalPostIn_local _ ciphAt_congr)
    (Proof.Modes.encFinalPost_local _) cfbEncryptFinalFrameSat

theorem cfbDecryptFinalFrameSat : ∃ s, (Spec.Sm4.cfbDecryptFinalContract Arm.abi 1560).pre s := by
  implies_sat [Spec.Sm4.cfbDecryptFinalContract, Spec.Sm4.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

/-- `cfbDecryptFinal`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cfbDecryptFinal)
      (Spec.Sm4.cfbDecryptFinalContract Arm.abi 1560) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.cfbFinalSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Modes.decFinalPost ciphAt 16 Arm.abi.ptrBits) (wa := true) (stack := 1480) (m := 0) (bytes := 80)
    cfbDecryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Modes.decFinalPostIn_local _ ciphAt_congr)
    (Proof.Modes.decFinalPost_local _) cfbDecryptFinalFrameSat

end VG.Proof.Sm4.Arm
