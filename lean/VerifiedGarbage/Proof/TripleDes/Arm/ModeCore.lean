module

import VerifiedGarbage.Proof.TripleDes.Arm.Frame
public import VerifiedGarbage.Proof.Modes.Arm.Core
public import VerifiedGarbage.Proof.Modes.Arm.Wrap
public import VerifiedGarbage.Impl.TripleDes.Arm.Cbc
public import VerifiedGarbage.Spec.TripleDes.Cbc
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.Arm.Scrub
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Verified
import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.Arm.Frame
meta import VerifiedGarbage.Proof.Modes.Arm.Core
meta import VerifiedGarbage.Proof.Modes.Arm.Wrap
meta import VerifiedGarbage.Impl.TripleDes.Arm.Cbc
meta import VerifiedGarbage.Spec.TripleDes.Cbc
meta import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.TripleDes.CbcBlocks
meta import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Verified
meta import VerifiedGarbage.Proof.TripleDes.Scratch
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# Triple DES's ECB functions on ARMv7 as the modes' core

`ecbSpec d`: what the modes need of Triple DES's ECB cores,
`vg_triple_des_ecb_encrypt_core` and `vg_triple_des_ecb_decrypt_core`
(`Proof.Modes.Arm.CoreSpec`), from the ECB functions' shared contract
(`Spec.TripleDes.ecbContract`, with 1024 bytes of stack) and the proof of
each (`ecb_framed`): the schedule is the 384-byte schedule, and the cipher on
a block is `Spec.TripleDes.cipher` or `Spec.TripleDes.invCipher` of it.

`vg_triple_des_ecb_encrypt` and `vg_triple_des_ecb_decrypt` call the cores in
a frame of 8 bytes (`Core.wrap`, `Proof.Modes.Arm.wrap_verified`), and so
meet the same contract with 1032 bytes of stack (`ecbWrap_implies`), and
with 1040, the stack their cleanup zeroes; `Fn` has the theorems their
registrations bind.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)

/-- The cipher of a direction, on blocks as lists. -/
def dirCipher : Spec.TripleDes.Direction → Spec.TripleDes.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.TripleDes.cipher
  | .decrypt => Spec.TripleDes.invCipher

/-- The block function of a direction. -/
def dirBlock : Spec.TripleDes.Direction → Spec.TripleDes.Schedule → Spec.TripleDes.Block → Spec.TripleDes.Block
  | .encrypt => Spec.TripleDes.encryptBlock
  | .decrypt => Spec.TripleDes.decryptBlock

theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) : blocksOf 8 m p n = Spec.TripleDes.cbcBlocksAt m p n := by
  simp only [VG.Proof.Modes.blocksOf, Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.blocksAt, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  apply List.ext_getElem (by simp [bytesAt])
  intro j h₁ _
  simp [bytesAt, Spec.TripleDes.blockAt]

theorem ofFn_getD (v : Spec.TripleDes.Block) : (Vector.ofFn fun i : Fin 8 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi; simp [List.getD_eq_getElem?_getD]

theorem dirCipher_toList (d : Spec.TripleDes.Direction) (k : Spec.TripleDes.Schedule) (v : Spec.TripleDes.Block) :
    dirCipher d k v.toList = (dirBlock d k v).toList := by
  cases d <;> simp only [dirCipher, dirBlock, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, ofFn_getD]

theorem ecb_dir (d : Spec.TripleDes.Direction) (k : Spec.TripleDes.Schedule) (xs : List Spec.TripleDes.Block) :
    Spec.TripleDes.ecb k d xs = xs.map (dirBlock d k) := by
  cases d <;> rfl

theorem ecbOut (d : Spec.TripleDes.Direction) (stack : Nat) :
    VG.Arm.Scrub.PostOut (Spec.TripleDes.ecbContract Arm.abi d stack) (Spec.TripleDes.ecbSig.retBits 32) :=
  VG.Arm.Scrub.postOut_of_local (leak := none) VG.Arm.Scrub.ScrubAbi.plain (Proof.TripleDes.ecbPostOut_local _ d)

end VG.Proof.TripleDes.Arm

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm
open VG.Proof.Modes (blocksOf)

theorem ecb_stack (d : Spec.TripleDes.Direction) : VG.Arm.FrameStack.armStack (ecbCore d).code ≤ 1024 := by
  cases d <;> lit_decide

/-- The ECB cores, by the ECB functions' shared contract. -/
theorem ecbVerified : ∀ d : Spec.TripleDes.Direction,
    Verified Arm.target (ecbCore d).code (Spec.TripleDes.ecbContract Arm.abi d 1024)
  | .encrypt => ecb_framed Bitsliced.encrypt_verified
  | .decrypt => ecb_framed Bitsliced.decrypt_verified

/-- Triple DES's ECB function in the direction `d`, as the modes' core. -/
def ecbSpec (d : Spec.TripleDes.Direction) : CoreSpec (ecbCore d) where
  keyLen := 384
  stack := 1024
  ciphAt m K _ := dirCipher d (Spec.TripleDes.scheduleAt m K)
  contract := Spec.TripleDes.ecbContract Arm.abi d 1024
  correct := (ecbVerified d).1
  ct := (ecbVerified d).2.1
  depth := ecb_stack d
  pre_of _ s h := by
    obtain ⟨stk, rd, wr, kd, bk, bd, fK, fD, -⟩ := h
    sig_pre [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact ⟨stk, by have := s.sp.isLt; omega_using [], rd, wr, kd, bk, bd, fK, fD⟩
  post_of _ s s' _ h := by
    sig_post [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    show blocksOf 8 _ _ _ = (blocksOf 8 _ _ _).map _
    rw [show (ecbCore d).dReg = .r1 from rfl, show (ecbCore d).nReg = .r2 from rfl]
    simp only [State.addr]
    rw [blocksOf_eq, blocksOf_eq, Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.cbcBlocksAt, h, ecb_dir,
      List.map_map, List.map_map]
    exact List.map_congr_left fun v _ => (dirCipher_toList d _ v).symm
  pub_of _ s₁ s₂ h0 h1 h2 h3 _ := by
    sig_pub [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact ⟨h0, h1, h2, h3⟩
  ciphAt_congr h := by simp only [Proof.TripleDes.scheduleAt_copy h]
  ciphAt_R _ _ _ _ _ := rfl
  cipher_len m K _ b _ := by
    cases d <;> (simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher]; rfl)
  bw_pos := by cases d <;> decide
  bw_le := by cases d <;> decide
  bs_enc := by cases d <;> decide

/-- The public ECB functions' contract, with the 8 bytes of the call's frame
more than the core's, is what the call of the core meets. -/
theorem ecbWrap_implies (d : Spec.TripleDes.Direction) :
    (wrapContract (ecbSpec d)).Implies (Spec.TripleDes.ecbContract Arm.abi d 1032) where
  pre s h := by
    sig_pre [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨stk, -, rd, wr, kd, bk, bd, fK, fD⟩ := h
    exact { stk := stk, rd := rd, wr := wr, kd := kd, bk := bk, bd := bd, fK := fK, fD := fD
            rr := fun h => by cases h
            a3 := fun _ h => by cases h }
  post s s' _ h := by
    sig_post [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    change blocksOf 8 s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      (blocksOf 8 s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat).map
        (dirCipher d (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0)))) at h
    simp only [State.addr] at h
    rw [blocksOf_eq, blocksOf_eq, Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.cbcBlocksAt] at h
    refine (List.map_inj_right (fun a b e => Vector.toList_inj.mp e)).1 ?_
    rw [h, ecb_dir, List.map_map, List.map_map]
    exact List.map_congr_left fun v _ => dirCipher_toList d _ v
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, fun h => by cases h⟩
  sat := by
    implies_sat [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [ecbFrameSat] using ecbFrameSat

theorem ecbWrapSat (d : Spec.TripleDes.Direction) : ∃ s, (Spec.TripleDes.ecbContract Arm.abi d 1040).pre s := by
  implies_sat [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [ecbFrameSat] using ecbFrameSat

end VG.Proof.TripleDes.Arm

namespace VG.Proof.TripleDes.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

theorem ecbWrap_code (d : Spec.TripleDes.Direction) : CodeOk (Impl.TripleDes.Arm.ecbCore d).wrap 1040 :=
  CodeOk.push (n := 1032) (CodeOk.seq ((CodeOk.block _).mono (Nat.zero_le _))
    (CodeOk.seq (CodeOk.call ⟨Nat.le_trans (ecb_stack d) (by decide), by cases d <;> lit_decide⟩)
      ((CodeOk.block _).mono (Nat.zero_le _))))

/-- `vg_triple_des_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.ecbEncrypt (Spec.TripleDes.ecbContract Arm.abi .encrypt 1040) 0 :=
  verifiedScrubbedAll (api := Spec.TripleDes.ecbEncryptApi)
    { code := (Impl.TripleDes.Arm.ecbCore .encrypt).wrap
      verified := Verified.stack_le (by decide)
        (Proof.Modes.Arm.wrap_verified (ecbSpec .encrypt) rfl (ecbWrap_implies .encrypt)) (ecbWrapSat .encrypt) }
    (ecbOut .encrypt _)
    (scrubSideF_of (ecbWrap_code .encrypt) (by decide) _)

/-- `vg_triple_des_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.ecbDecrypt (Spec.TripleDes.ecbContract Arm.abi .decrypt 1040) 0 :=
  verifiedScrubbedAll (api := Spec.TripleDes.ecbDecryptApi)
    { code := (Impl.TripleDes.Arm.ecbCore .decrypt).wrap
      verified := Verified.stack_le (by decide)
        (Proof.Modes.Arm.wrap_verified (ecbSpec .decrypt) rfl (ecbWrap_implies .decrypt)) (ecbWrapSat .decrypt) }
    (ecbOut .decrypt _)
    (scrubSideF_of (ecbWrap_code .decrypt) (by decide) _)

end VG.Proof.TripleDes.Arm.Fn
