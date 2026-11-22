module

import VerifiedGarbage.Proof.TripleDes.Arm.Frame
public import VerifiedGarbage.Proof.Modes.Arm.Core
public import VerifiedGarbage.Impl.TripleDes.Arm.Cbc
public import VerifiedGarbage.Spec.TripleDes.Cbc
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.Arm.Scrub
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Verified
import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.Arm.Frame
meta import VerifiedGarbage.Proof.Modes.Arm.Core
meta import VerifiedGarbage.Impl.TripleDes.Arm.Cbc
meta import VerifiedGarbage.Spec.TripleDes.Cbc
meta import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.TripleDes.CbcBlocks
meta import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Verified
meta import VerifiedGarbage.Proof.TripleDes.Scratch
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# Triple DES's ECB functions on ARMv7 as the modes' core

`ecbSpec d`: what the modes need of `vg_triple_des_ecb_encrypt` and
`vg_triple_des_ecb_decrypt` (`Proof.Modes.Arm.CoreSpec`), from their shared
contract (`Spec.TripleDes.ecbContract`, with 1024 bytes of stack) and the
proof of each as it is emitted, cleanup included (`Fn.ecbEncrypt`,
`Fn.ecbDecrypt`, which their registrations bind): the schedule is the
384-byte schedule, and the cipher on a block is `Spec.TripleDes.cipher` or
`Spec.TripleDes.invCipher` of it. The modes call the artifacts themselves.
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

theorem ecbOut (d : Spec.TripleDes.Direction) :
    VG.Arm.Scrub.PostOut (Spec.TripleDes.ecbContract Arm.abi d 1024) (Spec.TripleDes.ecbSig.retBits 32) :=
  VG.Arm.Scrub.postOut_of_local (leak := none) VG.Arm.Scrub.ScrubAbi.plain (Proof.TripleDes.ecbPostOut_local _ d)

end VG.Proof.TripleDes.Arm

namespace VG.Proof.TripleDes.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_triple_des_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.ecbEncrypt (Spec.TripleDes.ecbContract Arm.abi .encrypt 1024) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ecbEncryptApi) (W := 1024)
    { code := Impl.TripleDes.Arm.ecbCode .encrypt
      verified := Proof.TripleDes.Arm.ecb_framed Proof.TripleDes.Arm.Bitsliced.encrypt_verified }
    [] []
    (ecbOut .encrypt)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.ecbDecrypt (Spec.TripleDes.ecbContract Arm.abi .decrypt 1024) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ecbDecryptApi) (W := 1024)
    { code := Impl.TripleDes.Arm.ecbCode .decrypt
      verified := Proof.TripleDes.Arm.ecb_framed Proof.TripleDes.Arm.Bitsliced.decrypt_verified }
    [] []
    (ecbOut .decrypt)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

end VG.Proof.TripleDes.Arm.Fn

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm
open VG.Proof.Modes (blocksOf)

theorem ecb_stack (d : Spec.TripleDes.Direction) : VG.Arm.FrameStack.armStack (ecbCore d).code ≤ 1024 := by
  cases d <;> lit_decide

/-- The ECB functions as emitted, by their shared contract. -/
theorem ecbVerified : ∀ d : Spec.TripleDes.Direction,
    Verified Arm.target (ecbCore d).code (Spec.TripleDes.ecbContract Arm.abi d 1024)
  | .encrypt => Fn.ecbEncrypt.verified
  | .decrypt => Fn.ecbDecrypt.verified

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

end VG.Proof.TripleDes.Arm
