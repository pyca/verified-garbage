import VerifiedGarbage.Proof.TripleDes.Arm.Frame
import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.Modes.Arm.Core
import VerifiedGarbage.Impl.TripleDes.Arm.Cbc

/-!
# Triple DES's ECB functions on ARMv7 as the modes' core

`ecbSpec d`: what the modes need of `vg_triple_des_ecb_encrypt` and
`vg_triple_des_ecb_decrypt` (`Proof.Modes.Arm.CoreSpec`), from their shared
contract (`Spec.TripleDes.ecbContract`, with 1024 bytes of stack) and its
proof (`ecb_framed`): the schedule is the 384-byte schedule, and the cipher
on a block is `Spec.TripleDes.cipher` or `Spec.TripleDes.invCipher` of it.
-/

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

theorem ecb_stack (d : Spec.TripleDes.Direction) : VG.Arm.FrameStack.armStack (ecbCode d) ≤ 1024 := by
  cases d <;> decide +kernel

/-- The ECB functions, by their shared contract. -/
theorem ecbVerified : ∀ d : Spec.TripleDes.Direction,
    Verified Arm.target (ecbCode d) (Spec.TripleDes.ecbContract Arm.abi d 1024)
  | .encrypt => ecb_framed Ecb.encrypt_verified
  | .decrypt => ecb_framed Ecb.decrypt_verified

/-- Triple DES's ECB function in the direction `d`, as the modes' core. -/
def ecbSpec (d : Spec.TripleDes.Direction) : CoreSpec (ecbCore d) where
  keyLen := 384
  stack := 1024
  ciphAt m K := dirCipher d (Spec.TripleDes.scheduleAt m K)
  contract := Spec.TripleDes.ecbContract Arm.abi d 1024
  correct := (ecbVerified d).1
  ct := (ecbVerified d).2.1
  depth := ecb_stack d
  pre_of s h := by
    obtain ⟨stk, rd, wr, kd, bk, bd, fK, fD⟩ := h
    sig_pre [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact ⟨stk, by have := s.sp.isLt; omega, rd, wr, kd, bk, bd, fK, fD⟩
  post_of s s' _ h := by
    sig_post [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    show blocksOf 8 _ _ _ = (blocksOf 8 _ _ _).map _
    simp only [State.addr]
    rw [blocksOf_eq, blocksOf_eq, Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.cbcBlocksAt, h, ecb_dir,
      List.map_map, List.map_map]
    exact List.map_congr_left fun v _ => (dirCipher_toList d _ v).symm
  pub_of s₁ s₂ h0 h1 h2 h3 := by
    sig_pub [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact ⟨h0, h1, h2, h3⟩
  ciphAt_congr h := by simp only [Proof.CmacTripleDes.scheduleAt_congr (fun i hi => (h i hi).symm)]
  cipher_len m K b _ := by
    cases d <;> (simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher]; rfl)
  bw_pos := by cases d <;> decide
  bw_le := by cases d <;> decide
  bs_enc := by cases d <;> decide

end VG.Proof.TripleDes.Arm
