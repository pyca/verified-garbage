import VerifiedGarbage.Proof.Sm4.Arm.Verified
import VerifiedGarbage.Proof.Modes.Arm.Core
import VerifiedGarbage.Impl.Sm4.Arm.Cbc
import VerifiedGarbage.Proof.Sm4.CbcScratch

/-!
# SM4's ECB functions on ARMv7 as the modes' core

`ecbSpec dir`: what the modes need of `vg_sm4_ecb_encrypt` and
`vg_sm4_ecb_decrypt` (`Proof.Modes.Arm.CoreSpec`), from their shared
contract (`Spec.Sm4.ecbContract`, with 1456 bytes of stack) and its proof
(`ecb_framed`): the schedule is SM4's 128-byte schedule, and the cipher on
a block is `Spec.Sm4.cipher` or `Spec.Sm4.invCipher` of it.
-/

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

theorem ecb_stack (dir : Dir) : VG.Arm.FrameStack.armStack (ecbCode dir) ≤ 1456 := by
  cases dir <;> decide +kernel

/-- SM4's ECB function in the direction `dir`, as the modes' core. -/
def ecbSpec (dir : Dir) : CoreSpec (ecbCore dir) where
  keyLen := 128
  stack := 1456
  ciphAt m K := dirCipher dir (Spec.Sm4.scheduleAt m K)
  contract := Spec.Sm4.ecbContract Arm.abi (specDirArm dir) 1456
  correct := (ecb_framed dir).1
  ct := (ecb_framed dir).2.1
  depth := ecb_stack dir
  pre_of s h := by
    obtain ⟨stk, rd, wr, kd, bk, bd, fK, fD⟩ := h
    sig_pre [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨stk, by have := s.sp.isLt; omega, rd, wr, kd, bk, bd, fK, fD⟩
  post_of s s' _ h := by
    sig_post [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    show blocksOf 16 _ _ _ = (blocksOf 16 _ _ _).map _
    simp only [State.addr]
    rw [blocksOf_eq, blocksOf_eq, h, ecb_dir, List.map_map, List.map_map]
    exact List.map_congr_left fun v _ => (dirCipher_toList dir _ v).symm
  pub_of s₁ s₂ h0 h1 h2 h3 := by
    sig_pub [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h0, h1, h2, h3⟩
  ciphAt_congr h := by simp only [Proof.Sm4.scheduleAt_congr h]
  cipher_len m K b _ := by cases dir <;> (simp [dirCipher, Spec.Sm4.cipher, Spec.Sm4.invCipher]; rfl)
  bw_pos := by cases dir <;> decide
  bw_le := by cases dir <;> decide
  bs_enc := by cases dir <;> decide

end VG.Proof.Sm4.Arm
