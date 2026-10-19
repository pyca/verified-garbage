module

public import VerifiedGarbage.Proof.Modes.Arm.Core
public import VerifiedGarbage.Impl.Seed.Arm.Modes
public import VerifiedGarbage.Spec.Seed.Cbc
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Seed.Arm.Verified

/-!
# SEED's ECB functions on ARMv7 as the modes' core

`ecbSpec dir`: what the modes need of `vg_seed_ecb_encrypt` and
`vg_seed_ecb_decrypt` (`Proof.Modes.Arm.CoreSpec`), from their shared
contract (`Spec.Seed.ecbContract`, with 752 bytes of stack) and its proof
(`ecb_framed`): the schedule is SEED's 128-byte schedule, and the cipher on
a block is `Spec.Seed.cipher` or `Spec.Seed.invCipher` of it.
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Impl.Seed.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)

/-- The cipher of a direction, on blocks as lists. -/
def dirCipher : Spec.Seed.Direction → Spec.Seed.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.Seed.cipher
  | .decrypt => Spec.Seed.invCipher

theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) :
    blocksOf 16 m p n = (Spec.Seed.blocksAt m p n).map Vector.toList := by
  simp only [VG.Proof.Modes.blocksOf, Spec.Seed.blocksAt, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  apply List.ext_getElem (by simp [bytesAt])
  intro j h₁ _
  simp [bytesAt, Spec.Seed.blockAt]

theorem ofFn_getD (v : Spec.Seed.Block) : (Vector.ofFn fun i : Fin 16 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi; simp [List.getD_eq_getElem?_getD]

/-- The block function of a direction. -/
def dirBlock : Spec.Seed.Direction → Spec.Seed.Schedule → Spec.Seed.Block → Spec.Seed.Block
  | .encrypt => Spec.Seed.encryptBlock
  | .decrypt => Spec.Seed.decryptBlock

theorem dirCipher_toList (dir : Spec.Seed.Direction) (k : Spec.Seed.Schedule) (v : Spec.Seed.Block) :
    dirCipher dir k v.toList = (dirBlock dir k v).toList := by
  cases dir <;> simp only [dirCipher, dirBlock, Spec.Seed.cipher, Spec.Seed.invCipher, ofFn_getD]

theorem ecb_dir (dir : Spec.Seed.Direction) (k : Spec.Seed.Schedule) (xs : List Spec.Seed.Block) :
    Spec.Seed.ecb k dir xs = xs.map (dirBlock dir k) := by
  cases dir <;> rfl

theorem ecb_stack (dir : Spec.Seed.Direction) : VG.Arm.FrameStack.armStack (ecbCode dir) ≤ 752 := by
  cases dir <;> decide +kernel

/-- SEED's ECB function in the direction `dir`, as the modes' core. -/
def ecbSpec (dir : Spec.Seed.Direction) : CoreSpec (ecbCore dir) where
  keyLen := 128
  stack := 752
  ciphAt m K _ := dirCipher dir (Spec.Seed.scheduleAt m K)
  contract := Spec.Seed.ecbContract Arm.abi dir 752
  correct := (ecb_framed dir).1
  ct := (ecb_framed dir).2.1
  depth := ecb_stack dir
  pre_of _ s h := by
    obtain ⟨stk, rd, wr, kd, bk, bd, fK, fD, -⟩ := h
    sig_pre [Spec.Seed.ecbContract, Spec.Seed.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨stk, by have := s.sp.isLt; omega, rd, wr, kd, bk, bd, fK, fD⟩
  post_of _ s s' _ h := by
    sig_post [Spec.Seed.ecbContract, Spec.Seed.ecbSig, Spec.Seed.ecbPost, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    show blocksOf 16 _ _ _ = (blocksOf 16 _ _ _).map _
    rw [show (ecbCore dir).dReg = .r1 from rfl, show (ecbCore dir).nReg = .r2 from rfl]
    simp only [State.addr]
    rw [blocksOf_eq, blocksOf_eq, h, ecb_dir, List.map_map, List.map_map]
    exact List.map_congr_left fun v _ => (dirCipher_toList dir _ v).symm
  pub_of _ s₁ s₂ h0 h1 h2 h3 _ := by
    sig_pub [Spec.Seed.ecbContract, Spec.Seed.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h0, h1, h2, h3⟩
  ciphAt_congr h := by simp only [Proof.Seed.scheduleAt_congr h]
  ciphAt_R _ _ _ _ _ := rfl
  cipher_len m K _ b _ := by cases dir <;> (simp [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher]; rfl)
  bw_pos := by cases dir <;> decide
  bw_le := by cases dir <;> decide
  bs_enc := by cases dir <;> decide

end VG.Proof.Seed.Arm
