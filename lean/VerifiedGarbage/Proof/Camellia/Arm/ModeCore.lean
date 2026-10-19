module

import VerifiedGarbage.Proof.Camellia.Arm.Verified
public import VerifiedGarbage.Proof.Modes.Arm.Core
public import VerifiedGarbage.Impl.Camellia.Arm.Cbc
import VerifiedGarbage.Proof.Camellia.CtrCipher
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Proof.Camellia.Arm.Ecb
public import VerifiedGarbage.Proof.Camellia.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TaintSum
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# Camellia's ECB functions on ARMv7 as the modes' core

`ecbSpec dir`: what the modes need of `vg_camellia_ecb_encrypt` and
`vg_camellia_ecb_decrypt` (`Proof.Modes.Arm.CoreSpec`), from their shared
contract (`Spec.Camellia.ecbContract`, with 2816 bytes of stack) and its
proof (`ecb_framed`): the schedule is Camellia's 272-byte schedule, the
number of rounds is 18 or 24, and the cipher on a block is
`Spec.Camellia.cipher` or `Spec.Camellia.invCipher` of the subkeys of that
many rounds (`rsel`, which reads 18 or 24 whatever the number is).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Impl.Camellia.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)

/-- The number of rounds the cipher reads: 18 or 24. -/
def rsel (R : BitVec 32) : Nat := if R.toNat = 18 then 18 else 24

theorem rsel_eq {R : BitVec 32} (h : R.toNat = 18 ∨ R.toNat = 24) : rsel R = R.toNat := by
  unfold rsel; split <;> omega

/-- The cipher of a direction, on blocks as lists. -/
def dirCipher : Dir → Spec.Camellia.Subkeys → Spec.Cbc.Cipher
  | .encrypt => Spec.Camellia.cipher
  | .decrypt => Spec.Camellia.invCipher

/-- The block function of a direction. -/
def dirBlock : Dir → Spec.Camellia.Subkeys → Spec.Camellia.Block → Spec.Camellia.Block
  | .encrypt => Spec.Camellia.encryptBlock
  | .decrypt => Spec.Camellia.decryptBlock

theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) :
    blocksOf 16 m p n = (Spec.Camellia.blocksAt m p n).map Vector.toList := by
  simp only [VG.Proof.Modes.blocksOf, Spec.Camellia.blocksAt, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  exact Proof.Camellia.bytesAt_eq_blockAt _ _

theorem dirCipher_toList (dir : Dir) (k : Spec.Camellia.Subkeys) (v : Spec.Camellia.Block) :
    dirCipher dir k v.toList = (dirBlock dir k v).toList := by
  cases dir <;> simp only [dirCipher, dirBlock, Spec.Camellia.cipher, Spec.Camellia.invCipher,
    Proof.Camellia.ofFn_toList]

theorem ecb_dir (dir : Dir) (k : Spec.Camellia.Subkeys) (xs : List Spec.Camellia.Block) :
    Spec.Camellia.ecb k (specDir dir) xs = xs.map (dirBlock dir k) := by
  cases dir <;> rfl

theorem ecb_stack (dir : Dir) : VG.Arm.FrameStack.armStack (ecbCode dir) ≤ 2816 := by
  cases dir <;> decide +kernel

theorem dReg_eq (dir : Dir) : (ecbCore dir).dReg = .r2 := rfl
theorem nReg_eq (dir : Dir) : (ecbCore dir).nReg = .r3 := rfl

/-- Camellia's ECB function in the direction `dir`, as the modes' core. -/
def ecbSpec (dir : Dir) : CoreSpec (ecbCore dir) where
  keyLen := 272
  stack := 2816
  rok R := R.toNat = 18 ∨ R.toNat = 24
  ciphAt m K R := dirCipher dir (Spec.Camellia.subkeysAt m K (rsel R))
  contract := Spec.Camellia.ecbContract Arm.abi (specDir dir) 2816
  correct := (ecb_framed dir).1
  ct := (ecb_framed dir).2.1
  depth := ecb_stack dir
  pre_of _ s h := by
    obtain ⟨stk, rd, wr, kd, bk, bd, fK, fD, rr⟩ := h
    have rr := rr rfl
    rw [dReg_eq, nReg_eq] at wr kd bd fD
    sig_pre [Spec.Camellia.ecbContract, Spec.Camellia.ecbSig, Spec.Camellia.ecbPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    exact ⟨stk, by have := s.sp.isLt; omega, rd, wr, kd, bk, bd, fK, fD, rr⟩
  post_of _ s s' hp h := by
    have rr := hp.rr rfl
    sig_post [Spec.Camellia.ecbContract, Spec.Camellia.ecbSig, Spec.Camellia.ecbPost, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    show blocksOf 16 _ _ _ = (blocksOf 16 _ _ _).map _
    rw [dReg_eq, nReg_eq, rsel_eq rr]
    simp only [State.addr]
    rw [blocksOf_eq, blocksOf_eq, h rr, ecb_dir, List.map_map, List.map_map]
    exact List.map_congr_left fun v _ => (dirCipher_toList dir _ v).symm
  pub_of _ s₁ s₂ h0 h1 h2 h3 h4 := by
    sig_pub [Spec.Camellia.ecbContract, Spec.Camellia.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact ⟨h0, h1, h2, h3, h4 rfl⟩
  ciphAt_congr {_ _ _ R} h := congrArg (dirCipher dir) (Proof.Camellia.subkeysAt_congr (R := rsel R)
    (by unfold rsel; split <;> decide) h)
  ciphAt_R h := by cases dir <;> simp [ecbCore] at h
  cipher_len m K _ b _ := by cases dir <;> (simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher]; rfl)
  bw_pos := by cases dir <;> decide
  bw_le := by cases dir <;> decide
  bs_enc := by cases dir <;> decide

end VG.Proof.Camellia.Arm
