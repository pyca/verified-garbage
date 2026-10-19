module

import VerifiedGarbage.Proof.Idea.Arm.Verified
public import VerifiedGarbage.Proof.Modes.Arm.Core
public import VerifiedGarbage.Impl.Idea.Arm.Modes
import VerifiedGarbage.Proof.Idea.Arith
public import VerifiedGarbage.Spec.Idea.Cbc
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Prime.Defs
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Idea.Arm.Lit

/-!
# IDEA's ECB function on ARMv7 as the modes' core

`ecbSpec`: what the modes need of `vg_idea_ecb` (`Proof.Modes.Arm.CoreSpec`),
from its contract (`Spec.Idea.ecbContract`, with 32 bytes of stack) and its
proof (`ecb_framed`): the schedule is IDEA's 104-byte table of subkeys, and
the cipher on a block is `Spec.Idea.cipher` of it (encryption under the
encryption subkeys, decryption under the decryption subkeys).
-/

@[expose] public section

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Impl.Idea.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)

theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) : blocksOf 8 m p n = Spec.Idea.cbcBlocksAt m p n := by
  simp only [VG.Proof.Modes.blocksOf, Spec.Idea.cbcBlocksAt, Spec.Idea.blocksAt, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  apply List.ext_getElem (by simp [bytesAt])
  intro j h₁ _
  simp [bytesAt, Spec.Idea.blockAt]

theorem ofFn_getD (v : Spec.Idea.Block) : (Vector.ofFn fun i : Fin 8 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi; simp [List.getD_eq_getElem?_getD]

theorem cipher_toList (k : Spec.Idea.Schedule) (v : Spec.Idea.Block) :
    Spec.Idea.cipher k v.toList = (Spec.Idea.cryptBlock k v).toList := by
  simp only [Spec.Idea.cipher, ofFn_getD]

theorem ecb_stack : VG.Arm.FrameStack.armStack ecbCode ≤ 32 := by decide +kernel

/-- IDEA's ECB function, as the modes' core. -/
def ecbSpec : CoreSpec ecbCore where
  keyLen := 104
  stack := 32
  ciphAt m K _ := Spec.Idea.cipher (Spec.Idea.scheduleAt m K)
  contract := Spec.Idea.ecbContract Arm.abi 32
  correct := ecb_framed.1
  ct := ecb_framed.2.1
  depth := ecb_stack
  pre_of _ s h := by
    obtain ⟨stk, rd, wr, kd, bk, bd, fK, fD, -⟩ := h
    sig_pre [Spec.Idea.ecbContract, Spec.Idea.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨stk, by have := s.sp.isLt; omega, rd, wr, kd, bk, bd, fK, fD⟩
  post_of _ s s' _ h := by
    sig_post [Spec.Idea.ecbContract, Spec.Idea.ecbSig, Spec.Idea.ecbPost, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    show blocksOf 8 _ _ _ = (blocksOf 8 _ _ _).map _
    rw [show ecbCore.dReg = .r1 from rfl, show ecbCore.nReg = .r2 from rfl]
    simp only [State.addr]
    rw [blocksOf_eq, blocksOf_eq, Spec.Idea.cbcBlocksAt, Spec.Idea.cbcBlocksAt, h, Spec.Idea.ecb, List.map_map,
      List.map_map]
    exact List.map_congr_left fun v _ => (cipher_toList _ v).symm
  pub_of _ s₁ s₂ h0 h1 h2 h3 _ := by
    sig_pub [Spec.Idea.ecbContract, Spec.Idea.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h0, h1, h2, h3⟩
  ciphAt_congr h := by simp only [Proof.Idea.scheduleAt_congr h]
  ciphAt_R _ _ _ _ _ := rfl
  cipher_len m K _ b _ := by simp [Spec.Idea.cipher]; rfl
  bw_pos := by decide
  bw_le := by decide
  bs_enc := by decide

end VG.Proof.Idea.Arm
