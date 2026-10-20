module

public import VerifiedGarbage.Proof.Modes.Arm.Core
public import VerifiedGarbage.Impl.Blowfish.Arm.Modes
public import VerifiedGarbage.Spec.Blowfish.Cbc
public import VerifiedGarbage.Proof.Blowfish.Arm.Verified
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Blowfish.Arm.Lit
import VerifiedGarbage.Proof.Blowfish.Arm.Run
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Blowfish.Arm.Frame

/-!
# Blowfish's ECB functions on ARMv7 as the modes' core

`ecbSpec up`: what the modes need of `vg_blowfish_ecb_encrypt` (`up`) and
`vg_blowfish_ecb_decrypt` (`Proof.Modes.Arm.CoreSpec`), from their shared
contract (`Spec.Blowfish.ecbContract`, with 256 bytes of stack) and its
proof (`ecb_framed`): the schedule is Blowfish's 4168-byte schedule, and the
cipher on a block is `Spec.Blowfish.cipher` or `Spec.Blowfish.invCipher` of
it.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Impl.Blowfish.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)

/-- The cipher of `up`, on blocks as lists. -/
def dirCipher (up : Bool) : Spec.Blowfish.Schedule → Spec.Cbc.Cipher :=
  if up then Spec.Blowfish.cipher else Spec.Blowfish.invCipher

/-- The block function of `up`. -/
def dirBlock (up : Bool) : Spec.Blowfish.Schedule → Spec.Blowfish.Block → Spec.Blowfish.Block :=
  if up then Spec.Blowfish.encryptBlock else Spec.Blowfish.decryptBlock

theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) :
    blocksOf 8 m p n = (Spec.Blowfish.blocksAt m p n).map Vector.toList := by
  simp only [VG.Proof.Modes.blocksOf, Spec.Blowfish.blocksAt, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  apply List.ext_getElem (by simp [bytesAt])
  intro j h₁ _
  simp [bytesAt, Spec.Blowfish.blockAt]

theorem ofFn_getD (v : Spec.Blowfish.Block) : (Vector.ofFn fun i : Fin 8 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi; simp [List.getD_eq_getElem?_getD]

theorem dirCipher_toList (up : Bool) (k : Spec.Blowfish.Schedule) (v : Spec.Blowfish.Block) :
    dirCipher up k v.toList = (dirBlock up k v).toList := by
  cases up <;> simp only [dirCipher, dirBlock, Spec.Blowfish.cipher, Spec.Blowfish.invCipher, ofFn_getD,
    Bool.false_eq_true, ↓reduceIte]

theorem ecb_dir (up : Bool) (k : Spec.Blowfish.Schedule) (xs : List Spec.Blowfish.Block) :
    Spec.Blowfish.ecb k (dir up) xs = xs.map (dirBlock up k) := by
  cases up <;> rfl

theorem ecb_stack (up : Bool) : VG.Arm.FrameStack.armStack (ecbCode up) ≤ 256 := by
  cases up <;> decide +kernel

/-- Blowfish's ECB function of `up`, as the modes' core. -/
def ecbSpec (up : Bool) : CoreSpec (ecbCore up) where
  keyLen := 4168
  stack := 256
  ciphAt m K _ := dirCipher up (Spec.Blowfish.scheduleAt m K)
  contract := Spec.Blowfish.ecbContract Arm.abi (dir up) 256
  correct := (ecb_framed up).1
  ct := (ecb_framed up).2.1
  depth := ecb_stack up
  pre_of _ s h := by
    obtain ⟨stk, rd, wr, kd, bk, bd, fK, fD, -⟩ := h
    sig_pre [Spec.Blowfish.ecbContract, Spec.Blowfish.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact ⟨stk, by have := s.sp.isLt; omega, rd, wr, kd, bk, bd, fK, fD⟩
  post_of _ s s' _ h := by
    sig_post [Spec.Blowfish.ecbContract, Spec.Blowfish.ecbSig, Spec.Blowfish.ecbPost, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    show blocksOf 8 _ _ _ = (blocksOf 8 _ _ _).map _
    rw [show (ecbCore up).dReg = .r1 from rfl, show (ecbCore up).nReg = .r2 from rfl]
    simp only [State.addr]
    rw [blocksOf_eq, blocksOf_eq, h, ecb_dir, List.map_map, List.map_map]
    exact List.map_congr_left fun v _ => (dirCipher_toList up _ v).symm
  pub_of _ s₁ s₂ h0 h1 h2 h3 _ := by
    sig_pub [Spec.Blowfish.ecbContract, Spec.Blowfish.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact ⟨h0, h1, h2, h3⟩
  ciphAt_congr h := by simp only [Proof.Blowfish.scheduleAt_congr h]
  ciphAt_R _ _ _ _ _ := rfl
  cipher_len m K _ b _ := by cases up <;> (simp [dirCipher, Spec.Blowfish.cipher, Spec.Blowfish.invCipher]; rfl)
  bw_pos := by cases up <;> decide
  bw_le := by cases up <;> decide
  bs_enc := by cases up <;> decide

end VG.Proof.Blowfish.Arm
