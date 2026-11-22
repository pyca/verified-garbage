module

public import VerifiedGarbage.Proof.Modes.Arm.Core
public import VerifiedGarbage.Impl.Seed.Arm.Modes
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Seed.Arm.Verified
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Seed.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Modes.Arm.Core
meta import VerifiedGarbage.Impl.Seed.Arm.Modes
meta import VerifiedGarbage.Spec.Seed.Cbc
meta import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Seed.Arm.Verified
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Seed.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# SEED's ECB functions on ARMv7 as the modes' core

`ecbSpec dir`: what the modes need of `vg_seed_ecb_encrypt` and
`vg_seed_ecb_decrypt` (`Proof.Modes.Arm.CoreSpec`), from their shared
contract (`Spec.Seed.ecbContract`, with 752 bytes of stack) and the proof of
each as it is emitted, cleanup included (`Fn.ecbEncrypt`, `Fn.ecbDecrypt`,
which their registrations bind; the modes call the artifacts themselves):
the schedule is SEED's 128-byte schedule, and the cipher on
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

theorem ecbOut (d : Spec.Seed.Direction) (stack : Nat) :
    VG.Arm.Scrub.PostOut (Spec.Seed.ecbContract Arm.abi d stack) (Spec.Seed.ecbSig.retBits 32) :=
  VG.Arm.Scrub.postOut_of_local (leak := none) VG.Arm.Scrub.ScrubAbi.plain (Proof.Seed.ecbPostOut_local _ d)

end VG.Proof.Seed.Arm

namespace VG.Proof.Seed.Arm.Fn

open VG VG.Spec.Seed VG.Arm VG.Arm.Scrub

/-- `vg_seed_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.ecbEncrypt (ecbContract Arm.abi .encrypt 752) 0 :=
  verifiedScrubbedSel (api := ecbEncryptApi) (W := 752)
    { code := Impl.Seed.Arm.ecbCode .encrypt
      verified := Proof.Seed.Arm.ecb_framed .encrypt }
    [] []
    (ecbOut .encrypt _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_seed_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.ecbDecrypt (ecbContract Arm.abi .decrypt 752) 0 :=
  verifiedScrubbedSel (api := ecbDecryptApi) (W := 752)
    { code := Impl.Seed.Arm.ecbCode .decrypt
      verified := Proof.Seed.Arm.ecb_framed .decrypt }
    [] []
    (ecbOut .decrypt _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

end VG.Proof.Seed.Arm.Fn

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Impl.Seed.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm
open VG.Proof.Modes (blocksOf)

theorem ecb_stack (dir : Spec.Seed.Direction) : VG.Arm.FrameStack.armStack (ecbCore dir).code ≤ 752 := by
  cases dir <;> lit_decide

/-- The ECB functions as emitted, by their shared contract. -/
theorem ecbVerified : ∀ dir : Spec.Seed.Direction,
    Verified Arm.target (ecbCore dir).code (Spec.Seed.ecbContract Arm.abi dir 752)
  | .encrypt => Fn.ecbEncrypt.verified
  | .decrypt => Fn.ecbDecrypt.verified

/-- SEED's ECB function in the direction `dir`, as the modes' core. -/
def ecbSpec (dir : Spec.Seed.Direction) : CoreSpec (ecbCore dir) where
  keyLen := 128
  stack := 752
  ciphAt m K _ := dirCipher dir (Spec.Seed.scheduleAt m K)
  contract := Spec.Seed.ecbContract Arm.abi dir 752
  correct := (ecbVerified dir).1
  ct := (ecbVerified dir).2.1
  depth := ecb_stack dir
  pre_of _ s h := by
    obtain ⟨stk, rd, wr, kd, bk, bd, fK, fD, -⟩ := h
    sig_pre [Spec.Seed.ecbContract, Spec.Seed.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨stk, by have := s.sp.isLt; omega_using [], rd, wr, kd, bk, bd, fK, fD⟩
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
