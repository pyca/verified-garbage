import VerifiedGarbage.Proof.AesCbc.Arm.Verified
import VerifiedGarbage.Proof.AesXts.Arm.Body

/-!
# XTS-AES on ARMv7: `Verified`

Correctness and constant time, from the loop AES-CBC's proofs share, a state
satisfying the precondition, and the shared contracts of
`Spec/Xts/Contract.lean`, with 8 bytes of stack: each call of a block
function pushes its stack argument and `lr`.
-/

namespace VG.Proof.AesXts.Arm

open VG VG.Arm VG.Impl.AesXts.Arm
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.Arm

theorem encrypt_verified : Verified Arm.target encrypt (Spec.Xts.aesEncryptContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => whole_wp encBody_ok hs) (whole_ct encBody_ok encBody_ct)
    { pre := by sig_implies_pre [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      -- `xtsMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeArm, AesXts.xtsMode, ciphOf, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        sig_reduce [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeArm, AesXts.xtsMode, ciphOf, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        sig_simp [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeArm, AesXts.xtsMode, ciphOf, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      sat := by sig_implies_sat [Spec.Xts.aesEncryptContract, Spec.Xts.aesSig, modeArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
        [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat }

theorem decrypt_verified : Verified Arm.target decrypt (Spec.Xts.aesDecryptContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => whole_wp decBody_ok hs) (whole_ct decBody_ok decBody_ct)
    { pre := by sig_implies_pre [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      -- `xtsMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeArm, AesXts.xtsMode, ciphOf, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        sig_reduce [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeArm, AesXts.xtsMode, ciphOf, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        sig_simp [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeArm, AesXts.xtsMode, ciphOf, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      sat := by sig_implies_sat [Spec.Xts.aesDecryptContract, Spec.Xts.aesSig, modeArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
        [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat }

end VG.Proof.AesXts.Arm
