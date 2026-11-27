module

public import VerifiedGarbage.Proof.AesCfb.Rounds
public import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Verified
public import VerifiedGarbage.Proof.AesCfb.AArch64.Neon.Verified
public import VerifiedGarbage.Impl.AesCfb.AArch64.Neon
public import VerifiedGarbage.Proof.AesCfb.AArch64.Verified
public import VerifiedGarbage.Impl.AesCfb.AArch64
public import VerifiedGarbage.Impl.AesCfb.AArch64.Decrypt
public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
public import VerifiedGarbage.Proof.AesCbc.AArch64.Block
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.SideFill
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # The implementations of AES-CFB128 decryption on AArch64

A `CfbImpl` is the code of `vg_aes_cfb128_decrypt`'s whole blocks with what
is proven of it, and the block functions the functions around it call
(`vg_aes_cfb128_encrypt`, and both functions of a message's last piece).
`CfbImpl.aes` decrypts with the Cryptographic Extension and
`CfbImpl.neon` in AdvSIMD registers, each its own code; `CfbImpl.ofBlocks`
calls the block functions. -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64
open VG VG.AArch64 VG.Proof.Aes.AArch64
open VG.Proof.AesCbc.AArch64 (modeAArch64)

/-- An implementation of AES-CFB128: the block functions, and the code that
decrypts whole blocks. -/
structure CfbImpl where
  /-- The block functions `vg_aes_cfb128_encrypt` and a message's last piece
  call. -/
  blocks : BlocksImpl
  /-- `vg_aes_cfb128_decrypt`'s code. -/
  dec : Prog isa
  /-- What `dec` writes of its arguments' scratch space. -/
  written : List (String × Nat)
  decVerified : Verified AArch64.target dec (Proof.AesCfb.decryptRoundsContract AArch64.abi)
  decWritten : ∀ s tr t, (Proof.AesCfb.decryptRoundsContract AArch64.abi).pre s → Exec isa dec s tr t →
    Sig.writtenWithin (AArch64.abi.withConsts []) Spec.Cfb.aesSig written s t
  decCorrect : ∀ s, (modeAArch64 (cfbMode false)).pre s →
    ∃ t s', Exec isa dec s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (cfbMode false)).post s s'
  decCt : ConstantTime isa (modeAArch64 (cfbMode false)).pre (modeAArch64 (cfbMode false)).pub dec
  decNoFrames : dec.noFrames = true
  decKeepsV : dec.allInstrs keepsV = true
  /-- `dec` has no indirect call and never writes `DIT`. -/
  decSide : AArch64.Scrub.sideAll (fun i => !i.writesDit) dec = true

namespace CfbImpl

/-- What the names of its functions end with. -/
abbrev suffix (v : CfbImpl) : String := v.blocks.suffix

/-- The block function its functions call. -/
abbrev enc (v : CfbImpl) : Impl.Aes.AArch64.Blocks := v.blocks.enc

/-- Decryption with the Cryptographic Extension, which writes nothing in
`scratch`. -/
def aes (v : BlocksImpl) : CfbImpl where
  blocks := v
  dec := Impl.AesCfb.AArch64.Decrypt.code
  written := [("scratch", 0)]
  decVerified := Decrypt.verified
  decWritten := Decrypt.written
  decCorrect := Decrypt.correct
  decCt := Decrypt.ct
  decNoFrames := by kernel_rfl
  decKeepsV := by kernel_rfl
  decSide := by kernel_rfl

/-- Decryption in AdvSIMD registers. -/
def neon (v : BlocksImpl) : CfbImpl where
  blocks := v
  dec := Impl.AesCfb.AArch64.Neon.decrypt
  written := []
  decVerified := Neon.verified
  decWritten := fun _ _ _ _ _ => True.intro
  decCorrect := Neon.correct
  decCt := Neon.ct
  decNoFrames := Neon.decrypt_noFrames
  decKeepsV := Neon.decrypt_keepsV
  decSide := by kernel_rfl

private theorem decrypt_side0 :
    AArch64.Scrub.sideAll (fun i => !i.writesDit)
      (Impl.AesCfb.AArch64.decrypt ⟨"", .block [], ⟨[], [], []⟩, 0⟩) = true := by
  kernel_rfl

theorem decrypt_side (v : BlocksImpl) :
    AArch64.Scrub.sideAll (fun i => !i.writesDit) (Impl.AesCfb.AArch64.decrypt v.enc) = true := by
  have h0 := decrypt_side0
  have hc := AArch64.Scrub.sideAll_noDit_of_calleeSide v.encScrub
  simp only [Impl.AesCfb.AArch64.decrypt, Impl.AesCbc.AArch64.batched, Impl.AesCbc.AArch64.groups,
    Impl.AesCfb.AArch64.decGroup, Impl.AesCfb.AArch64.body, AArch64.Scrub.sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, hc, and_self]

theorem decrypt_noFrames (v : BlocksImpl) : (Impl.AesCfb.AArch64.decrypt v.enc).noFrames = true := by
  simp only [Impl.AesCfb.AArch64.decrypt, Impl.AesCbc.AArch64.batched, Impl.AesCbc.AArch64.groups,
    Impl.AesCfb.AArch64.decGroup, Impl.AesCfb.AArch64.body, Code.noFrames, v.encNoFrames,
    Bool.and_self]

/-- Decryption that calls the block function of `v`. -/
def ofBlocks (v : BlocksImpl) : CfbImpl where
  blocks := v
  dec := Impl.AesCfb.AArch64.decrypt v.enc
  written := []
  decVerified := decrypt_verified v
  decWritten := fun _ _ _ _ _ => True.intro
  decCorrect := decrypt_correct v
  decCt := decrypt_ct v
  decNoFrames := decrypt_noFrames v
  decKeepsV := decrypt_keepsV v
  decSide := decrypt_side v

end CfbImpl

end VG.Proof.AesCfb.AArch64
