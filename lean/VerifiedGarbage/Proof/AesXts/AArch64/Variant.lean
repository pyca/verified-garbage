module

public import VerifiedGarbage.Proof.AesXts.AArch64.Verified
public import VerifiedGarbage.Proof.AesXts.AArch64.Aes.Verified
public import VerifiedGarbage.Proof.AesXts.AArch64.CT
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Implementations of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt` on AArch64

An `XtsImpl` is what a function that calls the whole-block functions needs
of them, so that its proof holds for every implementation: each is a
variant of the interface `AesXts` on AArch64 (`Variants/AesXts/AArch64/`),
and each caller (in `Generic/AesXts/AArch64/`) is emitted once for each of
them (see `TCB/Emit.lean`). Both functions are proven against the contracts
`modeAArch64 (xtsMode true)` and `modeAArch64 (xtsMode false)`, have no
frames and write no callee-saved vector register.

There are two: the functions calling the bitsliced block functions
(`XtsImpl.blocks .scalar`, `vg_aes_xts_encrypt`), and the one-pass functions
with the AES instructions, which call nothing (`XtsImpl.aes`,
`vg_aes_xts_encrypt_aes`); both are emitted by
`Artifacts/AesXts/AArch64.lean`.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64

open VG VG.AArch64
open VG.Proof.AesCbc (aesWith_state aesInvWith_state)
open VG.Proof.AesCbc.AArch64 (modeAArch64)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- An implementation of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt` on AArch64. -/
structure XtsImpl where
  /-- `vg_aes_xts_encrypt`: its symbol and code. -/
  enc : Impl.Aes.AArch64.Blocks
  encNoFrames : enc.code.noFrames = true
  encOk : ∀ s, (modeAArch64 (AesXts.xtsMode true)).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s'
  encCt : ConstantTime isa (modeAArch64 (AesXts.xtsMode true)).pre (modeAArch64 (AesXts.xtsMode true)).pub
    enc.code
  encKeepsV : enc.code.allInstrs keepsV = true
  /-- `vg_aes_xts_decrypt`: its symbol and code. -/
  dec : Impl.Aes.AArch64.Blocks
  decNoFrames : dec.code.noFrames = true
  decOk : ∀ s, (modeAArch64 (AesXts.xtsMode false)).pre s →
    ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode false)).post s s'
  decCt : ConstantTime isa (modeAArch64 (AesXts.xtsMode false)).pre (modeAArch64 (AesXts.xtsMode false)).pub
    dec.code
  decKeepsV : dec.code.allInstrs keepsV = true
  /-- What the names of its callers' instances end with (e.g. `_aes`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace XtsImpl

theorem crypt_noFrames {b : Impl.Aes.AArch64.Blocks} (h : b.code.noFrames = true) :
    (Impl.AesXts.AArch64.crypt b).noFrames = true := by
  simp [Impl.AesXts.AArch64.crypt, Impl.AesXts.AArch64.batch, Impl.AesXts.AArch64.pass, Code.noFrames, h]

/-- The functions calling the block functions of `v`, `vg_aes_xts_encrypt`
and `vg_aes_xts_decrypt` with `v`'s suffix. -/
def blocks (v : BlocksImpl) : XtsImpl where
  enc := ⟨"vg_aes_xts_encrypt" ++ v.suffix, Impl.AesXts.AArch64.encrypt v.enc⟩
  encNoFrames := crypt_noFrames v.encNoFrames
  encOk := encrypt_correct v
  encCt := crypt_ct true v.encOk v.encCt v.encNoFrames fun R w m p => (aesWith_state R w m p).symm
  encKeepsV := encrypt_keepsV v
  dec := ⟨"vg_aes_xts_decrypt" ++ v.suffix, Impl.AesXts.AArch64.decrypt v.dec⟩
  decNoFrames := crypt_noFrames v.decNoFrames
  decOk := decrypt_correct v
  decCt := crypt_ct false v.decOk v.decCt v.decNoFrames fun R w m p => (aesInvWith_state R w m p).symm
  decKeepsV := decrypt_keepsV v
  suffix := v.suffix
  features := v.features

/-- The one-pass functions with the AES instructions,
`vg_aes_xts_encrypt_aes` and `vg_aes_xts_decrypt_aes`. -/
def aes : XtsImpl where
  enc := ⟨"vg_aes_xts_encrypt" ++ "_aes", Impl.AesXts.AArch64Aes.encrypt⟩
  encNoFrames := Aes.encrypt_noFrames
  encOk := Aes.encrypt_correct
  encCt := Aes.encrypt_ct true
  encKeepsV := Aes.encrypt_keepsV
  dec := ⟨"vg_aes_xts_decrypt" ++ "_aes", Impl.AesXts.AArch64Aes.decrypt⟩
  decNoFrames := Aes.decrypt_noFrames
  decOk := Aes.decrypt_correct
  decCt := Aes.decrypt_ct false
  decKeepsV := Aes.decrypt_keepsV
  suffix := "_aes"
  features := ["aes"]

end XtsImpl

end VG.Proof.AesXts.AArch64
