module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on AArch64: `vg_ghash_aes`, `vg_ghash_prepared8_aes` and `vg_ghash_with_powers_aes`

Untrusted: everything here is checked by Lean. The `GhashImpl` of
`vg_ghash_aes` and the `GhashPreparedImpl` of `vg_ghash_prepared8_aes`, from
their proofs, apart from `Callee.lean`: only the variants
need it, and its proof imports the algebra of `Proof/Gcm/Poly.lean`, which
the rest of the AES-GCM proofs then need not import.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64

/-- `vg_ghash_prepared8_aes`, with PMULL. -/
def GhashPreparedImpl.aes : GhashPreparedImpl where
  fn := ⟨"vg_ghash_prepared8_aes", Impl.Gcm.AArch64.Pmull.ghashP⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghashP_correct
  ct := Proof.Gcm.AArch64.Pmull.ghashP_ct
  keepsV := by decide +kernel

/-- `vg_ghash_with_powers_aes`, with PMULL. -/
def GhashWithImpl.aes : GhashWithImpl where
  fn := ⟨"vg_ghash_with_powers_aes", Impl.Gcm.AArch64.Pmull.ghashW⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghashW_correct
  ct := Proof.Gcm.AArch64.Pmull.ghashW_ct
  keepsV := by decide +kernel

def GhashStoreImpl.aes : GhashStoreImpl where
  fn := ⟨"vg_ghash_store_powers_aes", Impl.Gcm.AArch64.Pmull.ghashS⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghashS_correct
  ct := Proof.Gcm.AArch64.Pmull.ghashS_ct
  keepsV := by decide +kernel

namespace GhashImpl

/-- `vg_ghash_aes`, with PMULL (which Rust's `aes` feature stands for, with
the AES instructions). -/
def aes : GhashImpl where
  fn := ⟨"vg_ghash_aes", Impl.Gcm.AArch64.Pmull.ghash⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghash_correct
  ct := Proof.Gcm.AArch64.Pmull.ghash_ct
  keepsV := by decide +kernel
  suffix := "_aes"
  features := ["aes"]
  pmull := true
  prepared := some .aes
  withPowers := some .aes
  storePowers := some .aes

end GhashImpl

/-- The implementation of `vg_ghash` named `n`. -/
def GhashName.impl : GhashName → GhashImpl
  | .scalar => .scalar
  | .aes => .aes

/-- The implementations a variant calls. -/
def GcmVariant.impl (v : GcmVariant) : GcmImpl := ⟨v.ctr, v.key, v.gh.impl⟩

end VG.Proof.AesGcm.AArch64
