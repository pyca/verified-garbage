module

import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Lit
meta import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Lit
meta import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Lit
meta import VerifiedGarbage.Proof.Gcm.X86_64.Lit
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
public import VerifiedGarbage.Proof.Gcm.X86_64.Ghash
public import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Powers
import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# AES-GCM on x86-64: the implementations of `vg_ghash`

Untrusted: everything here is checked by Lean. The `GhashImpl`s of
`vg_ghash`, `vg_ghash_pclmul` and `vg_ghash_vpclmul`, from their proofs,
apart from `Callee.lean`: only the variants need them, and their proofs import the
algebra of `Proof/Gcm/Poly.lean`, which the rest of the AES-GCM proofs then
need not import.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

namespace GhashImpl

/-- `vg_ghash`, in the baseline ISA. -/
def scalar : GhashImpl where
  fn := ⟨"vg_ghash", Impl.Gcm.X86_64.ghash⟩
  depth := by lit_decide
  ok := Proof.Gcm.X86_64.ghash_correct
  ct := Proof.Gcm.X86_64.ghash_ct
  nosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []

/-- `vg_ghash_pclmul`. -/
def pclmul : GhashImpl where
  fn := ⟨"vg_ghash_pclmul", Impl.Gcm.X86_64.Pclmul.ghash⟩
  depth := by lit_decide
  ok := Proof.Gcm.X86_64.Pclmul.ghash_correct
  ct := Proof.Gcm.X86_64.Pclmul.ghash_ct
  nosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_pclmul"
  features := ["pclmulqdq", "ssse3"]

/-- `vg_ghash_vpclmul`. -/
def vpclmul : GhashImpl where
  fn := ⟨"vg_ghash_vpclmul", Impl.Gcm.X86_64.Vpclmul.ghash⟩
  depth := by lit_decide
  ok := Proof.Gcm.X86_64.Vpclmul.ghash_correct
  ct := Proof.Gcm.X86_64.Vpclmul.ghash_ct
  nosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_vpclmul"
  features := ["avx", "avx2", "pclmulqdq", "ssse3", "vpclmulqdq"]

end GhashImpl

/-- The implementation of `vg_ghash` named `n`. -/
def GhashName.impl : GhashName → GhashImpl
  | .scalar => .scalar
  | .pclmul => .pclmul
  | .vpclmul => .vpclmul

end VG.Proof.AesGcm.X86_64
