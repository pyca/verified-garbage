module

public import VerifiedGarbage.Proof.Ed25519.X86.VerifyVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed25519.X86.VerifyLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ed25519.Bytes
public import VerifiedGarbage.Proof.Ed25519.ScalarBytes
public import VerifiedGarbage.Proof.Ed25519.Window
public import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
public import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
public import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
public import VerifiedGarbage.Proof.Ed25519.X86.InputBits
public import VerifiedGarbage.Proof.Ed25519.X86.PointEncodeSign
public import VerifiedGarbage.Proof.Ed25519.X86.PointEqual
public import VerifiedGarbage.Proof.Ed25519.X86.PointMul
public import VerifiedGarbage.Proof.Ed25519.X86.Power
public import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
public import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarStep
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyPoints
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyTables
public import VerifiedGarbage.Proof.Ed25519.X86.WindowTables
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
import VerifiedGarbage.Proof.Ed25519.X86.InputBits
import VerifiedGarbage.Proof.Ed25519.X86.PointEncodeSign
import VerifiedGarbage.Proof.Ed25519.X86.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86.PointMul
import VerifiedGarbage.Proof.Ed25519.X86.Power
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Ed25519.X86.ScalarStep
import VerifiedGarbage.Proof.Ed25519.X86.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.X86.VerifyTables
import VerifiedGarbage.Proof.Ed25519.X86.WindowTables
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx

/-! The complete strict verification equation on baseline i686. -/

@[expose] public section

namespace VG.Artifacts.Ed25519Verify.X86

def artifacts : List Artifact := [
  Spec.Ed25519.verifyEquationApi.artifact X86.target {
    notes := ["Checks canonical point encodings (A's, then R's, by one loop running \
      the decoding twice) and S < L, then evaluates the uncofactored equation using all 512 challenge bits. \
      Computes [k]A - [S]B with one chain of doublings and 4-bit windows of the public \
      scalars, from a table of [1]A to [15]A and one of -[1]B to -[15]B copied into `scratch` \
      from the static `VG_ED25519_VERIFY_NEG_BASE`, skipping the \
      leading zero bytes of k above its low 32, and compares it with -R projectively. \
      Point additions call `vg_ed25519_r32_point_add`, and the decodings' square root's \
      addition chain `vg_gf25519_r32_pow250`. Point tables and callee-saved registers \
      reside in `scratch`."]
    consts := Impl.Ed25519.X86.bConsts
    code := Impl.Ed25519.X86.verifyEquation
    verified := Proof.Ed25519.X86.verify_verified
    stack := 8 }]

end VG.Artifacts.Ed25519Verify.X86
