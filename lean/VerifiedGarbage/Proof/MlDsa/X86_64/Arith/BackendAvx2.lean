module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMontgomeryInv
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Verified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNtt
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMul
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YAddSub
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YUse
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ML-DSA on x86-64: the polynomial arithmetic with AVX2, as an `ArithImpl`

The AVX2 code (`Impl/MlDsa/X86_64/Arith/Avx2.lean`) meets what the callers of
the polynomial arithmetic need of it (`FnOk`), and requires AVX and AVX2.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith

/-- The AVX2 code. -/
def ArithImpl.avx2 : ArithImpl where
  code := .avx2Combined
  ok :=
    { ntt := FnOk.of Arith.Lazy.verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      invNtt := FnOk.of Arith.MontgomeryInv.verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      mul := FnOk.of Arith.montMulY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      mulAdd := FnOk.of Arith.montMulAddY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      add := FnOk.of Arith.addY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      sub := FnOk.of Arith.subY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      highBits := FnOk.of Round.highBitsY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      lowBits := FnOk.of Round.lowBitsY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      normLt := FnOk.of Round.normLtY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      makeHint := FnOk.of Round.makeHintY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      useHint := FnOk.of Round.useHintY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      rej4 := ⟨Rej4.Segment.rejNTT4Avx2_verified, Proof.MlKem.X86_64.nosp_of (by decide +kernel), by decide +kernel,
        by decide +kernel, Code.all_of_allInstrs (by decide +kernel), fun _ _ _ => Rej4.Segment.rejNTT4Avx2_ret⟩
      expandMask4 := ⟨Mask4.expandMask4Avx2_verified, Proof.MlKem.X86_64.nosp_of (by decide +kernel),
        by decide +kernel, by decide +kernel, Code.all_of_allInstrs (by decide +kernel)⟩ }
  features := ["avx", "avx2"]

end VG.Proof.MlDsa.X86_64
