module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Avx2Lit
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNtt
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YAddSub
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMontgomery
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMontgomeryInv
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YDot
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YBits
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YNorm
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YUse
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Verified

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
    { ntt := FnOk.of Arith.Lazy.verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      invNtt := FnOk.of Arith.MontgomeryInv.verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      mul := FnOk.of Arith.montMulY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      mulAdd := FnOk.of Arith.montMulAddY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      add := FnOk.of Arith.addY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      sub := FnOk.of Arith.subY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      highBits := FnOk.of Round.highBitsY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      lowBits := FnOk.of Round.lowBitsY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      normLt := FnOk.of Round.normLtY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      makeHint := FnOk.of Round.makeHintY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      useHint := FnOk.of Round.useHintY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      rej4 := ⟨Rej4.Segment.rejNTT4Avx2_verified, Proof.MlKem.X86_64.nosp_of (by lit_decide), by lit_decide,
        by lit_decide, Code.all_of_allInstrs (by lit_decide), fun _ _ _ => Rej4.Segment.rejNTT4Avx2_ret⟩
      expandMask4 := ⟨Mask4.expandMask4Avx2_verified, Proof.MlKem.X86_64.nosp_of (by lit_decide),
        by lit_decide, by lit_decide, Code.all_of_allInstrs (by lit_decide)⟩
      dotInv := fun c hc => by
        rcases hc with rfl | rfl | rfl
        · exact FnOk.of Arith.YDot.verified4 (by lit_decide) (by lit_decide) (by lit_decide) (by lit_decide)
        · exact FnOk.of Arith.YDot.verified5 (by lit_decide) (by lit_decide) (by lit_decide) (by lit_decide)
        · exact FnOk.of Arith.YDot.verified7 (by lit_decide) (by lit_decide) (by lit_decide) (by lit_decide) }
  features := ["avx", "avx2"]

end VG.Proof.MlDsa.X86_64
