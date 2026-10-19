module

import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMontgomeryInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Verified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNtt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YAddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YUse
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Avx2Lit
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YNorm
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMontgomery
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Verified
import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyButterfly
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNormalize
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNttLayers
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.MontgomeryCore
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMul
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.OneOut
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Scalar
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Sq
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Verified
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5CT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5ParseCT
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.X86_64.Zero
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop

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
        by lit_decide, by lit_decide, Code.all_of_allInstrs (by lit_decide)⟩ }
  features := ["avx", "avx2"]

end VG.Proof.MlDsa.X86_64
