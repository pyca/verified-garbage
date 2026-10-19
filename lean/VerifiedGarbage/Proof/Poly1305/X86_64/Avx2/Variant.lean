module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Blocks
public import VerifiedGarbage.Proof.Poly1305.X86_64.Variant
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Final

/-!
# `vg_poly1305_blocks_avx2` as an implementation of `vg_poly1305_blocks`

The `BlocksImpl` of `vg_poly1305_blocks_avx2` (see
`Proof/Poly1305/X86_64/Variant.lean`): its calls use 8 bytes of stack below
its return address (the return address of its call of `vg_poly1305_blocks`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64

namespace BlocksImpl

/-- The AVX2 implementation, `vg_poly1305_blocks_avx2`. -/
def avx2 : BlocksImpl where
  name := Impl.Poly1305.X86_64.Blocks.name .avx2
  code := Impl.Poly1305.X86_64.Blocks.code .avx2
  stack := 8
  stack_le := by decide
  depth_le := by
    change Impl.Poly1305.X86_64.Avx2.blocksAvx2.depth ≤ 2
    lit_decide
  xdepth := by change Impl.Poly1305.X86_64.Avx2.blocksAvx2.x86_64Depth ≤ 8; lit_decide
  ok := Avx2.blocksAvx2_ok
  ct := Avx2.blocksAvx2_ct
  nosp := avx2_nosp
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_avx2"
  features := Impl.Poly1305.X86_64.Blocks.features .avx2

end BlocksImpl

end VG.Proof.Poly1305.X86_64
