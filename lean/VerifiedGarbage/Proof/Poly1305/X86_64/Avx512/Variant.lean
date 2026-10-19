module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Blocks
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Final
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Gpr
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.StoreY

/-!
# `vg_poly1305_blocks_avx512` as an implementation of `vg_poly1305_blocks`

The `BlocksImpl` of `vg_poly1305_blocks_avx512` (see
`Proof/Poly1305/X86_64/Variant.lean`): its calls use 16 bytes of stack below
its return address (the return addresses of its call of
`vg_poly1305_blocks_avx2` and of that one's call of `vg_poly1305_blocks`), two
levels of calls.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64

namespace BlocksImpl

theorem avx512_keeps : ((instrs Impl.Poly1305.X86_64.Avx512.blocksAvx512).all fun i =>
    !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem avx512_nosp : NoSp Impl.Poly1305.X86_64.Avx512.blocksAvx512 :=
  fun i hi => by simpa using List.all_eq_true.mp avx512_keeps i hi

/-- The AVX-512 implementation, `vg_poly1305_blocks_avx512`. -/
def avx512 : BlocksImpl where
  name := Impl.Poly1305.X86_64.Blocks.name .avx512
  code := Impl.Poly1305.X86_64.Blocks.code .avx512
  stack := 16
  stack_le := by decide
  depth_le := by
    change Impl.Poly1305.X86_64.Avx512.blocksAvx512.depth ≤ 2
    lit_decide
  xdepth := by change Impl.Poly1305.X86_64.Avx512.blocksAvx512.x86_64Depth ≤ 16; lit_decide
  ok := Avx512.blocksAvx512_ok
  ct := Avx512.blocksAvx512_ct
  nosp := avx512_nosp
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_avx512"
  features := Impl.Poly1305.X86_64.Blocks.features .avx512

end BlocksImpl

end VG.Proof.Poly1305.X86_64
