module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit

/-!
# `vg_poly1305_blocks_ifma` as an implementation of `vg_poly1305_blocks`

The `BlocksImpl` of `vg_poly1305_blocks_ifma` (see
`Proof/Poly1305/X86_64/Variant.lean`): its calls use 16 bytes of stack below
its return address (the return addresses of its call of
`vg_poly1305_blocks_avx2` and of that one's call of `vg_poly1305_blocks`), two
levels of calls.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64

namespace BlocksImpl

theorem ifma_keeps : ((instrs Impl.Poly1305.X86_64.Ifma.blocksIfma).all fun i =>
    !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem ifma_nosp : NoSp Impl.Poly1305.X86_64.Ifma.blocksIfma :=
  fun i hi => by simpa using List.all_eq_true.mp ifma_keeps i hi

/-- The AVX-512 IFMA implementation, `vg_poly1305_blocks_ifma`. -/
def ifma : BlocksImpl where
  name := Impl.Poly1305.X86_64.Blocks.name .ifma
  code := Impl.Poly1305.X86_64.Blocks.code .ifma
  stack := 16
  stack_le := by decide
  depth_le := by
    change Impl.Poly1305.X86_64.Ifma.blocksIfma.depth ≤ 2
    lit_decide
  xdepth := by change Impl.Poly1305.X86_64.Ifma.blocksIfma.x86_64Depth ≤ 16; lit_decide
  ok := Ifma.blocksIfma_ok
  ct := Ifma.blocksIfma_ct
  nosp := ifma_nosp
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_ifma"
  features := Impl.Poly1305.X86_64.Blocks.features .ifma

end BlocksImpl

end VG.Proof.Poly1305.X86_64
