module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Blocks
public import VerifiedGarbage.Proof.Poly1305.X86_64.Variant
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Inv
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Lit

/-! ### `Poly1305.X86_64.Avx2.Variant`, which only this module used -/

section

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
  update := some avx2Update

end BlocksImpl

end VG.Proof.Poly1305.X86_64

end

end

/-! ### `Poly1305.X86_64.Avx512.Variant`, which only this module used -/

section

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
  update := some avx512Update

end BlocksImpl

end VG.Proof.Poly1305.X86_64

end

end

/-! ### `Poly1305.X86_64.Ifma.Variant`, which only this module used -/

section

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
  update := some ifmaUpdate

end BlocksImpl

end VG.Proof.Poly1305.X86_64

end

end


/-! # The implementations of `Poly1305Blocks` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.Poly1305Blocks.X86_64

def avx2 : Proof.Poly1305.X86_64.BlocksImpl := .avx2

def avx512 : Proof.Poly1305.X86_64.BlocksImpl := .avx512

def ifma : Proof.Poly1305.X86_64.BlocksImpl := .ifma

def scalar : Proof.Poly1305.X86_64.BlocksImpl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [ifma, avx512, avx2, scalar]

end VG.Proof.Variants.Poly1305Blocks.X86_64
