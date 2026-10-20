module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Compiled
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Fusion
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem
public import VerifiedGarbage.Impl.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

/-! # The fixed hash's shapes are their proof-oriented decompositions, for any permutation

Each shape's code with the permutation's calls erased (over `hole`) has the
normal form of its decomposition (`decide`); with the holes filled by any
permutation `c` (`kernel_rfl`, with `c` a variable), so do the two
(`Fusion.Same.of_fillHoles`). -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
deriving instance DecidableEq for Code

/-- The decomposition of a shape is its code, for any permutation `c`, from the
code with holes: both are it with the holes filled with `c`, and the two have
the same normal form. -/
theorem compiled_same {c : Impl.Sha3.AArch64.Callee} {sc : Reg} {st wk rate sfx : Nat}
    {ins outs : List Piece}
    (hc : compiled c sc st wk rate sfx ins outs =
      Code.fillHoles c.name c.code (compiled hole sc st wk rate sfx ins outs))
    (hh : Impl.MlKem.AArch64.FixedHash.code c sc st wk rate sfx ins outs =
      Code.fillHoles c.name c.code (Impl.MlKem.AArch64.FixedHash.code hole sc st wk rate sfx ins outs))
    (h : Fusion.normalize (compiled hole sc st wk rate sfx ins outs) =
      Fusion.normalize (Impl.MlKem.AArch64.FixedHash.code hole sc st wk rate sfx ins outs)) :
    Fusion.Same (compiled c sc st wk rate sfx ins outs)
      (Impl.MlKem.AArch64.FixedHash.code c sc st wk rate sfx ins outs) :=
  Fusion.Same.of_fillHoles hc hh h

theorem kgG768_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem kgH768_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,lay768.ekLen⟩] [⟨.x27,2336,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,lay768.ekLen⟩] [⟨.x27,2336,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem prf768_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem enH768_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,lay768.ekLen⟩] [⟨.x28,KEM.HB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,lay768.ekLen⟩] [⟨.x28,KEM.HB,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem enG768_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem deG768_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,2336,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,2336,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem kgG1024_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem kgH1024_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x27,3104,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x27,3104,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem prf1024_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem enH1024_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x28,KEM.HB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x28,KEM.HB,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem enG1024_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem deG1024_compiled (c : Impl.Sha3.AArch64.Callee) : Fusion.Same
 (compiled c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,3104,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,3104,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩]) :=
 compiled_same (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.MlKem.AArch64.FixedHash
