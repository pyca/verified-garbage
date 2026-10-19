module

public import VerifiedGarbage.Impl.MlKem.AArch64.Top
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt

/-! Fused ML-KEM polynomial dot product. All terms are consumed for each
32-byte output block before that block is stored. -/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Dot

open VG.AArch64

def dotTerm (fg : Nat × Nat) : List Instr :=
 ptrTo .x1 .x28 fg.1 ++ ptrTo .x2 .x28 fg.2 ++
 [.add .x .x1 .x1 .x12,.add .x .x2 .x2 .x12,
 .ldrq .v0 .x1 0,.ldrq .v1 .x1 16,.ldrq .v4 .x2 0,.ldrq .v5 .x2 16,
 .vop (.perm .uzp1 .s4 .v6 .v0 .v1),.vop (.perm .uzp2 .s4 .v7 .v0 .v1),
 .vop (.perm .uzp1 .s4 .v19 .v4 .v5),.vop (.perm .uzp2 .s4 .v20 .v4 .v5),
 .vop (.mla .v21 .v6 .v19),.vop (.mla .v22 .v7 .v20),
 .vop (.mla .v23 .v6 .v20),.vop (.mla .v23 .v7 .v19)]
def dotReduce (v : VReg) : List Instr :=
 [.vop (.sqdmulh .v24 v .v17),.vop (.mls v .v24 .v16),.vop (.sub .s4 .v24 v .v16),.vop (.umin v v .v24)]
def dot (out : Nat) (terms : List (Nat × Nat)) : Prog isa :=
 .seq (.block (ptrTo .x0 .x28 out ++ vconsts ++
 [.adrSym .x3 "VG_MLKEM_GAMMA",.movz .x .x11 32 0,.movz .x .x12 0 0]))
 (.loop (.block ([.vop (.movi0 .v21),.vop (.movi0 .v22),.vop (.movi0 .v23)] ++
 terms.flatMap dotTerm ++ [.ldrq .v18 .x3 0,.vop (.sqdmulh .v24 .v22 .v17),.vop (.mls .v22 .v24 .v16),
 .vop (.mla .v21 .v22 .v18)] ++ dotReduce .v21 ++ dotReduce .v23 ++
 [.vop (.perm .zip1 .s4 .v0 .v21 .v23),.vop (.perm .zip2 .s4 .v1 .v21 .v23),
 .strq .v0 .x0 0,.strq .v1 .x0 16,.addImm .x .x0 .x0 32,.addImm .x .x3 .x3 16,
 .addImm .x .x12 .x12 32,.subImm .x .x11 .x11 1])) (.nonzero .x .x11))

end VG.Impl.MlKem.AArch64.Dot
