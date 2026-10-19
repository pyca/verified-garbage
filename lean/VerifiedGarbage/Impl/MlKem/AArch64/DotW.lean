module

public import VerifiedGarbage.Impl.MlKem.AArch64.Dot

/-!
# ML-KEM on AArch64: the fused dot product of polynomials stored with 16 bits

`dotW bo bf bg out terms` is `dot out terms` for polynomials stored with 16-bit
coefficients: each iteration takes 16 coefficients (8 pairs) of each
polynomial (the first of each term at `bf` plus its offset, the second at
`bg` plus its offset), two vectors, splits them into the even and odd coefficients of
the pairs (UZP1, UZP2 of halfwords), and accumulates the products of pairs
`0 … 3` (UMLAL) and `4 … 7` (UMLAL2) in words, as `dot` does: `v21`–`v23`
and `v25`–`v27`. Each group is reduced as in `dot` (`finishR`), narrowed to
halfwords (UZP1) and interleaved (ZIP1, ZIP2) into 16 output coefficients, at `bo + out`.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.DotW

open VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Dot

/-- The products of the pairs of one term, accumulated. -/
def termW (bf bg : Reg) (fg : Nat × Nat) : List Instr :=
 ptrTo .x1 bf fg.1 ++ ptrTo .x2 bg fg.2 ++
 [.add .x .x1 .x1 .x12,.add .x .x2 .x2 .x12,
 .ldrq .v0 .x1 0,.ldrq .v1 .x1 16,.ldrq .v4 .x2 0,.ldrq .v5 .x2 16,
 .vop (.perm .uzp1 .h8 .v6 .v0 .v1),.vop (.perm .uzp2 .h8 .v7 .v0 .v1),
 .vop (.perm .uzp1 .h8 .v19 .v4 .v5),.vop (.perm .uzp2 .h8 .v20 .v4 .v5),
 .vop (.umlalH false .v21 .v6 .v19),.vop (.umlalH true .v25 .v6 .v19),
 .vop (.umlalH false .v22 .v7 .v20),.vop (.umlalH true .v26 .v7 .v20),
 .vop (.umlalH false .v23 .v6 .v20),.vop (.umlalH true .v27 .v6 .v20),
 .vop (.umlalH false .v23 .v7 .v19),.vop (.umlalH true .v27 .v7 .v19)]
/-- `a + b · γ` and `c`, reduced to `[0, q)`, with the temporary `t`: `finish` of `dot`. -/
def finishR (a b c g t : VReg) : List Instr :=
 [.vop (.sqdmulh t b .v17),.vop (.mls b t .v16),.vop (.mla a b g)] ++
 [.vop (.sqdmulh t a .v17),.vop (.mls a t .v16)] ++ vcsub a t ++
 [.vop (.sqdmulh t c .v17),.vop (.mls c t .v16)] ++ vcsub c t
def clearW : List Instr :=
 [.vop (.movi0 .v21),.vop (.movi0 .v22),.vop (.movi0 .v23),
 .vop (.movi0 .v25),.vop (.movi0 .v26),.vop (.movi0 .v27)]
def storeW : List Instr :=
 [.vop (.perm .uzp1 .h8 .v0 .v21 .v25),.vop (.perm .uzp1 .h8 .v1 .v23 .v27),
 .vop (.perm .zip1 .h8 .v2 .v0 .v1),.vop (.perm .zip2 .h8 .v3 .v0 .v1),
 .strq .v2 .x0 0,.strq .v3 .x0 16]
def bumpW : List Instr :=
 [.addImm .x .x0 .x0 32,.addImm .x .x3 .x3 32,.addImm .x .x12 .x12 32,.subImm .x .x11 .x11 1]
def bodyW (bf bg : Reg) (terms : List (Nat × Nat)) : List Instr :=
 clearW ++ terms.flatMap (termW bf bg) ++ [.ldrq .v18 .x3 0,.ldrq .v28 .x3 16] ++
 finishR .v21 .v22 .v23 .v18 .v24 ++ finishR .v25 .v26 .v27 .v28 .v24 ++ storeW ++ bumpW
def dotW (bo bf bg : Reg) (out : Nat) (terms : List (Nat × Nat)) : Prog isa :=
 .seq (.block (ptrTo .x0 bo out ++ vconsts ++
 [.adrSym .x3 "VG_MLKEM_GAMMA",.movz .x .x11 16 0,.movz .x .x12 0 0]))
 (.loop (.block (bodyW bf bg terms)) (.nonzero .x .x11))

end VG.Impl.MlKem.AArch64.DotW
