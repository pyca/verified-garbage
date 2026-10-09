import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector

namespace VG.Impl.MlDsa.AArch64.Optimized.KeccakMix
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Sha3.Vector

/-- The measured N2 schedule replaces ten BCAX operations with BIC/EOR
pairs to distribute work beyond the single crypto execution pipeline. -/
def chi : List Op := [.bcax .v20 .v26 .v22 .v8,
.bcax .v21 .v8 .v23 .v22,
.bic .v7 .v24 .v23,
.xor .v22 .v22 .v7,
.bcax .v23 .v23 .v26 .v24,
.bic .v7 .v8 .v26,
.xor .v24 .v24 .v7,
.bcax .v17 .v30 .v19 .v3,
.bcax .v18 .v3 .v15 .v19,
.bic .v7 .v16 .v15,
.xor .v19 .v19 .v7,
.bcax .v15 .v15 .v30 .v16,
.bic .v3 .v3 .v30,
.xor .v16 .v16 .v3,
.bcax .v10 .v25 .v12 .v31,
.bcax .v11 .v31 .v13 .v12,
.bic .v3 .v14 .v13,
.xor .v12 .v12 .v3,
.bcax .v13 .v13 .v25 .v14,
.bic .v3 .v31 .v25,
.xor .v14 .v14 .v3,
.bcax .v7 .v29 .v9 .v4,
.bcax .v8 .v4 .v5 .v9,
.bic .v3 .v6 .v5,
.xor .v9 .v9 .v3,
.bcax .v5 .v5 .v29 .v6,
.bic .v3 .v4 .v29,
.xor .v6 .v6 .v3,
.bcax .v3 .v27 .v0 .v28,
.bcax .v4 .v28 .v1 .v0,
.bic .v25 .v2 .v1,
.xor .v0 .v0 .v25,
.bcax .v1 .v1 .v27 .v2,
.bic .v25 .v28 .v27,
.xor .v2 .v2 .v25]

def round (r : Nat) : List Instr :=
  constant (Spec.Sha3.RC r) ++ theta.map Op.instr ++ rhoPi.map Op.instr ++ chi.map Op.instr ++ iota

def rounds : List Instr := (List.range 24).flatMap round
end VG.Impl.MlDsa.AArch64.Optimized.KeccakMix
