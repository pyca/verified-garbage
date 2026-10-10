import VerifiedGarbage.TCB.AArch64.Isa

/-! Fixed-address selection of X, Y, Z, Z² and Z³ from sixteen rows. -/
namespace VG.Impl.P256.EcdhSelect
open VG VG.AArch64

def vectorAcc : List VReg :=
  [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v16,.v17]

def vectorLoad : List VReg :=
  [.v18,.v19,.v20,.v21,.v22,.v23,.v24,.v25,.v26,.v27]

/-- Ten vector accumulators fit the full cached point without v8–v15. -/
def neon (tbl out cache : Nat) : List Instr :=
  ([.movz .x .x5 1 0,.vop (.dup .d2 .v31 .x5),.vop (.dup .d2 .v30 .x2),.vop (.movi0 .v28)] : List Instr) ++
  vectorAcc.map (fun r => .vop (.movi0 r)) ++
  (List.range 16).flatMap (fun row =>
    ([.vop (.add .d2 .v28 .v28 .v31),.vop (.cmeq .d2 .v29 .v28 .v30)] : List Instr) ++
      (List.range 10).map (fun i => .ldrq (vectorLoad.getD i .v18) .x0 (tbl+160*row+16*i)) ++
      (List.range 10).map (fun i => .vop (.bsel .bit (vectorAcc.getD i .v0) (vectorLoad.getD i .v18) .v29))) ++
  (List.range 6).map (fun i => .strq (vectorAcc.getD i .v0) .x0 (out+16*i)) ++
  ([.movz .x .x17 (BitVec.ofNat 16 cache) 0,.add .x .x17 .x0 .x17] : List Instr) ++
  (List.range 4).map (fun i => .strq (vectorAcc.getD (i+6) .v0) .x17 (16*i))


end VG.Impl.P256.EcdhSelect
