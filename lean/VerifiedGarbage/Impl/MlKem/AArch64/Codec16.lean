module
public import VerifiedGarbage.Impl.MlKem.AArch64.Compress
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt


/-! # Eight ML-KEM coefficients encoded or decoded per iteration -/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Codec16
open VG VG.AArch64

def maskVec (v : VReg) (xs : List Nat) : List Instr :=
 let word (start : Nat) := (List.range 8).foldl (fun a i => a + (xs.getD (start+i) 255)*2^(8*i)) 0
 movImm .x9 (BitVec.ofNat 64 (word 0)) ++ [.vop (.dup .d2 v .x9)] ++
 movImm .x9 (BitVec.ofNat 64 (word 8)) ++ [.vop (.ins .d2 v 1 .x9)]
def encMath : List Instr :=
 [.vop (.perm .uzp1 .s4 .v2 .v0 .v1),.vop (.perm .uzp2 .s4 .v3 .v0 .v1),
 .vop (.shift .shl .s4 .v3 .v3 12),.vop (.logic .orr .v2 .v2 .v3),.vop (.tbl .v0 .v2 .v16),
 .umov .x .x9 .v0 0,.umov .x .x10 .v0 1]
def decMath : List Instr :=
 [.vop (.dup .d2 .v0 .x9),.vop (.ins .d2 .v0 1 .x10),
 .vop (.tbl .v1 .v0 .v16),.vop (.logic .and .v2 .v1 .v17),.vop (.shift .ushr .s4 .v3 .v1 12),
 .vop (.sub .s4 .v4 .v2 .v18),.vop (.umin .v2 .v2 .v4),.vop (.sub .s4 .v4 .v3 .v18),.vop (.umin .v3 .v3 .v4),
 .vop (.perm .zip1 .s4 .v0 .v2 .v3),.vop (.perm .zip2 .s4 .v1 .v2 .v3)]

end VG.Impl.MlKem.AArch64.Codec16
