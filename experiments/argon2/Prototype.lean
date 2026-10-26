import VerifiedGarbage.Impl.Argon2.AArch64.Compress
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64 VG.Impl.Argon2.AArch64
namespace Trial
def seqs (xs : List (Prog isa)) : Prog isa := xs.foldr .seq (.block [])
def two_1_chunkAdd (a b t : Reg) : List Instr := addMul a b t
def two_1_chunkP : Prog isa := .block (two_1_chunkAdd (lane 0) (lane 4) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
two_1_chunkAdd (lane 8) (lane 12) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
two_1_chunkAdd (lane 0) (lane 4) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
two_1_chunkAdd (lane 8) (lane 12) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
two_1_chunkAdd (lane 1) (lane 5) .x17 ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
two_1_chunkAdd (lane 9) (lane 13) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
two_1_chunkAdd (lane 1) (lane 5) .x17 ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
two_1_chunkAdd (lane 9) (lane 13) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
two_1_chunkAdd (lane 2) (lane 6) .x17 ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
two_1_chunkAdd (lane 10) (lane 14) .x17 ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
two_1_chunkAdd (lane 2) (lane 6) .x17 ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
two_1_chunkAdd (lane 10) (lane 14) .x17 ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
two_1_chunkAdd (lane 3) (lane 7) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
two_1_chunkAdd (lane 11) (lane 15) .x17 ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
two_1_chunkAdd (lane 3) (lane 7) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
two_1_chunkAdd (lane 11) (lane 15) .x17 ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
two_1_chunkAdd (lane 0) (lane 5) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
two_1_chunkAdd (lane 10) (lane 15) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
two_1_chunkAdd (lane 0) (lane 5) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
two_1_chunkAdd (lane 10) (lane 15) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
two_1_chunkAdd (lane 1) (lane 6) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
two_1_chunkAdd (lane 11) (lane 12) .x17 ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
two_1_chunkAdd (lane 1) (lane 6) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
two_1_chunkAdd (lane 11) (lane 12) .x17 ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
two_1_chunkAdd (lane 2) (lane 7) .x17 ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
two_1_chunkAdd (lane 8) (lane 13) .x17 ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
two_1_chunkAdd (lane 2) (lane 7) .x17 ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
two_1_chunkAdd (lane 8) (lane 13) .x17 ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
two_1_chunkAdd (lane 3) (lane 4) .x17 ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
two_1_chunkAdd (lane 9) (lane 14) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
two_1_chunkAdd (lane 3) (lane 4) .x17 ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
two_1_chunkAdd (lane 9) (lane 14) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def two_1_chunkAt (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq two_1_chunkP (.block ((List.finRange 16).map (storeWord index))))
def two_1_chunk : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair),
 .block ([.vop (.dup .d2 .v16 .x2)] ++ []),
 seqs ((List.finRange 8).map (fun r => two_1_chunkAt (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => two_1_chunkAt (Spec.Argon2.colIndex c))),
 .block ([.umov .x .x2 .v16 0] ++ []),
 .block ((List.range 64).flatMap finishPair)]
def two_2_chunkAdd (a b t : Reg) : List Instr := addMul a b t
def two_2_chunkP : Prog isa := .block (two_2_chunkAdd (lane 0) (lane 4) .x17 ++
two_2_chunkAdd (lane 1) (lane 5) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
two_2_chunkAdd (lane 8) (lane 12) .x17 ++
two_2_chunkAdd (lane 9) (lane 13) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
two_2_chunkAdd (lane 0) (lane 4) .x17 ++
two_2_chunkAdd (lane 1) (lane 5) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
two_2_chunkAdd (lane 8) (lane 12) .x17 ++
two_2_chunkAdd (lane 9) (lane 13) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
two_2_chunkAdd (lane 2) (lane 6) .x17 ++
two_2_chunkAdd (lane 3) (lane 7) .x17 ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
two_2_chunkAdd (lane 10) (lane 14) .x17 ++
two_2_chunkAdd (lane 11) (lane 15) .x17 ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
two_2_chunkAdd (lane 2) (lane 6) .x17 ++
two_2_chunkAdd (lane 3) (lane 7) .x17 ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
two_2_chunkAdd (lane 10) (lane 14) .x17 ++
two_2_chunkAdd (lane 11) (lane 15) .x17 ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
two_2_chunkAdd (lane 0) (lane 5) .x17 ++
two_2_chunkAdd (lane 1) (lane 6) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
two_2_chunkAdd (lane 10) (lane 15) .x17 ++
two_2_chunkAdd (lane 11) (lane 12) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
two_2_chunkAdd (lane 0) (lane 5) .x17 ++
two_2_chunkAdd (lane 1) (lane 6) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
two_2_chunkAdd (lane 10) (lane 15) .x17 ++
two_2_chunkAdd (lane 11) (lane 12) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
two_2_chunkAdd (lane 2) (lane 7) .x17 ++
two_2_chunkAdd (lane 3) (lane 4) .x17 ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
two_2_chunkAdd (lane 8) (lane 13) .x17 ++
two_2_chunkAdd (lane 9) (lane 14) .x17 ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
two_2_chunkAdd (lane 2) (lane 7) .x17 ++
two_2_chunkAdd (lane 3) (lane 4) .x17 ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
two_2_chunkAdd (lane 8) (lane 13) .x17 ++
two_2_chunkAdd (lane 9) (lane 14) .x17 ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def two_2_chunkAt (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq two_2_chunkP (.block ((List.finRange 16).map (storeWord index))))
def two_2_chunk : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair),
 .block ([.vop (.dup .d2 .v16 .x2)] ++ []),
 seqs ((List.finRange 8).map (fun r => two_2_chunkAt (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => two_2_chunkAt (Spec.Argon2.colIndex c))),
 .block ([.umov .x .x2 .v16 0] ++ []),
 .block ((List.range 64).flatMap finishPair)]
def two_2_stripeAdd (a b t : Reg) : List Instr := addMul a b t
def two_2_stripeP : Prog isa := .block (([(((two_2_stripeAdd (lane 0) (lane 4) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 1) (lane 5) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 0) (lane 4) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 1) (lane 5) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 0) (lane 4) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 1) (lane 5) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 8) (lane 12) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 9) (lane 13) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 8) (lane 12) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 9) (lane 13) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 8) (lane 12) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 9) (lane 13) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 0) (lane 4) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 1) (lane 5) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 0) (lane 4) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 1) (lane 5) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 0) (lane 4) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 1) (lane 5) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 8) (lane 12) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 9) (lane 13) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 8) (lane 12) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 9) (lane 13) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 8) (lane 12) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 9) (lane 13) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 2) (lane 6) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 3) (lane 7) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 2) (lane 6) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 3) (lane 7) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 2) (lane 6) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 3) (lane 7) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 10) (lane 14) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 11) (lane 15) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 10) (lane 14) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 11) (lane 15) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 10) (lane 14) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 11) (lane 15) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 2) (lane 6) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 3) (lane 7) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 2) (lane 6) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 3) (lane 7) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 2) (lane 6) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 3) (lane 7) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 10) (lane 14) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 11) (lane 15) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 10) (lane 14) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 11) (lane 15) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 10) (lane 14) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 11) (lane 15) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 0) (lane 5) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 1) (lane 6) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 0) (lane 5) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 1) (lane 6) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 0) (lane 5) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 1) (lane 6) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 10) (lane 15) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 11) (lane 12) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 10) (lane 15) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 11) (lane 12) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 10) (lane 15) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 11) (lane 12) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 0) (lane 5) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 1) (lane 6) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 0) (lane 5) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 1) (lane 6) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 0) (lane 5) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 1) (lane 6) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 10) (lane 15) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 11) (lane 12) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 10) (lane 15) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 11) (lane 12) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 10) (lane 15) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 11) (lane 12) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 2) (lane 7) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 3) (lane 4) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 2) (lane 7) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 3) (lane 4) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 2) (lane 7) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 3) (lane 4) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 8) (lane 13) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 9) (lane 14) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 8) (lane 13) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 9) (lane 14) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 8) (lane 13) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 9) (lane 14) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 2) (lane 7) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 3) (lane 4) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 2) (lane 7) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 3) (lane 4) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 2) (lane 7) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 3) (lane 4) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_2_stripeAdd (lane 8) (lane 13) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 9) (lane 14) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 8) (lane 13) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 9) (lane 14) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 8) (lane 13) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_2_stripeAdd (lane 9) (lane 14) .x19)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]))
def two_2_stripeAt (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq two_2_stripeP (.block ((List.finRange 16).map (storeWord index))))
def two_2_stripe : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair),
 .block ([.vop (.dup .d2 .v16 .x2)] ++ [.vop (.dup .d2 .v17 .x19)]),
 seqs ((List.finRange 8).map (fun r => two_2_stripeAt (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => two_2_stripeAt (Spec.Argon2.colIndex c))),
 .block ([.umov .x .x2 .v16 0] ++ [.umov .x .x19 .v17 0]),
 .block ((List.range 64).flatMap finishPair)]
def two_4_chunkAdd (a b t : Reg) : List Instr := addMul a b t
def two_4_chunkP : Prog isa := .block (two_4_chunkAdd (lane 0) (lane 4) .x17 ++
two_4_chunkAdd (lane 1) (lane 5) .x17 ++
two_4_chunkAdd (lane 2) (lane 6) .x17 ++
two_4_chunkAdd (lane 3) (lane 7) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
two_4_chunkAdd (lane 8) (lane 12) .x17 ++
two_4_chunkAdd (lane 9) (lane 13) .x17 ++
two_4_chunkAdd (lane 10) (lane 14) .x17 ++
two_4_chunkAdd (lane 11) (lane 15) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
two_4_chunkAdd (lane 0) (lane 4) .x17 ++
two_4_chunkAdd (lane 1) (lane 5) .x17 ++
two_4_chunkAdd (lane 2) (lane 6) .x17 ++
two_4_chunkAdd (lane 3) (lane 7) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
two_4_chunkAdd (lane 8) (lane 12) .x17 ++
two_4_chunkAdd (lane 9) (lane 13) .x17 ++
two_4_chunkAdd (lane 10) (lane 14) .x17 ++
two_4_chunkAdd (lane 11) (lane 15) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
two_4_chunkAdd (lane 0) (lane 5) .x17 ++
two_4_chunkAdd (lane 1) (lane 6) .x17 ++
two_4_chunkAdd (lane 2) (lane 7) .x17 ++
two_4_chunkAdd (lane 3) (lane 4) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
two_4_chunkAdd (lane 10) (lane 15) .x17 ++
two_4_chunkAdd (lane 11) (lane 12) .x17 ++
two_4_chunkAdd (lane 8) (lane 13) .x17 ++
two_4_chunkAdd (lane 9) (lane 14) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
two_4_chunkAdd (lane 0) (lane 5) .x17 ++
two_4_chunkAdd (lane 1) (lane 6) .x17 ++
two_4_chunkAdd (lane 2) (lane 7) .x17 ++
two_4_chunkAdd (lane 3) (lane 4) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
two_4_chunkAdd (lane 10) (lane 15) .x17 ++
two_4_chunkAdd (lane 11) (lane 12) .x17 ++
two_4_chunkAdd (lane 8) (lane 13) .x17 ++
two_4_chunkAdd (lane 9) (lane 14) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def two_4_chunkAt (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq two_4_chunkP (.block ((List.finRange 16).map (storeWord index))))
def two_4_chunk : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair),
 .block ([.vop (.dup .d2 .v16 .x2)] ++ []),
 seqs ((List.finRange 8).map (fun r => two_4_chunkAt (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => two_4_chunkAt (Spec.Argon2.colIndex c))),
 .block ([.umov .x .x2 .v16 0] ++ []),
 .block ((List.range 64).flatMap finishPair)]
def two_4_stripeAdd (a b t : Reg) : List Instr := addMul a b t
def two_4_stripeP : Prog isa := .block (([(((two_4_stripeAdd (lane 0) (lane 4) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 1) (lane 5) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 2) (lane 6) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 3) (lane 7) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 0) (lane 4) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 1) (lane 5) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 2) (lane 6) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 3) (lane 7) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 0) (lane 4) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 1) (lane 5) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 2) (lane 6) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 3) (lane 7) .x21)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_4_stripeAdd (lane 8) (lane 12) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 9) (lane 13) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 10) (lane 14) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 11) (lane 15) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 8) (lane 12) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 9) (lane 13) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 10) (lane 14) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 11) (lane 15) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 8) (lane 12) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 9) (lane 13) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 10) (lane 14) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 11) (lane 15) .x21)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_4_stripeAdd (lane 0) (lane 4) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 1) (lane 5) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 2) (lane 6) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 3) (lane 7) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 0) (lane 4) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 1) (lane 5) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 2) (lane 6) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 3) (lane 7) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 0) (lane 4) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 1) (lane 5) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 2) (lane 6) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 3) (lane 7) .x21)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_4_stripeAdd (lane 8) (lane 12) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 9) (lane 13) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 10) (lane 14) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 11) (lane 15) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 8) (lane 12) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 9) (lane 13) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 10) (lane 14) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 11) (lane 15) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 8) (lane 12) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 9) (lane 13) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 10) (lane 14) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 11) (lane 15) .x21)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_4_stripeAdd (lane 0) (lane 5) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 1) (lane 6) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 2) (lane 7) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 3) (lane 4) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 0) (lane 5) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 1) (lane 6) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 2) (lane 7) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 3) (lane 4) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 0) (lane 5) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 1) (lane 6) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 2) (lane 7) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 3) (lane 4) .x21)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_4_stripeAdd (lane 10) (lane 15) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 11) (lane 12) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 8) (lane 13) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 9) (lane 14) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 10) (lane 15) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 11) (lane 12) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 8) (lane 13) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 9) (lane 14) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 10) (lane 15) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 11) (lane 12) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 8) (lane 13) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 9) (lane 14) .x21)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_4_stripeAdd (lane 0) (lane 5) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 1) (lane 6) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 2) (lane 7) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 3) (lane 4) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 0) (lane 5) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 1) (lane 6) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 2) (lane 7) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 3) (lane 4) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 0) (lane 5) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 1) (lane 6) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 2) (lane 7) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 3) (lane 4) .x21)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((two_4_stripeAdd (lane 10) (lane 15) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 11) (lane 12) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 8) (lane 13) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 9) (lane 14) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 10) (lane 15) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 11) (lane 12) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 8) (lane 13) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 9) (lane 14) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 10) (lane 15) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 11) (lane 12) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 8) (lane 13) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((two_4_stripeAdd (lane 9) (lane 14) .x21)).getD 2 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]))
def two_4_stripeAt (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq two_4_stripeP (.block ((List.finRange 16).map (storeWord index))))
def two_4_stripe : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair),
 .block ([.vop (.dup .d2 .v16 .x2)] ++ [.vop (.dup .d2 .v17 .x19), .vop (.dup .d2 .v18 .x20), .vop (.dup .d2 .v19 .x21)]),
 seqs ((List.finRange 8).map (fun r => two_4_stripeAt (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => two_4_stripeAt (Spec.Argon2.colIndex c))),
 .block ([.umov .x .x2 .v16 0] ++ [.umov .x .x19 .v17 0, .umov .x .x20 .v18 0, .umov .x .x21 .v19 0]),
 .block ((List.range 64).flatMap finishPair)]
def one_1_chunkAdd (a b t : Reg) : List Instr := [.umull t a b, .add .x a a b, .add .x a a t, .add .x a a t]
def one_1_chunkP : Prog isa := .block (one_1_chunkAdd (lane 0) (lane 4) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
one_1_chunkAdd (lane 8) (lane 12) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
one_1_chunkAdd (lane 0) (lane 4) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
one_1_chunkAdd (lane 8) (lane 12) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
one_1_chunkAdd (lane 1) (lane 5) .x17 ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
one_1_chunkAdd (lane 9) (lane 13) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
one_1_chunkAdd (lane 1) (lane 5) .x17 ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
one_1_chunkAdd (lane 9) (lane 13) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
one_1_chunkAdd (lane 2) (lane 6) .x17 ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
one_1_chunkAdd (lane 10) (lane 14) .x17 ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
one_1_chunkAdd (lane 2) (lane 6) .x17 ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
one_1_chunkAdd (lane 10) (lane 14) .x17 ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
one_1_chunkAdd (lane 3) (lane 7) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
one_1_chunkAdd (lane 11) (lane 15) .x17 ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
one_1_chunkAdd (lane 3) (lane 7) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
one_1_chunkAdd (lane 11) (lane 15) .x17 ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
one_1_chunkAdd (lane 0) (lane 5) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
one_1_chunkAdd (lane 10) (lane 15) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
one_1_chunkAdd (lane 0) (lane 5) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
one_1_chunkAdd (lane 10) (lane 15) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
one_1_chunkAdd (lane 1) (lane 6) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
one_1_chunkAdd (lane 11) (lane 12) .x17 ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
one_1_chunkAdd (lane 1) (lane 6) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
one_1_chunkAdd (lane 11) (lane 12) .x17 ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
one_1_chunkAdd (lane 2) (lane 7) .x17 ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
one_1_chunkAdd (lane 8) (lane 13) .x17 ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
one_1_chunkAdd (lane 2) (lane 7) .x17 ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
one_1_chunkAdd (lane 8) (lane 13) .x17 ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
one_1_chunkAdd (lane 3) (lane 4) .x17 ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
one_1_chunkAdd (lane 9) (lane 14) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
one_1_chunkAdd (lane 3) (lane 4) .x17 ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
one_1_chunkAdd (lane 9) (lane 14) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def one_1_chunkAt (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq one_1_chunkP (.block ((List.finRange 16).map (storeWord index))))
def one_1_chunk : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair),
 .block ([.vop (.dup .d2 .v16 .x2)] ++ []),
 seqs ((List.finRange 8).map (fun r => one_1_chunkAt (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => one_1_chunkAt (Spec.Argon2.colIndex c))),
 .block ([.umov .x .x2 .v16 0] ++ []),
 .block ((List.range 64).flatMap finishPair)]
def one_2_chunkAdd (a b t : Reg) : List Instr := [.umull t a b, .add .x a a b, .add .x a a t, .add .x a a t]
def one_2_chunkP : Prog isa := .block (one_2_chunkAdd (lane 0) (lane 4) .x17 ++
one_2_chunkAdd (lane 1) (lane 5) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
one_2_chunkAdd (lane 8) (lane 12) .x17 ++
one_2_chunkAdd (lane 9) (lane 13) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
one_2_chunkAdd (lane 0) (lane 4) .x17 ++
one_2_chunkAdd (lane 1) (lane 5) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
one_2_chunkAdd (lane 8) (lane 12) .x17 ++
one_2_chunkAdd (lane 9) (lane 13) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
one_2_chunkAdd (lane 2) (lane 6) .x17 ++
one_2_chunkAdd (lane 3) (lane 7) .x17 ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
one_2_chunkAdd (lane 10) (lane 14) .x17 ++
one_2_chunkAdd (lane 11) (lane 15) .x17 ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
one_2_chunkAdd (lane 2) (lane 6) .x17 ++
one_2_chunkAdd (lane 3) (lane 7) .x17 ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
one_2_chunkAdd (lane 10) (lane 14) .x17 ++
one_2_chunkAdd (lane 11) (lane 15) .x17 ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
one_2_chunkAdd (lane 0) (lane 5) .x17 ++
one_2_chunkAdd (lane 1) (lane 6) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
one_2_chunkAdd (lane 10) (lane 15) .x17 ++
one_2_chunkAdd (lane 11) (lane 12) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
one_2_chunkAdd (lane 0) (lane 5) .x17 ++
one_2_chunkAdd (lane 1) (lane 6) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
one_2_chunkAdd (lane 10) (lane 15) .x17 ++
one_2_chunkAdd (lane 11) (lane 12) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
one_2_chunkAdd (lane 2) (lane 7) .x17 ++
one_2_chunkAdd (lane 3) (lane 4) .x17 ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
one_2_chunkAdd (lane 8) (lane 13) .x17 ++
one_2_chunkAdd (lane 9) (lane 14) .x17 ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
one_2_chunkAdd (lane 2) (lane 7) .x17 ++
one_2_chunkAdd (lane 3) (lane 4) .x17 ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
one_2_chunkAdd (lane 8) (lane 13) .x17 ++
one_2_chunkAdd (lane 9) (lane 14) .x17 ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def one_2_chunkAt (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq one_2_chunkP (.block ((List.finRange 16).map (storeWord index))))
def one_2_chunk : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair),
 .block ([.vop (.dup .d2 .v16 .x2)] ++ []),
 seqs ((List.finRange 8).map (fun r => one_2_chunkAt (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => one_2_chunkAt (Spec.Argon2.colIndex c))),
 .block ([.umov .x .x2 .v16 0] ++ []),
 .block ((List.range 64).flatMap finishPair)]
def one_2_stripeAdd (a b t : Reg) : List Instr := [.umull t a b, .add .x a a b, .add .x a a t, .add .x a a t]
def one_2_stripeP : Prog isa := .block (([(((one_2_stripeAdd (lane 0) (lane 4) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 5) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 0) (lane 4) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 5) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 0) (lane 4) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 5) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 0) (lane 4) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 5) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 8) (lane 12) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 13) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 8) (lane 12) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 13) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 8) (lane 12) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 13) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 8) (lane 12) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 13) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 0) (lane 4) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 5) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 0) (lane 4) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 5) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 0) (lane 4) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 5) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 0) (lane 4) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 5) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 8) (lane 12) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 13) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 8) (lane 12) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 13) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 8) (lane 12) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 13) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 8) (lane 12) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 13) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 2) (lane 6) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 7) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 2) (lane 6) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 7) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 2) (lane 6) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 7) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 2) (lane 6) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 7) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 10) (lane 14) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 15) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 10) (lane 14) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 15) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 10) (lane 14) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 15) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 10) (lane 14) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 15) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 2) (lane 6) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 7) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 2) (lane 6) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 7) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 2) (lane 6) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 7) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 2) (lane 6) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 7) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 10) (lane 14) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 15) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 10) (lane 14) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 15) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 10) (lane 14) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 15) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 10) (lane 14) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 15) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 0) (lane 5) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 6) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 0) (lane 5) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 6) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 0) (lane 5) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 6) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 0) (lane 5) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 6) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 10) (lane 15) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 12) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 10) (lane 15) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 12) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 10) (lane 15) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 12) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 10) (lane 15) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 12) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 0) (lane 5) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 6) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 0) (lane 5) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 6) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 0) (lane 5) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 6) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 0) (lane 5) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 1) (lane 6) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 10) (lane 15) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 12) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 10) (lane 15) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 12) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 10) (lane 15) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 12) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 10) (lane 15) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 11) (lane 12) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 2) (lane 7) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 4) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 2) (lane 7) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 4) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 2) (lane 7) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 4) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 2) (lane 7) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 4) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 8) (lane 13) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 14) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 8) (lane 13) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 14) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 8) (lane 13) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 14) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 8) (lane 13) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 14) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 2) (lane 7) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 4) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 2) (lane 7) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 4) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 2) (lane 7) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 4) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 2) (lane 7) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 3) (lane 4) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_2_stripeAdd (lane 8) (lane 13) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 14) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 8) (lane 13) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 14) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 8) (lane 13) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 14) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 8) (lane 13) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_2_stripeAdd (lane 9) (lane 14) .x19)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]))
def one_2_stripeAt (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq one_2_stripeP (.block ((List.finRange 16).map (storeWord index))))
def one_2_stripe : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair),
 .block ([.vop (.dup .d2 .v16 .x2)] ++ [.vop (.dup .d2 .v17 .x19)]),
 seqs ((List.finRange 8).map (fun r => one_2_stripeAt (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => one_2_stripeAt (Spec.Argon2.colIndex c))),
 .block ([.umov .x .x2 .v16 0] ++ [.umov .x .x19 .v17 0]),
 .block ((List.range 64).flatMap finishPair)]
def one_4_chunkAdd (a b t : Reg) : List Instr := [.umull t a b, .add .x a a b, .add .x a a t, .add .x a a t]
def one_4_chunkP : Prog isa := .block (one_4_chunkAdd (lane 0) (lane 4) .x17 ++
one_4_chunkAdd (lane 1) (lane 5) .x17 ++
one_4_chunkAdd (lane 2) (lane 6) .x17 ++
one_4_chunkAdd (lane 3) (lane 7) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
one_4_chunkAdd (lane 8) (lane 12) .x17 ++
one_4_chunkAdd (lane 9) (lane 13) .x17 ++
one_4_chunkAdd (lane 10) (lane 14) .x17 ++
one_4_chunkAdd (lane 11) (lane 15) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
one_4_chunkAdd (lane 0) (lane 4) .x17 ++
one_4_chunkAdd (lane 1) (lane 5) .x17 ++
one_4_chunkAdd (lane 2) (lane 6) .x17 ++
one_4_chunkAdd (lane 3) (lane 7) .x17 ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
one_4_chunkAdd (lane 8) (lane 12) .x17 ++
one_4_chunkAdd (lane 9) (lane 13) .x17 ++
one_4_chunkAdd (lane 10) (lane 14) .x17 ++
one_4_chunkAdd (lane 11) (lane 15) .x17 ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
one_4_chunkAdd (lane 0) (lane 5) .x17 ++
one_4_chunkAdd (lane 1) (lane 6) .x17 ++
one_4_chunkAdd (lane 2) (lane 7) .x17 ++
one_4_chunkAdd (lane 3) (lane 4) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
one_4_chunkAdd (lane 10) (lane 15) .x17 ++
one_4_chunkAdd (lane 11) (lane 12) .x17 ++
one_4_chunkAdd (lane 8) (lane 13) .x17 ++
one_4_chunkAdd (lane 9) (lane 14) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
one_4_chunkAdd (lane 0) (lane 5) .x17 ++
one_4_chunkAdd (lane 1) (lane 6) .x17 ++
one_4_chunkAdd (lane 2) (lane 7) .x17 ++
one_4_chunkAdd (lane 3) (lane 4) .x17 ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
one_4_chunkAdd (lane 10) (lane 15) .x17 ++
one_4_chunkAdd (lane 11) (lane 12) .x17 ++
one_4_chunkAdd (lane 8) (lane 13) .x17 ++
one_4_chunkAdd (lane 9) (lane 14) .x17 ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def one_4_chunkAt (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq one_4_chunkP (.block ((List.finRange 16).map (storeWord index))))
def one_4_chunk : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair),
 .block ([.vop (.dup .d2 .v16 .x2)] ++ []),
 seqs ((List.finRange 8).map (fun r => one_4_chunkAt (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => one_4_chunkAt (Spec.Argon2.colIndex c))),
 .block ([.umov .x .x2 .v16 0] ++ []),
 .block ((List.range 64).flatMap finishPair)]
def one_4_stripeAdd (a b t : Reg) : List Instr := [.umull t a b, .add .x a a b, .add .x a a t, .add .x a a t]
def one_4_stripeP : Prog isa := .block (([(((one_4_stripeAdd (lane 0) (lane 4) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 5) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 6) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 7) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 0) (lane 4) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 5) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 6) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 7) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 0) (lane 4) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 5) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 6) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 7) .x21)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 0) (lane 4) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 5) .x19)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 6) .x20)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 7) .x21)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_4_stripeAdd (lane 8) (lane 12) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 13) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 14) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 15) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 12) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 13) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 14) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 15) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 12) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 13) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 14) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 15) .x21)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 12) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 13) .x19)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 14) .x20)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 15) .x21)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_4_stripeAdd (lane 0) (lane 4) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 5) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 6) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 7) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 0) (lane 4) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 5) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 6) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 7) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 0) (lane 4) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 5) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 6) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 7) .x21)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 0) (lane 4) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 5) .x19)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 6) .x20)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 7) .x21)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_4_stripeAdd (lane 8) (lane 12) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 13) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 14) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 15) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 12) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 13) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 14) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 15) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 12) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 13) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 14) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 15) .x21)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 12) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 13) .x19)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 14) .x20)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 15) .x21)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_4_stripeAdd (lane 0) (lane 5) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 6) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 7) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 4) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 0) (lane 5) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 6) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 7) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 4) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 0) (lane 5) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 6) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 7) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 4) .x21)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 0) (lane 5) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 6) .x19)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 7) .x20)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 4) .x21)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_4_stripeAdd (lane 10) (lane 15) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 12) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 13) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 14) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 15) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 12) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 13) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 14) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 15) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 12) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 13) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 14) .x21)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 15) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 12) .x19)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 13) .x20)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 14) .x21)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_4_stripeAdd (lane 0) (lane 5) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 6) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 7) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 4) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 0) (lane 5) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 6) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 7) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 4) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 0) (lane 5) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 6) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 7) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 4) .x21)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 0) (lane 5) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 1) (lane 6) .x19)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 2) (lane 7) .x20)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 3) (lane 4) .x21)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]) ++
([(((one_4_stripeAdd (lane 10) (lane 15) .x17)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 12) .x19)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 13) .x20)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 14) .x21)).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 15) .x17)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 12) .x19)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 13) .x20)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 14) .x21)).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 15) .x17)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 12) .x19)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 13) .x20)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 14) .x21)).getD 2 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 10) (lane 15) .x17)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 11) (lane 12) .x19)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 8) (lane 13) .x20)).getD 3 (.add .x .x0 .x0 .x0))] ++ [(((one_4_stripeAdd (lane 9) (lane 14) .x21)).getD 3 (.add .x .x0 .x0 .x0))]) ++
([(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 0 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))] ++ [(((([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))).getD 1 (.add .x .x0 .x0 .x0))]))
def one_4_stripeAt (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq one_4_stripeP (.block ((List.finRange 16).map (storeWord index))))
def one_4_stripe : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair),
 .block ([.vop (.dup .d2 .v16 .x2)] ++ [.vop (.dup .d2 .v17 .x19), .vop (.dup .d2 .v18 .x20), .vop (.dup .d2 .v19 .x21)]),
 seqs ((List.finRange 8).map (fun r => one_4_stripeAt (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => one_4_stripeAt (Spec.Argon2.colIndex c))),
 .block ([.umov .x .x2 .v16 0] ++ [.umov .x .x19 .v17 0, .umov .x .x20 .v18 0, .umov .x .x21 .v19 0]),
 .block ((List.range 64).flatMap finishPair)]
def emit (name : String) (p : Prog isa) (apple : Bool) : String :=
 let pre := if apple then "_" else ""
 ".p2align 6\n.globl " ++ pre ++ name ++ "\n" ++ pre ++ name ++ ":\n" ++
 String.intercalate "\n" ((printer.function p).map fun l => match l with
 | .text s => s | .call n => "bl " ++ pre ++ n | .sym .. => "ERROR") ++ "\n"
def main : IO Unit := do
 IO.FS.writeFile "/tmp/vg-argon2-arm64/prototypes-apple.S" (".text\n" ++ String.join ([("trial_base",compress),("trial_two_1_chunk",two_1_chunk),("trial_two_2_chunk",two_2_chunk),("trial_two_2_stripe",two_2_stripe),("trial_two_4_chunk",two_4_chunk),("trial_two_4_stripe",two_4_stripe),("trial_one_1_chunk",one_1_chunk),("trial_one_2_chunk",one_2_chunk),("trial_one_2_stripe",one_2_stripe),("trial_one_4_chunk",one_4_chunk),("trial_one_4_stripe",one_4_stripe)].map fun (n,p) => emit n p true))
 IO.FS.writeFile "/tmp/vg-argon2-arm64/prototypes-linux.S" (".text\n" ++ String.join ([("trial_base",compress),("trial_two_1_chunk",two_1_chunk),("trial_two_2_chunk",two_2_chunk),("trial_two_2_stripe",two_2_stripe),("trial_two_4_chunk",two_4_chunk),("trial_two_4_stripe",two_4_stripe),("trial_one_1_chunk",one_1_chunk),("trial_one_2_chunk",one_2_chunk),("trial_one_2_stripe",one_2_stripe),("trial_one_4_chunk",one_4_chunk),("trial_one_4_stripe",one_4_stripe)].map fun (n,p) => emit n p false))
end Trial
def main := Trial.main
