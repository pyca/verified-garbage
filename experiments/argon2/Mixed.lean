import VerifiedGarbage.Impl.Argon2.AArch64.Compress
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64 VG.Impl.Argon2.AArch64
namespace Trial
def seqs (xs : List (Prog isa)) : Prog isa := xs.foldr .seq (.block [])
def once (a b : Reg) : List Instr :=
 [.umull .x17 a b, .add .x a a b, .add .x a a .x17, .add .x a a .x17]
def mixed_0_0P : Prog isa := .block ((fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_0_0At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_0_0P (.block ((List.finRange 16).map (storeWord index))))
def mixed_0_0 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_0_0At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_0_0At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_1_1P : Prog isa := .block ((once) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(once) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(once) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(once) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(once) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(once) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(once) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(once) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_1_1At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_1_1P (.block ((List.finRange 16).map (storeWord index))))
def mixed_1_1 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_1_1At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_1_1At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_2_2P : Prog isa := .block ((fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_2_2At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_2_2P (.block ((List.finRange 16).map (storeWord index))))
def mixed_2_2 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_2_2At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_2_2At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_4_4P : Prog isa := .block ((fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_4_4At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_4_4P (.block ((List.finRange 16).map (storeWord index))))
def mixed_4_4 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_4_4At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_4_4At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_8_8P : Prog isa := .block ((fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_8_8At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_8_8P (.block ((List.finRange 16).map (storeWord index))))
def mixed_8_8 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_8_8At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_8_8At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_3_3P : Prog isa := .block ((once) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(once) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(once) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(once) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(once) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(once) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(once) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(once) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_3_3At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_3_3P (.block ((List.finRange 16).map (storeWord index))))
def mixed_3_3 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_3_3At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_3_3At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_5_5P : Prog isa := .block ((once) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(once) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(once) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(once) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(once) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(once) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(once) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(once) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_5_5At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_5_5P (.block ((List.finRange 16).map (storeWord index))))
def mixed_5_5 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_5_5At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_5_5At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_6_6P : Prog isa := .block ((fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_6_6At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_6_6P (.block ((List.finRange 16).map (storeWord index))))
def mixed_6_6 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_6_6At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_6_6At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_9_9P : Prog isa := .block ((once) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(once) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(once) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(once) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(once) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(once) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(once) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(once) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_9_9At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_9_9P (.block ((List.finRange 16).map (storeWord index))))
def mixed_9_9 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_9_9At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_9_9At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_10_10P : Prog isa := .block ((fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_10_10At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_10_10P (.block ((List.finRange 16).map (storeWord index))))
def mixed_10_10 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_10_10At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_10_10At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_12_12P : Prog isa := .block ((fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_12_12At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_12_12P (.block ((List.finRange 16).map (storeWord index))))
def mixed_12_12 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_12_12At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_12_12At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_7_7P : Prog isa := .block ((once) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(once) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(once) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(once) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(once) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(once) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(once) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(once) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_7_7At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_7_7P (.block ((List.finRange 16).map (storeWord index))))
def mixed_7_7 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_7_7At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_7_7At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_11_11P : Prog isa := .block ((once) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(once) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(once) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(once) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(once) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(once) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(once) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(once) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_11_11At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_11_11P (.block ((List.finRange 16).map (storeWord index))))
def mixed_11_11 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_11_11At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_11_11At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_13_13P : Prog isa := .block ((once) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(once) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(once) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(once) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(once) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(once) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(once) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(once) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_13_13At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_13_13P (.block ((List.finRange 16).map (storeWord index))))
def mixed_13_13 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_13_13At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_13_13At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_14_14P : Prog isa := .block ((fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_14_14At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_14_14P (.block ((List.finRange 16).map (storeWord index))))
def mixed_14_14 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_14_14At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_14_14At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_15_15P : Prog isa := .block ((once) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(once) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(once) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(once) (lane 2) (lane 6) ++
(once) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(once) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(once) (lane 10) (lane 14) ++
(once) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(once) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(once) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(once) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(once) (lane 2) (lane 7) ++
(once) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(once) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(once) (lane 8) (lane 13) ++
(once) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_15_15At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_15_15P (.block ((List.finRange 16).map (storeWord index))))
def mixed_15_15 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_15_15At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_15_15At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_0_1P : Prog isa := .block ((fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(once) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(once) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(once) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(once) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_0_1At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_0_1P (.block ((List.finRange 16).map (storeWord index))))
def mixed_0_1 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_0_1At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_0_1At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_1_0P : Prog isa := .block ((once) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(once) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(once) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(once) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_1_0At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_1_0P (.block ((List.finRange 16).map (storeWord index))))
def mixed_1_0 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_1_0At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_1_0At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_0_3P : Prog isa := .block ((fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(once) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(once) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(once) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(once) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_0_3At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_0_3P (.block ((List.finRange 16).map (storeWord index))))
def mixed_0_3 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_0_3At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_0_3At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_3_0P : Prog isa := .block ((once) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(once) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(once) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(once) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(fun a b => addMul a b .x17) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(fun a b => addMul a b .x17) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_3_0At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_3_0P (.block ((List.finRange 16).map (storeWord index))))
def mixed_3_0 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_3_0At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_3_0At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_1_3P : Prog isa := .block ((once) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(once) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(once) (lane 0) (lane 4) ++
(fun a b => addMul a b .x17) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(once) (lane 8) (lane 12) ++
(fun a b => addMul a b .x17) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(once) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(once) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(once) (lane 0) (lane 5) ++
(once) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(once) (lane 10) (lane 15) ++
(once) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_1_3At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_1_3P (.block ((List.finRange 16).map (storeWord index))))
def mixed_1_3 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_1_3At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_1_3At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def mixed_3_1P : Prog isa := .block ((once) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
(once) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
(once) (lane 0) (lane 4) ++
(once) (lane 1) (lane 5) ++
(fun a b => addMul a b .x17) (lane 2) (lane 6) ++
(fun a b => addMul a b .x17) (lane 3) (lane 7) ++
([.logic .eor .x (lane 12) (lane 12) (lane 0), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 1), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 2), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
([.logic .eor .x (lane 15) (lane 15) (lane 3), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
(once) (lane 8) (lane 12) ++
(once) (lane 9) (lane 13) ++
(fun a b => addMul a b .x17) (lane 10) (lane 14) ++
(fun a b => addMul a b .x17) (lane 11) (lane 15) ++
([.logic .eor .x (lane 4) (lane 4) (lane 8), .ror .x (lane 4) (lane 4) 63] : List Instr) ++
([.logic .eor .x (lane 5) (lane 5) (lane 9), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 10), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 11), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
(once) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 32] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 32] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 32] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 32] : List Instr) ++
(once) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 24] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 24] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 24] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 24] : List Instr) ++
(once) (lane 0) (lane 5) ++
(fun a b => addMul a b .x17) (lane 1) (lane 6) ++
(fun a b => addMul a b .x17) (lane 2) (lane 7) ++
(fun a b => addMul a b .x17) (lane 3) (lane 4) ++
([.logic .eor .x (lane 15) (lane 15) (lane 0), .ror .x (lane 15) (lane 15) 16] : List Instr) ++
([.logic .eor .x (lane 12) (lane 12) (lane 1), .ror .x (lane 12) (lane 12) 16] : List Instr) ++
([.logic .eor .x (lane 13) (lane 13) (lane 2), .ror .x (lane 13) (lane 13) 16] : List Instr) ++
([.logic .eor .x (lane 14) (lane 14) (lane 3), .ror .x (lane 14) (lane 14) 16] : List Instr) ++
(once) (lane 10) (lane 15) ++
(fun a b => addMul a b .x17) (lane 11) (lane 12) ++
(fun a b => addMul a b .x17) (lane 8) (lane 13) ++
(fun a b => addMul a b .x17) (lane 9) (lane 14) ++
([.logic .eor .x (lane 5) (lane 5) (lane 10), .ror .x (lane 5) (lane 5) 63] : List Instr) ++
([.logic .eor .x (lane 6) (lane 6) (lane 11), .ror .x (lane 6) (lane 6) 63] : List Instr) ++
([.logic .eor .x (lane 7) (lane 7) (lane 8), .ror .x (lane 7) (lane 7) 63] : List Instr) ++
([.logic .eor .x (lane 4) (lane 4) (lane 9), .ror .x (lane 4) (lane 4) 63] : List Instr))
def mixed_3_1At (index : Fin 16 → Fin 128) : Prog isa :=
 .seq (.block ((List.finRange 16).map (loadWord index)))
 (.seq mixed_3_1P (.block ((List.finRange 16).map (storeWord index))))
def mixed_3_1 : Prog isa := seqs [
 .block ((List.range 64).flatMap initPair), .block [.vop (.dup .d2 .v16 .x2)],
 seqs ((List.finRange 8).map (fun r => mixed_3_1At (Spec.Argon2.rowIndex r))),
 seqs ((List.finRange 8).map (fun c => mixed_3_1At (Spec.Argon2.colIndex c))),
 .block [.umov .x .x2 .v16 0], .block ((List.range 64).flatMap finishPair)]
def emit (name : String) (p : Prog isa) (apple : Bool) : String :=
 let pre := if apple then "_" else ""
 ".p2align 6\n.globl " ++ pre ++ name ++ "\n" ++ pre ++ name ++ ":\n" ++
 String.intercalate "\n" ((printer.function p).map fun l => match l with
 | .text s => s | .call n => "bl " ++ pre ++ n | .sym .. => "ERROR") ++ "\n"
def main : IO Unit := do
 IO.FS.writeFile "/tmp/vg-argon2-arm64/mixed-apple.S" (".text\n" ++ String.join ([("trial_mixed_0_0",mixed_0_0),("trial_mixed_1_1",mixed_1_1),("trial_mixed_2_2",mixed_2_2),("trial_mixed_4_4",mixed_4_4),("trial_mixed_8_8",mixed_8_8),("trial_mixed_3_3",mixed_3_3),("trial_mixed_5_5",mixed_5_5),("trial_mixed_6_6",mixed_6_6),("trial_mixed_9_9",mixed_9_9),("trial_mixed_10_10",mixed_10_10),("trial_mixed_12_12",mixed_12_12),("trial_mixed_7_7",mixed_7_7),("trial_mixed_11_11",mixed_11_11),("trial_mixed_13_13",mixed_13_13),("trial_mixed_14_14",mixed_14_14),("trial_mixed_15_15",mixed_15_15),("trial_mixed_0_1",mixed_0_1),("trial_mixed_1_0",mixed_1_0),("trial_mixed_0_3",mixed_0_3),("trial_mixed_3_0",mixed_3_0),("trial_mixed_1_3",mixed_1_3),("trial_mixed_3_1",mixed_3_1)].map fun (n,p) => emit n p true))
 IO.FS.writeFile "/tmp/vg-argon2-arm64/mixed-linux.S" (".text\n" ++ String.join ([("trial_mixed_0_0",mixed_0_0),("trial_mixed_1_1",mixed_1_1),("trial_mixed_2_2",mixed_2_2),("trial_mixed_4_4",mixed_4_4),("trial_mixed_8_8",mixed_8_8),("trial_mixed_3_3",mixed_3_3),("trial_mixed_5_5",mixed_5_5),("trial_mixed_6_6",mixed_6_6),("trial_mixed_9_9",mixed_9_9),("trial_mixed_10_10",mixed_10_10),("trial_mixed_12_12",mixed_12_12),("trial_mixed_7_7",mixed_7_7),("trial_mixed_11_11",mixed_11_11),("trial_mixed_13_13",mixed_13_13),("trial_mixed_14_14",mixed_14_14),("trial_mixed_15_15",mixed_15_15),("trial_mixed_0_1",mixed_0_1),("trial_mixed_1_0",mixed_1_0),("trial_mixed_0_3",mixed_0_3),("trial_mixed_3_0",mixed_3_0),("trial_mixed_1_3",mixed_1_3),("trial_mixed_3_1",mixed_3_1)].map fun (n,p) => emit n p false))
end Trial
def main := Trial.main
