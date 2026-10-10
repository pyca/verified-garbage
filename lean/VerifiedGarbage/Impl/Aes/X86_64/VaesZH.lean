import VerifiedGarbage.Impl.Aes.X86_64.VaesZ

/-!
# AVX-512 AES with round keys kept in the high vector registers

The caller loads the schedule once before processing batches. The low
registers remain available for counters, data, and interleaved GHASH.
-/

namespace VG.Impl.Aes.X86_64.VaesZH

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_)

/-- Registers for the initial key and the thirteen possible inner rounds. -/
def keyReg : Nat → HReg
  | 0 => .xmm16 | 1 => .xmm17 | 2 => .xmm18 | 3 => .xmm19
  | 4 => .xmm20 | 5 => .xmm21 | 6 => .xmm22 | 7 => .xmm23
  | 8 => .xmm24 | 9 => .xmm25 | 10 => .xmm26 | 11 => .xmm27
  | 12 => .xmm28 | _ => .xmm29

def loadKey (j : Nat) : Instr := .vbroadcasti32x4H (keyReg j) (at_ .rdi (16 * j))

/-- `rsi` is the round count and `r10` points to the final key. -/
def loadKeys : Prog isa :=
  .seq (.block ((List.range 10).map loadKey ++ ([.alu .cmp .rsi (.imm 10)] : List Instr)))
    (.seq
      (.ite .e (.block [])
        (.seq (.block [loadKey 10, loadKey 11, .alu .cmp .rsi (.imm 12)])
          (.ite .e (.block []) (.block [loadKey 12, loadKey 13]))))
      (.block [.vbroadcasti32x4H .xmm31 (at_ .r10 0)]))

def keyOp (k : HReg) (regs : List XReg) (op : ZKeyOp) : List Instr :=
  regs.map fun b => .zop (.zbinH op b b k)

def round (regs : List XReg) (j : Nat) : List Instr := keyOp (keyReg j) regs .vaesenc

/-- The same rounds and interleaving points as `VaesZ.aesZ`, without
loading the round key again for each batch. -/
def aes (regs : List XReg) (g : Nat → List Instr := fun _ => []) : Prog isa :=
  .seq (.block (keyOp (keyReg 0) regs .vpxord ++
      (List.range 9).flatMap (fun j => round regs (j + 1) ++ g (j + 1)) ++ ([.alu .cmp .rsi (.imm 10)] : List Instr)))
    (.seq
      (.ite .e (.block [])
        (.seq (.block (round regs 10 ++ round regs 11 ++ ([.alu .cmp .rsi (.imm 12)] : List Instr)))
          (.ite .e (.block []) (.block (round regs 12 ++ round regs 13)))))
      (.block (keyOp .xmm31 regs .vaesenclast)))

end VG.Impl.Aes.X86_64.VaesZH
