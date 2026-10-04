import VerifiedGarbage.Impl.Aes.X86_64.AesNi

/-!
# AES with AVX-512 VAES on x86-64: the building blocks

A 512-bit register holds four AES states, one in each 128-bit lane, and the
EVEX.512 `vaesenc` and `vaesenclast` apply a round to each lane with the
round key in the same lane of their second source, which `vbroadcasti32x4`
loads into all four lanes, as `Vaes` does with two. The counter is kept as
four GCM blocks (byte-reversed) in the lanes of a register; `vpshufb` with
the byte-reversal mask in each lane turns them into the AES inputs of four
blocks, and `vpaddd` with 4 in doubleword 0 of each lane advances them by
four.
-/

namespace VG.Impl.Aes.X86_64.VaesZ

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_)

/-- A round key into the four lanes of `k`, then `op b, b, k` for each block
register `b`. -/
def keyOpZ (k : XReg) (regs : List XReg) (op : ZBinOp) (a : MemOp) : List Instr :=
  .vbroadcasti32x4 k a :: regs.map fun b => .zop (.zbin op b b k)

/-- Round `j` (`1 ≤ j < Nr`) of each block, the round key in `k`. -/
def roundZ (k : XReg) (regs : List XReg) (j : Nat) : List Instr := keyOpZ k regs .vaesenc (at_ .rdi (16 * j))

/-- AES of the four lanes of each block register, with `rounds` (10, 12 or
14) in `rsi`, the key schedule at `rdi`, and its last round key at `r10`, the
round keys in `k`, and the instructions `g j` after round `j`. -/
def aesZ (k : XReg) (regs : List XReg) (g : Nat → List Instr := fun _ => []) : Prog isa :=
  .seq (.block (keyOpZ k regs .vpxord (at_ .rdi 0) ++
      (List.range 9).flatMap (fun j => roundZ k regs (j + 1) ++ g (j + 1)) ++ [.alu .cmp .rsi (.imm 10)]))
    (.seq
      (.ite .e (.block [])
        (.seq (.block (roundZ k regs 10 ++ roundZ k regs 11 ++ [.alu .cmp .rsi (.imm 12)]))
          (.ite .e (.block []) (.block (roundZ k regs 12 ++ roundZ k regs 13)))))
      (.block (keyOpZ k regs .vaesenclast (at_ .r10 0))))

/-- The counter blocks: each block register gets the four counters (`c`),
byte-reversed with the mask in `m`, and the counters advance by four (`i`). -/
def ctrsZ (c m i : XReg) : List XReg → List Instr
  | [] => []
  | b :: bs => [.zop (.zbin .vpshufb b c m), .zop (.zbin .vpaddd c c i)] ++ ctrsZ c m i bs

/-- XOR block register `i` into the four data blocks at `base + 64 (j + i)`,
through `t`. -/
def xorDataZ (t : XReg) (base : Reg) : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => [.vmovdqu32Load t (at_ base (64 * j)), .zop (.zbin .vpxord b b t),
      .vmovdqu32Store (at_ base (64 * j)) b] ++ xorDataZ t base bs (j + 1)

end VG.Impl.Aes.X86_64.VaesZ
