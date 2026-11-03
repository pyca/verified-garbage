module

public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# ChaCha20 block function: RISC-V implementation

`vg_chacha20_block(state = a0, buf = a1)`.

The structure of the PPC64LE implementation, for RV64I, which has no
rotates and faults on misaligned accesses:
* Word `k` of the state lives in the low word of `wreg k` (`t0`–`t6`,
  `a2`–`a7`, `s0`–`s2`) throughout; a counted loop runs the ten
  double rounds, using `U` (`s4`) as its public counter. The additions act
  on all 64 bits, so the high words hold carries, which the word shifts and
  the byte stores ignore.
* A rotation left by `k` is `slliw` by `k` into a temporary, `srliw` by
  `32 - k` and `or` (`rotl_shifts`). A round's four quarter rounds touch
  disjoint words, so each of their four steps runs for all four at once
  (`qstep4`), so that the four chains of dependent operations are side by
  side; the rotations share `T` (`s3`), which the core renames.
* `state` and `buf` are argument buffers, whose alignment the contract does
  not state: the words are loaded and stored a byte at a time
  (`Impl/Words/RISCV64.lean`). The input state is re-read from `state` to
  add it at the end, into `T`, with `U` (`s4`) as a temporary.
* `s0`–`s4` are callee-saved: they are saved first and restored last, as
  doublewords, at `buf + 64` rounded up to a multiple of 8 (`t0` holds that
  address), within `buf[64..112)`, which is working space. Only the first
  64 bytes of `buf` are written otherwise.
* Every address is `a0`, `a1` or `t0` (computed from `a1`) plus a constant,
  and the only branch counts ten double rounds, so only the pointers can
  affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64

/-- The register holding word `k`. -/
def wreg (k : Nat) : Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a2, .a3, .a4, .a5, .a6, .a7, .s0, .s1, .s2].getD k .t0

/-- The rotation temporary, and the second temporary of the final addition. -/
def T : Reg := .s3
def U : Reg := .s4

/-- The callee-saved registers used, in the order they are saved. -/
def saved (i : Nat) : Reg := [.s0, .s1, .s2, .s3, .s4].getD i .s0

/-- `t0 :=` `buf + 64` rounded up to a multiple of 8 (`(buf + 71) & -8`). -/
def savePtr : List Instr := [.addi .t0 .a1 71, .logicImm .and .t0 .t0 (-8)]

/-- Save them at `t0`. -/
def save : List Instr :=
  savePtr ++ (List.range 5).flatMap fun i => [.store .d (saved i) .t0 (8 * i)]

/-- Restore them. -/
def restore : List Instr :=
  savePtr ++ (List.range 5).flatMap fun i => [.load .d (saved i) .t0 (8 * i)]

/-- Step `k` of four quarter rounds at once: `a += b; d ^= a; d <<<= k` for
each `(a, b, d)` of `ls`, the additions and XORs operation by operation, then
the rotations, each through `T`. -/
def qstep4 (ls : List (Reg × Reg × Reg)) (k : Nat) : List Instr :=
  ls.map (fun (a, b, _) => .add a a b) ++ ls.map (fun (a, _, d) => .logic .xor d d a) ++
  ls.flatMap fun (_, _, d) => [.shift .sll .w T d k, .shift .srl .w d d (32 - k), .logic .or d d T]

/-- The four quarter rounds `QUARTERROUND(x, y, z, w)` (RFC 8439 §2.2) of `qs`, at once. -/
def round4 (qs : List (Nat × Nat × Nat × Nat)) : List Instr :=
  qstep4 (qs.map fun (x, y, _, w) => (wreg x, wreg y, wreg w)) 16 ++
  qstep4 (qs.map fun (_, y, z, w) => (wreg z, wreg w, wreg y)) 12 ++
  qstep4 (qs.map fun (x, y, _, w) => (wreg x, wreg y, wreg w)) 8 ++
  qstep4 (qs.map fun (_, y, z, w) => (wreg z, wreg w, wreg y)) 7

/-- The column round's quarter rounds, and the diagonal round's. -/
def columns : List (Nat × Nat × Nat × Nat) := [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15)]
def diagonals : List (Nat × Nat × Nat × Nat) := [(0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]

/-- `inner_block` (RFC 8439 §2.3.1): a column round and a diagonal round. -/
def doubleRound : Prog isa := .block (round4 columns ++ round4 diagonals)

/-- Ten double rounds, with one copy of the round body and a public counter. -/
def rounds : Prog isa :=
  .seq (.block [.li U 10])
    (.loop (.seq doubleRound (.block [.addi U U (-1)])) (.nonzero U))

/-- Load the state into the registers (`lwu`: `state` is 4-byte aligned). -/
def load : List Instr := (List.range 16).flatMap fun k => [.load .w (wreg k) .a0 (4 * k)]

/-- Add input word `k` (via `T`) and store output word `k` (`buf` is 4-byte
aligned). -/
def addWord (k : Nat) : List Instr :=
  [.load .w T .a0 (4 * k)] ++ [.add (wreg k) (wreg k) T] ++ [.store .w (wreg k) .a1 (4 * k)]

def finish : List Instr := (List.range 16).flatMap addWord

/-- Load, run the rounds and add. -/
def main : Prog isa := .seq (.block load) (.seq rounds (.block finish))

def block : Prog isa := .seq (.block save) (.seq main (.block restore))

end VG.Impl.ChaCha20.RISCV64
