module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Entry
public import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Setup
public import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Wipe
public import VerifiedGarbage.Impl.Sha3.AArch64.Stream

/-!
# Ed448's complete operations on AArch64: shared code

The complete operations run in the frame of AArch64 Ed25519's
(`Impl.Ed25519.AArch64.Whole.wrap`: `x30` pushed, 320 bytes allocated, the
arguments in `x0`–`x5` saved in their last 48 bytes), with the locals in its
first 256 bytes. Arguments beyond `x5` are kept in the locals (`keep`), and a
call's argument may be one (`Src.loc`), or the previous call's result
(`Src.ret`), besides what `Whole.setup` sets (`Src.val`).

The hashes are SHAKE256 with the sponge functions, the Keccak state at the
start of `scratch` (zeroed by `zeroStores`, through `x15`) and their working
space at `scratch + 256`; the first ten bytes of `dom4(0, C)` are built in the
frame (`hdr`). `pruneAt` prunes a hash in the frame into a scalar
(`Spec.Ed448.prune`).
-/

@[expose] public section

namespace VG.Impl.Ed448.AArch64.Whole

open VG.AArch64
open VG.Impl.Ed25519.AArch64.Whole (Value setArg zeroWord)

/-- A call's argument. -/
inductive Src where
  /-- As `Whole.setup` sets it. -/
  | val (v : Value)
  /-- The word at `sp + d` (the locals), plus `o`. -/
  | loc (d o : Nat)
  /-- `x0`, the previous call's result. -/
  | ret

def setSrc (r : Reg) : Src → List Instr
  | .val v => setArg r v
  | .loc d o => [.ldrSp r d, .addImm .x r r o]
  | .ret => [.addImm .x r .x0 0]

/-- Set each argument, in order (a `ret` before anything writes `x0`). -/
def setupS (args : List (Reg × Src)) : List Instr := args.flatMap fun (r, v) => setSrc r v

/-- A call of `code`, named `name`, with the arguments `args`. -/
def callS (args : List (Reg × Src)) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (setupS args)) (.call name code)

/-- Keep `r` in the locals at `sp + d`. -/
def keep (r : Reg) (d : Nat) : List Instr := [.addSp .x15 d, .str .x r .x15 0]

/-- `"SigEd448"`, then `ctxlen · 2^8` (the bytes `0 ‖ ctxlen`, for `ctxlen < 256`):
the first ten bytes of `dom4(0, context)`, at `sp + d`. -/
def hdr (d : Nat) (ctxlen : Value) : List Instr :=
  [.movz .x .x9 0x6953 0, .movk .x .x9 0x4567 1, .movk .x .x9 0x3464 2, .movk .x .x9 0x3834 3,
    .addSp .x15 d, .str .x .x9 .x15 0] ++ setArg .x9 ctxlen ++ [.lsl .x .x9 .x9 8, .str .x .x9 .x15 8]

/-- `x14 = 0`, and the 25 words of the Keccak state at `x15` zeroed (in a
block of their own: their address is a pointer read from the frame). -/
def zeroStores : List Instr := .movz .x .x14 0 0 :: (List.range 25).map fun k => .str .x .x14 .x15 (8 * k)

/-! The SHA-3 sponge's calls, with the permutation `c`, the Keccak state at
`scratch` and the working space at `scratch + 256`, `scratch` the word `scr`
of the locals. -/
section
variable (c : Impl.Sha3.AArch64.Callee) (scr : Nat)

/-- The Keccak state zeroed. -/
def zeroSt : Prog isa := .seq (.block (setupS [(.x15, .loc scr 0)])) (.block zeroStores)

/-- Absorb `len` bytes at `src`, at the position `pos` of the block. -/
def kabs (src len pos : Src) : Prog isa :=
  callS [(.x2, pos), (.x0, .loc scr 0), (.x1, .val (.const 136)), (.x3, src), (.x4, len),
    (.x5, .loc scr 256)] ("vg_keccak_absorb_scratch" ++ c.suffix) (Impl.Sha3.AArch64.Stream.absorbWith c)

/-- Pad at the position `pos`, with the suffix of SHAKE. -/
def kpad (pos : Src) : Prog isa :=
  callS [(.x2, pos), (.x0, .loc scr 0), (.x1, .val (.const 136)), (.x3, .val (.const 0x1f)),
    (.x4, .loc scr 256)] ("vg_keccak_pad_scratch" ++ c.suffix) (Impl.Sha3.AArch64.Stream.padWith c)

/-- Squeeze 114 bytes from position 0 to `out`. -/
def ksqz (out : Src) : Prog isa :=
  callS [(.x0, .loc scr 0), (.x1, .val (.const 136)), (.x2, .val (.const 0)), (.x3, out),
    (.x4, .val (.const 114)), (.x5, .loc scr 256)] ("vg_keccak_squeeze_scratch" ++ c.suffix)
    (Impl.Sha3.AArch64.Stream.squeezeWith c)

end

/-! ## Pruning -/

/-- Bits 0–1 of `x9` cleared. -/
def pruneLow : List Instr :=
  [.movz .x .x10 0xfffc 0, .movk .x .x10 0xffff 1, .movk .x .x10 0xffff 2,
    .movk .x .x10 0xffff 3, .logic .and .x .x9 .x9 .x10]

/-- Bit 63 of `x9` set. -/
def pruneHigh : List Instr := [.movz .x .x10 0x8000 3, .logic .orr .x .x9 .x9 .x10]

/-- Word `k` of the hash at `sp + h`, pruned, to word `k` of the scalar at `sp + d`. -/
def pruneWord (h d k : Nat) : List Instr :=
  [.ldrSp .x9 (h + 8 * k)] ++
    (if k = 0 then pruneLow else if k = 6 then pruneHigh else []) ++
    [.addSp .x15 (d + 8 * k), .str .x .x9 .x15 0]

/-- Pruning (`Spec.Ed448.prune`): the first seven words of the hash at
`sp + h`, bits 0–1 cleared and bit 447 (the top of word 6) set, and an
eighth word 0, whose low byte is the 57th, as the scalar at `sp + d`. -/
def pruneAt (h d : Nat) : List Instr :=
  (List.range 7).flatMap (pruneWord h d) ++ zeroWord (d / 8 + 7)

end VG.Impl.Ed448.AArch64.Whole
