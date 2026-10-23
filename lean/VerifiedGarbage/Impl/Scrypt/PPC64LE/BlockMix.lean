module

public import VerifiedGarbage.Impl.Scrypt.PPC64LE.Salsa

/-!
# scryptBlockMix: PPC64LE implementation

`blockmix(b = r3, r = r4, y = r5, ry = r6, scratch = r7)` writes
scryptBlockMix (RFC 7914 §4) of the `128 * r` bytes at `b` to the `128 * r`
bytes at `y`.

As on AArch64 (`Impl/Scrypt/AArch64/BlockMix.lean`), step 2's `Y[i]` go
straight to their places in step 3's output: `Y[2k]` to `y + 64k` and
`Y[2k + 1]` to `y + 64 (r + k)`. Each is computed in place: `T = X xor B[i]`
is written there, and `vg_salsa20_8` replaces it by `Salsa (T)`. `X` is then
the block just written (initially `B[2r - 1]`). The loop runs once for each
pair `(2k, 2k + 1)`.

`scratch` (128 bytes) holds Salsa20/8's working space (`[0, 64)`) and our
caller's `r24`–`r29` (`[64, 112)`); our return address, which each call
replaces, is moved to `r0` and saved in a stack frame around the whole
function. Across the calls, which preserve them, `r24` is `B[2k]`, `r25` is
`y + 64k`, `r26` is `y + 64 (r + k)`, `r27` is `scratch`, `r28` counts the
pairs left and `r29` is `X`. Every address is one of these plus a constant,
and the only branch is on the count, so only the pointers and `r` affect
timing.
-/

@[expose] public section

namespace VG.Impl.Scrypt.PPC64LE

open VG.PPC64LE

/-- `mr d, n` (as `addi d, n, 0`; `n ≠ r0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The nonvolatile registers we use, and where they are saved in `scratch`.
`r27` is last: the epilogue reads the others through it. -/
def bmSaved : List (Reg × Nat) :=
  [(.r24, 64), (.r25, 72), (.r26, 80), (.r28, 88), (.r29, 96), (.r27, 104)]

/-- Doubleword `k` of `[dst] ← [x] xor [src]`. -/
def xorW (dst x src : Reg) (k : Nat) : List Instr :=
  [.load .d .r9 x (8 * k), .load .d .r10 src (8 * k), .logic .xor .r9 .r9 .r10,
    .store .d .r9 dst (8 * k)]

/-- The 64 bytes `[dst] ← [x] xor [src]`. -/
def xor64 (dst x src : Reg) : List Instr := (List.range 8).flatMap (xorW dst x src)

/-- `vg_salsa20_8(dst, scratch)`. -/
def salsaAt (salsa : Prog isa) (dst : Reg) : Prog isa :=
  .seq (.block [mov .r3 dst, mov .r4 .r27]) (.call "vg_salsa20_8" salsa)

/-- Saving our caller's registers and setting up ours: `r26 = y + 64 r`,
`r29 = b + 128 r - 64` (`B[2r - 1]`). -/
def bmPrologue : List Instr :=
  bmSaved.map (fun (r, d) => .store .d r .r7 d) ++
    [mov .r28 .r4, mov .r24 .r3, mov .r25 .r5, mov .r27 .r7,
     .lsl .r9 .r4 6, .add .r26 .r5 .r9,
     .lsl .r9 .r4 7, .add .r29 .r3 .r9, .subi .r29 .r29 64]

/-- One pair: `Y[2k]` from `X` and `B[2k]`, then `Y[2k + 1]` from it and
`B[2k + 1]`; then the pointers move on and the count goes down. -/
def bmBody (salsa : Prog isa) : Prog isa :=
  .seq (.block (xor64 .r25 .r29 .r24)) <|
  .seq (salsaAt salsa .r25) <|
  .seq (.block (.addi .r24 .r24 64 :: xor64 .r26 .r25 .r24)) <|
  .seq (salsaAt salsa .r26)
    (.block [mov .r29 .r26, .addi .r24 .r24 64, .addi .r25 .r25 64,
      .addi .r26 .r26 64, .subi .r28 .r28 1])

/-- Restoring our caller's registers. -/
def bmEpilogue : List Instr := bmSaved.map fun (r, d) => .load .d r .r27 d

def blockMixMain (salsa : Prog isa) : Prog isa :=
  .seq (.block bmPrologue) (.seq (.loop (bmBody salsa) (.nonzero .d .r28)) (.block bmEpilogue))

def blockMixWith (salsa : Prog isa) : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (blockMixMain salsa) (.pop .r0)) (.block [.mtlr .r0]))

def blockMix : Prog isa := blockMixWith salsa

end VG.Impl.Scrypt.PPC64LE
