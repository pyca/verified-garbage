module

public import VerifiedGarbage.Impl.Scrypt.PPC64LE.BlockMix

/-!
# scryptROMix: PPC64LE implementation

`romix(b = r3, r = r4, v = r5, vlen = r6, scratch = r7, slen = r8)`
replaces the `128 * r` bytes at `b` by scryptROMix (RFC 7914 §5) of them,
with `N = vlen / r`, a power of two. `X` stays in `b`.

As on AArch64 (`Impl/Scrypt/AArch64/RoMix.lean`), step 2 runs `N` times:
`V[i] = X` (a copy), then `X = scryptBlockMix (V[i])`. Step 3 runs `N`
times: `j = Integerify (X) mod N` (the low 8 bytes of `X`'s last 64-byte
block, masked with `N - 1`), then `T = X xor V[j]`, then
`X = scryptBlockMix (T)`. The address of `V[j]` is `v + j * 128 r` (`mulld`
then `add`).

`scratch` (`128 (r + 2)` bytes) holds scryptBlockMix's working space
(`[0, 128)`), our caller's `r24`–`r29` and our return address, moved to `r0`
(`[128, 184)`: there is no stack frame), `N` (`[184, 192)`) and `T`
(`[192, 192 + 128 r)`). Across the calls, which preserve them, `r24` is `b`,
`r25` is `v`, `r27` is `scratch`, `r26` is `128 r` and `r28` counts the
iterations left; `r29` is `V[i]` in step 2 and `N - 1` in step 3.

Every branch and address depends only on the pointers, `r`, `N` and the
indices `j`: the contract declares that the function leaks the `j`.
-/

@[expose] public section

namespace VG.Impl.Scrypt.PPC64LE

open VG.PPC64LE

/-- The registers we save, and where they are saved in `scratch` (our return
address goes to `[168, 176)`). `r27` is last: the epilogue reads the others
through it. -/
def rmSaved : List (Reg × Nat) :=
  [(.r24, 128), (.r25, 136), (.r26, 144), (.r28, 152), (.r29, 160), (.r27, 176)]

/-- The doublewords `[r10] ← [r9]`, `r11` of them. -/
def copyLoop : Prog isa :=
  .loop (.block [.load .d .r12 .r9 0, .store .d .r12 .r10 0, .addi .r9 .r9 8,
    .addi .r10 .r10 8, .subi .r11 .r11 1]) (.nonzero .d .r11)

/-- The doublewords `[r11] ← [r9] xor [r10]`, `r12` of them. -/
def xorLoop : Prog isa :=
  .loop (.block [.load .d .r6 .r9 0, .load .d .r8 .r10 0, .logic .xor .r6 .r6 .r8,
    .store .d .r6 .r11 0, .addi .r9 .r9 8, .addi .r10 .r10 8, .addi .r11 .r11 8,
    .subi .r12 .r12 1]) (.nonzero .d .r12)

/-- Saving our caller's registers and our return address (through `r0`);
`r24 = b`,
`r25 = v`, `r27 = scratch`, `r26 = 128 r`; `r9 = r`, `r10 = 1`,
`r11 = 2 vlen` for `nLoop`. -/
def rmPrologue : List Instr :=
  rmSaved.map (fun (r, d) => .store .d r .r7 d) ++
    [.mflr .r0, .store .d .r0 .r7 168, mov .r24 .r3, mov .r25 .r5, mov .r27 .r7, .lsl .r26 .r4 7,
     mov .r9 .r4, .li .r10 1, .add .r11 .r6 .r6]

/-- `r10 ← 2 N`: doubling `r9` (from `r`) and `r10` (from 1) until `r9 = 2 vlen`. -/
def nLoop : Prog isa :=
  .loop (.block [.add .r9 .r9 .r9, .add .r10 .r10 .r10, .sub .r12 .r9 .r11])
    (.nonzero .d .r12)

/-- `N` to `scratch` and the count; `r29 = v`. -/
def rmSetup : List Instr :=
  [.lsr .d .r10 .r10 1, .store .d .r10 .r27 184, mov .r28 .r10, mov .r29 .r25]

/-- `vg_scrypt_blockmix(src, r, dst = b, r, scratch)`. -/
def blockMixTo (blockMix : Prog isa) (src : List Instr) : Prog isa :=
  .seq (.block (src ++ ([.lsr .d .r4 .r26 7, mov .r5 .r24, mov .r6 .r4, mov .r7 .r27] : List Instr)))
    (.call "vg_scrypt_blockmix" blockMix)

/-- Step 2, once: `V[i] = X`, `X = scryptBlockMix (V[i])`. -/
def step2 (blockMix : Prog isa) : Prog isa :=
  .seq (.block [mov .r9 .r24, mov .r10 .r29, .lsr .d .r11 .r26 3]) <|
  .seq copyLoop <|
  .seq (blockMixTo blockMix [mov .r3 .r29])
    (.block [.add .r29 .r29 .r26, .subi .r28 .r28 1])

/-- Between the steps: the count is `N` again, and `r29 = N - 1`. -/
def rmMid : List Instr :=
  [.load .d .r28 .r27 184, .subi .r29 .r28 1]

/-- `r9 ← j`: the low 8 bytes of `X`'s last 64-byte block, masked with `N - 1`. -/
def jBlock : List Instr :=
  [.add .r9 .r24 .r26, .subi .r9 .r9 64, .load .d .r9 .r9 0, .logic .and .r9 .r9 .r29]

/-- Step 3, once: `j`; `r10 = V[j]`; `T = X xor V[j]`; `X = scryptBlockMix (T)`. -/
def step3 (blockMix : Prog isa) : Prog isa :=
  .seq (.block jBlock) <|
  .seq (.block [.mul .r10 .r9 .r26, .add .r10 .r10 .r25, mov .r9 .r24, .addi .r11 .r27 192,
    .lsr .d .r12 .r26 3]) <|
  .seq xorLoop <|
  .seq (blockMixTo blockMix [.addi .r3 .r27 192])
    (.block [.subi .r28 .r28 1])

/-- Restoring our caller's registers and our return address. -/
def rmEpilogue : List Instr :=
  [.load .d .r0 .r27 168, .mtlr .r0] ++ rmSaved.map fun (r, d) => .load .d r .r27 d

def roMixWith (blockMix : Prog isa) : Prog isa :=
  .seq (.block rmPrologue) <|
  .seq nLoop <|
  .seq (.block rmSetup) <|
  .seq (.loop (step2 blockMix) (.nonzero .d .r28)) <|
  .seq (.block rmMid) <|
  .seq (.loop (step3 blockMix) (.nonzero .d .r28))
    (.block rmEpilogue)

def roMix : Prog isa := roMixWith blockMix

end VG.Impl.Scrypt.PPC64LE
