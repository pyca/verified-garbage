module

public import VerifiedGarbage.Impl.Scrypt.RISCV64.BlockMix

/-!
# scryptROMix: RISC-V implementation

`vg_scrypt_romix(b = a0, r = a1, v = a2, vlen = a3, t = a4)` (with
doubleword accesses, `wide`; `b`, `v` and `t` multiples of 8) and
`vg_scrypt_romix_bytes` (byte accesses, any pointers) replace the
`128 * r` bytes at `b` by scryptROMix (RFC 7914 §5) of them, with
`N = vlen / r`, a power of two, as on PPC64LE
(`Impl/Scrypt/PPC64LE/RoMix.lean`): `X` stays in `b`; step 2 runs `N`
times, `V[i] = X` (a copy), then `X = scryptBlockMix (V[i])`; step 3 runs
`N` times, `j = Integerify (X) mod N` (the low 8 bytes of `X`'s last
64-byte block, masked with `N - 1`), then `T = X xor V[j]` (`T` is the
`128 * r` bytes at `t`), then `X = scryptBlockMix (T)`. The address of
`V[j]` is `v + j * 128 r` (`mul` then `add`).

The function runs in a 64-byte frame on the stack holding our return
address, which each call replaces, our caller's `s4`–`s9` and `N`. Across
the calls, which preserve them, `s4` is `b`, `s5` is `v`, `s6` is `128 r`,
`s7` counts the iterations left, `s8` is `V[i]` in step 2 and `N - 1` in
step 3, and `s9` is `t`.

Every branch and address depends only on the pointers, `r`, `N` and the
indices `j`: the contract declares that the function leaks the `j`.
-/

@[expose] public section

namespace VG.Impl.Scrypt.RISCV64

open VG.RISCV64

/-- The registers we save, and where they are in the frame (`N` is at 56). -/
def rmSaved : List (Reg × Nat) :=
  [(.ra, 0), (.s4, 8), (.s5, 16), (.s6, 24), (.s7, 32), (.s8, 40), (.s9, 48)]

/-- The units `[t1] ← [t0]`, `t2` of them. -/
def copyLoop (wide : Bool) : Prog isa :=
  .loop (.block [.load (unitW wide) .t3 .t0 0, .store (unitW wide) .t3 .t1 0,
    .addi .t0 .t0 (unitB wide), .addi .t1 .t1 (unitB wide), .addi .t2 .t2 (-1)]) (.nonzero .t2)

/-- The units `[t2] ← [t0] xor [t1]`, `t3` of them. -/
def xorLoop (wide : Bool) : Prog isa :=
  .loop (.block [.load (unitW wide) .t4 .t0 0, .load (unitW wide) .t5 .t1 0,
    .logic .xor .t4 .t4 .t5, .store (unitW wide) .t4 .t2 0, .addi .t0 .t0 (unitB wide),
    .addi .t1 .t1 (unitB wide), .addi .t2 .t2 (unitB wide), .addi .t3 .t3 (-1)]) (.nonzero .t3)

/-- `t2 ←` the number of units in `128 r` bytes. -/
def unitCount (wide : Bool) : Instr := if wide then .shift .srl .d .t2 .s6 3 else mov .t2 .s6

/-- Saving the return address and our caller's registers; `s4 = b`,
`s5 = v`, `s9 = t`, `s6 = 128 r`; `t0 = r`, `t1 = 1`, `t2 = 2 vlen` for
`nLoop`. -/
def rmPrologue : List Instr :=
  .addSp .t0 0 :: rmSaved.map (fun (r, d) => .store .d r .t0 d) ++
    ([mov .s4 .a0, mov .s5 .a2, mov .s9 .a4, .shift .sll .d .s6 .a1 7,
      mov .t0 .a1, .li .t1 1, .add .t2 .a3 .a3] : List Instr)

/-- `t1 ← 2 N`: doubling `t0` (from `r`) and `t1` (from 1) until `t0 = 2 vlen`. -/
def nLoop : Prog isa :=
  .loop (.block [.add .t0 .t0 .t0, .add .t1 .t1 .t1, .sub .t3 .t0 .t2]) (.nonzero .t3)

/-- `N` to the frame and the count; `s8 = v`. -/
def rmSetup : List Instr :=
  [.shift .srl .d .t1 .t1 1, .addSp .t0 0, .store .d .t1 .t0 56, mov .s7 .t1, mov .s8 .s5]

/-- `vg_scrypt_blockmix(src, r, dst = b)`. -/
def blockMixTo (wide : Bool) (src : List Instr) : Prog isa :=
  .seq (.block (src ++ ([.shift .srl .d .a1 .s6 7, mov .a2 .s4] : List Instr)))
    (.call (blockMixName wide) (blockMix wide))

/-- Step 2, once: `V[i] = X`, `X = scryptBlockMix (V[i])`. -/
def step2 (wide : Bool) : Prog isa :=
  .seq (.block [mov .t0 .s4, mov .t1 .s8, unitCount wide]) <|
  .seq (copyLoop wide) <|
  .seq (blockMixTo wide [mov .a0 .s8])
    (.block [.add .s8 .s8 .s6, .addi .s7 .s7 (-1)])

/-- Between the steps: the count is `N` again, and `s8 = N - 1`. -/
def rmMid : List Instr :=
  [.addSp .t0 0, .load .d .s7 .t0 56, .addi .s8 .s7 (-1)]

/-- `t0 ← j`: the low 8 bytes of `X`'s last 64-byte block (one `ld`, or
eight `lbu` through `t2`), masked with `N - 1`. -/
def jBlock (wide : Bool) : List Instr :=
  [.add .t1 .s4 .s6, .addi .t1 .t1 (-64)] ++
    (if wide then [.load .d .t0 .t1 0] else
      .load .b .t0 .t1 0 :: (List.range 7).flatMap fun i =>
        [.load .b .t2 .t1 (i + 1), .shift .sll .d .t2 .t2 (8 * (i + 1)), .logic .or .t0 .t0 .t2]) ++
    ([.logic .and .t0 .t0 .s8] : List Instr)

/-- Step 3, once: `j`; `t1 = V[j]`; `T = X xor V[j]`; `X = scryptBlockMix (T)`. -/
def step3 (wide : Bool) : Prog isa :=
  .seq (.block (jBlock wide)) <|
  .seq (.block [.mul .t1 .t0 .s6, .add .t1 .t1 .s5, mov .t0 .s4, mov .t2 .s9,
    if wide then .shift .srl .d .t3 .s6 3 else mov .t3 .s6]) <|
  .seq (xorLoop wide) <|
  .seq (blockMixTo wide [mov .a0 .s9])
    (.block [.addi .s7 .s7 (-1)])

/-- Restoring the return address and our caller's registers. -/
def rmEpilogue : List Instr := .addSp .t0 0 :: rmSaved.map fun (r, d) => .load .d r .t0 d

def roMixMain (wide : Bool) : Prog isa :=
  .seq (.block rmPrologue) <|
  .seq nLoop <|
  .seq (.block rmSetup) <|
  .seq (.loop (step2 wide) (.nonzero .s7)) <|
  .seq (.block rmMid) <|
  .seq (.loop (step3 wide) (.nonzero .s7))
    (.block rmEpilogue)

def roMix (wide : Bool) : Prog isa := .frame (.alloc 64) (roMixMain wide) (.free 64)

def roMixName (wide : Bool) : String :=
  if wide then "vg_scrypt_romix" else "vg_scrypt_romix_bytes"

end VG.Impl.Scrypt.RISCV64
