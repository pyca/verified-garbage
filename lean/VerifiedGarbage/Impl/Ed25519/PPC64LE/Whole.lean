module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Verify
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.ScalarBase
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Scalar
public import VerifiedGarbage.Impl.Sha512.PPC64LE.Stream
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Spec.Sha512.Contract

/-!
# Ed25519 on PPC64LE: the whole functions

`publicKey`, `signCached` and `verifyMessage` hash with SHA-512's verified
streaming functions and compute with the verified Ed25519 functions, by
calls. Each is written for one more argument than its signature has, a frame
buffer `F` that `withStackScratch` allocates on the stack (wiped after use
when it holds secrets). The caller's `scratch` holds SHA-512's state (at 0)
and its working space (at 192) during a hash, and is the working space of the
Ed25519 functions called; everything that lives across calls is in `F`: the
digests and scalars, our caller's nonvolatile registers that we use, and the
link register. The pointers stay in `r20`–`r25`, which no function called
writes, so that the taint analysis sees them public after each call.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE.Whole

open VG.PPC64LE

def mov (d n : Reg) : Instr := .addi d n 0

def shaInit : Prog isa :=
  .call Spec.Sha512.init512Api.name (Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512)
def shaUpdate : Prog isa := .call "vg_sha512_update_scratch" Impl.Sha512.PPC64LE.Stream.update
def shaFinalize : Prog isa := .call "vg_sha512_finalize_scratch" Impl.Sha512.PPC64LE.Stream.finalize

/-- The slots at `o(F)` of the registers of `rs` and, after them, of the link register (from `r0`). -/
def slots (o : Nat) (rs : List Reg) : List (Reg × Nat) :=
  (rs ++ [Reg.r0]).zipIdx.map fun (r, i) => (r, o + 8 * i)

/-- Saving the registers of `rs` and the link register in their slots, `F` in `f`. -/
def saveRegs (f : Reg) (o : Nat) (rs : List Reg) : List Instr :=
  .mflr .r0 :: (slots o rs).map fun (r, d) => .store .d r f d

/-- Restoring them, the link register first; `f`, the base, must be the last of `rs`. -/
def restoreRegs (f : Reg) (o : Nat) (rs : List Reg) : List Instr :=
  (((Reg.r0, o + 8 * rs.length) :: (slots o rs).dropLast).map fun (r, d) => .load .d r f d) ++ [.mtlr .r0]

/-- `init` of the state at `scratch` (`sc`). -/
def hashInit (sc : Reg) : Prog isa := .seq (.block [mov .r3 sc]) shaInit

/-- `update` with the `len` bytes at `src`, the count before in `r4`: `count` and `len` are
set by `cnt` and `ln`. -/
def hashUpdate (sc : Reg) (cnt : List Instr) (src : Reg) (srcOff : Nat) (ln : List Instr) : Prog isa :=
  .seq (.block ([mov .r3 sc] ++ cnt ++ [.addi .r5 src srcOff] ++ ln ++ [.addi .r7 sc 192])) shaUpdate

/-- `finalize` into `o(F)`. -/
def hashFinalize (sc : Reg) (cnt : List Instr) (f : Reg) (o : Nat) : Prog isa :=
  .seq (.block ([mov .r3 sc] ++ cnt ++ [.addi .r5 f o, .addi .r6 sc 192])) shaFinalize

/-- The pruning of the digest's first half at `d(F)` into `o(F)`: bits 0–2 and 255 cleared, 254 set. -/
def prune (f : Reg) (d o : Nat) : List Instr :=
  [.load .d .r8 f d, .lsr .d .r8 .r8 3, .lsl .r8 .r8 3, .store .d .r8 f o,
    .load .d .r8 f (d + 8), .store .d .r8 f (o + 8),
    .load .d .r8 f (d + 16), .store .d .r8 f (o + 16),
    .load .d .r8 f (d + 24), .lsl .r8 .r8 2, .lsr .d .r8 .r8 2, .lis .r9 0x4000, .lsl .r9 .r9 32,
    .logic .or .r8 .r8 .r9, .store .d .r8 f (o + 24)]

/-- Copying the 32 bytes at `d(F)` to `o(F)`. -/
def copy32 (f : Reg) (d o : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [.load .d .r8 f (d + 8 * k), .store .d .r8 f (o + 8 * k)]

/-- Copying the 32 bytes at `src` to `o(F)`. -/
def copyIn (src f : Reg) (o : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [.load .d .r8 src (8 * k), .store .d .r8 f (o + 8 * k)]

/-! ## `vg_ed25519_public_key(out = r3, seed = r4, scratch = r5)`, `F` in `r6`

`F`: the digest at 0, the scalar at 64, the saves at 96. -/

def pkRegs : List Reg := [.r20, .r21, .r22, .r23]

def publicKey : Prog isa :=
  .seq (.block (saveRegs .r6 96 pkRegs ++ [mov .r20 .r3, mov .r21 .r4, mov .r22 .r5, mov .r23 .r6])) <|
  .seq (hashInit .r22) <|
  .seq (hashUpdate .r22 [.li .r4 0] .r21 0 [.li .r6 32]) <|
  .seq (hashFinalize .r22 [.li .r4 32] .r23 0) <|
  .seq (.block (prune .r23 0 64 ++ [mov .r3 .r20, .addi .r4 .r23 64, mov .r5 .r22])) <|
  .seq (.call "vg_ed25519_scalar_base" scalarBase) <|
  .block (restoreRegs .r23 96 pkRegs)

/-! ## `vg_ed25519_sign_cached(out = r3, seed = r4, pk = r5, message = r6, len = r7, scratch = r8)`,
`F` in `r9`

`F`: the scalar at 0, the nonce's prefix at 32, the nonce at 64, the challenge at 96, the digest at
128, a copy of `pk` at 192, the saves at 224. Six registers hold what lives across calls: `pk` is
copied first, and `seed` is needed only for the first hash. -/

def signRegs : List Reg := [.r20, .r21, .r22, .r23, .r24, .r25]

/-- The setup: the registers saved, the pointers moved, `pk` copied. -/
def signSetup : List Instr :=
  saveRegs .r9 224 signRegs ++
    ([mov .r20 .r3, mov .r21 .r4, mov .r22 .r6, mov .r23 .r7, mov .r24 .r8, mov .r25 .r9] ++ copyIn .r5 .r25 192)

/-- The secret scalar and the nonce's prefix. -/
def signExpand : Prog isa :=
  .seq (hashInit .r24) <|
  .seq (hashUpdate .r24 [.li .r4 0] .r21 0 [.li .r6 32]) <|
  .seq (hashFinalize .r24 [.li .r4 32] .r25 128) <|
  .block (prune .r25 128 0 ++ copy32 .r25 160 32)

/-- The nonce, and `R`. -/
def signNonce : Prog isa :=
  .seq (hashInit .r24) <|
  .seq (hashUpdate .r24 [.li .r4 0] .r25 32 [.li .r6 32]) <|
  .seq (hashUpdate .r24 [.li .r4 32] .r22 0 [mov .r6 .r23]) <|
  .seq (hashFinalize .r24 [.addi .r4 .r23 32] .r25 128) <|
  .seq (.block [.addi .r3 .r25 64, .addi .r4 .r25 128, mov .r5 .r24]) <|
  .seq (.call "vg_ed25519_scalar_reduce" scalarReduce) <|
  .seq (.block [mov .r3 .r20, .addi .r4 .r25 64, mov .r5 .r24]) <|
  .call "vg_ed25519_scalar_base" scalarBase

/-- The challenge, and `S`. -/
def signChallenge : Prog isa :=
  .seq (hashInit .r24) <|
  .seq (hashUpdate .r24 [.li .r4 0] .r20 0 [.li .r6 32]) <|
  .seq (hashUpdate .r24 [.li .r4 32] .r25 192 [.li .r6 32]) <|
  .seq (hashUpdate .r24 [.li .r4 64] .r22 0 [mov .r6 .r23]) <|
  .seq (hashFinalize .r24 [.addi .r4 .r23 64] .r25 128) <|
  .seq (.block [.addi .r3 .r25 96, .addi .r4 .r25 128, mov .r5 .r24]) <|
  .seq (.call "vg_ed25519_scalar_reduce" scalarReduce) <|
  .seq (.block [.addi .r3 .r20 32, .addi .r4 .r25 64, .addi .r5 .r25 96, .addi .r6 .r25 0, mov .r7 .r24]) <|
  .call "vg_ed25519_scalar_mul_add" scalarMulAdd

def signCached : Prog isa :=
  .seq (.block signSetup) <| .seq signExpand <| .seq signNonce <| .seq signChallenge <|
  .block (restoreRegs .r25 224 signRegs)

/-! ## `vg_ed25519_verify(pk = r3, message = r4, len = r5, signature = r6, scratch = r7)`, `F` in `r8`

`F`: the challenge (64 bytes, its upper half zero) at 0, the digest at 64, the saves at 128. -/

def verifyRegs : List Reg := [.r20, .r21, .r22, .r23, .r24, .r25]

/-- The setup, the challenge (reduced, its upper half zeroed) and the arguments of `verify_equation`. -/
def verifyHash : Prog isa :=
  .seq (.block (saveRegs .r8 128 verifyRegs ++
    [mov .r20 .r3, mov .r21 .r4, mov .r22 .r5, mov .r23 .r6, mov .r24 .r7, mov .r25 .r8])) <|
  .seq (hashInit .r24) <|
  .seq (hashUpdate .r24 [.li .r4 0] .r23 0 [.li .r6 32]) <|
  .seq (hashUpdate .r24 [.li .r4 32] .r20 0 [.li .r6 32]) <|
  .seq (hashUpdate .r24 [.li .r4 64] .r21 0 [mov .r6 .r22]) <|
  .seq (hashFinalize .r24 [.addi .r4 .r22 64] .r25 64) <|
  .seq (.block [.addi .r3 .r25 0, .addi .r4 .r25 64, mov .r5 .r24]) <|
  .seq (.call "vg_ed25519_scalar_reduce" scalarReduce) <|
  .block [.li .r8 0, .store .d .r8 .r25 32, .store .d .r8 .r25 40, .store .d .r8 .r25 48,
    .store .d .r8 .r25 56, mov .r3 .r20, mov .r4 .r23, .addi .r5 .r25 0, mov .r6 .r24]

def verifyMessage : Prog isa :=
  .seq verifyHash <| .seq (.call "vg_ed25519_verify_equation" verifyEquation) <|
  .block (restoreRegs .r25 128 verifyRegs)

/-! ## The functions, with their frames -/

def publicKeyCode : Prog isa := Impl.StackScratch.PPC64LE.withStackScratchWiped 176 .r6 17 publicKey
def signCachedCode : Prog isa := Impl.StackScratch.PPC64LE.withStackScratchWiped 320 .r9 28 signCached
def verifyCode : Prog isa := Impl.StackScratch.PPC64LE.withStackScratch 224 .r8 verifyMessage

end VG.Impl.Ed25519.PPC64LE.Whole
