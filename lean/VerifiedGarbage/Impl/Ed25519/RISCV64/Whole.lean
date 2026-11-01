module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Verify
public import VerifiedGarbage.Impl.Ed25519.RISCV64.ScalarBase
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar
public import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.TCB.Artifact

/-!
# Ed25519 on RISC-V: the whole functions

The PPC64LE design (`Impl/Ed25519/PPC64LE/Whole.lean`): `publicKey`,
`signCached` and `verifyMessage` hash with SHA-512's verified streaming
functions and compute with the verified Ed25519 functions, by calls. Each
is written for one more argument than its signature has, a frame buffer `F`
that `withStackScratch` allocates on the stack (wiped after use when it
holds secrets). The caller's `scratch` holds SHA-512's state (at 0) during
a hash, and is the working space of the Ed25519 functions called; SHA-512's
`update` and `finalize` keep their working space in frames of their own
below ours. Everything that lives across calls is in `F`: the digests and
scalars, our caller's callee-saved registers that we use, and `ra`. The
pointers stay in `s7`–`s11`, which no function called writes (SHA-512's
save and restore `s0`–`s6`, `vg_ed25519_scalar_base` `s0`–`s3`, `s5` and
`s6`, and the scalar functions none), so that the taint analysis, to which
a register restored from memory is secret, sees them public after each
call. That is five registers: the signer keeps `seed`, needed only for the
first hash, in `s1`, which nothing writes before it is used, and the
verifier copies `pk` and the signature into `F`, from where it hashes them
and passes them to `vg_ed25519_verify_equation`. `F` is on the
stack, so aligned to 16 bytes, and its slots take `ld`/`sd`; the arguments
are read only by the functions called, but for `pk`, which `signCached`
copies a byte at a time.
-/

@[expose] public section

namespace VG.Impl.Ed25519.RISCV64.Whole

open VG.RISCV64

def mov (d n : Reg) : Instr := .addi d n 0

def shaInit : Prog isa :=
  .call Spec.Sha512.init512Api.name (Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512)
def shaUpdate : Prog isa := .call Spec.Sha512.updateApi.name Impl.Sha512.RISCV64.Stream.update
def shaFinalize : Prog isa := .call Spec.Sha512.finalizeApi.name Impl.Sha512.RISCV64.Stream.finalize

/-- The slots at `o(F)` of the registers of `rs` and, after them, of `ra`. -/
def slots (o : Nat) (rs : List Reg) : List (Reg × Nat) :=
  (rs ++ [Reg.ra]).zipIdx.map fun (r, i) => (r, o + 8 * i)

/-- Saving the registers of `rs` and `ra` in their slots, `F` in `f`. -/
def saveRegs (f : Reg) (o : Nat) (rs : List Reg) : List Instr :=
  (slots o rs).map fun (r, d) => .store .d r f d

/-- Restoring them, `ra` first; `f`, the base, must be the last of `rs`. -/
def restoreRegs (f : Reg) (o : Nat) (rs : List Reg) : List Instr :=
  ((Reg.ra, o + 8 * rs.length) :: (slots o rs).dropLast).map fun (r, d) => .load .d r f d

/-- `init` of the state at `scratch` (`sc`). -/
def hashInit (sc : Reg) : Prog isa := .seq (.block [mov .a0 sc]) shaInit

/-- `update` with the `len` bytes at `off(src)`: `count` (in `a1`) and `len` (in `a3`) are set
by `cnt` and `ln`. -/
def hashUpdate (sc : Reg) (cnt : List Instr) (src : Reg) (srcOff : Nat) (ln : List Instr) : Prog isa :=
  .seq (.block ([mov .a0 sc] ++ cnt ++ [.addi .a2 src srcOff] ++ ln)) shaUpdate

/-- `finalize` into `o(F)`. -/
def hashFinalize (sc : Reg) (cnt : List Instr) (f : Reg) (o : Nat) : Prog isa :=
  .seq (.block ([mov .a0 sc] ++ cnt ++ [.addi .a2 f o])) shaFinalize

/-- The pruning of the digest's first half at `d(F)` into `o(F)`: bits 0–2 and 255 cleared, 254 set. -/
def prune (f : Reg) (d o : Nat) : List Instr :=
  [.load .d .a5 f d, .shift .srl .d .a5 .a5 3, .shift .sll .d .a5 .a5 3, .store .d .a5 f o,
    .load .d .a5 f (d + 8), .store .d .a5 f (o + 8),
    .load .d .a5 f (d + 16), .store .d .a5 f (o + 16),
    .load .d .a5 f (d + 24), .shift .sll .d .a5 .a5 2, .shift .srl .d .a5 .a5 2, .li .a6 1,
    .shift .sll .d .a6 .a6 62, .logic .or .a5 .a5 .a6, .store .d .a5 f (o + 24)]

/-- Copying the 32 bytes at `d(F)` to `o(F)`. -/
def copy32 (f : Reg) (d o : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [.load .d .a5 f (d + 8 * k), .store .d .a5 f (o + 8 * k)]

/-- Copying the `n` bytes at `src`, a byte at a time, to `o(F)`. -/
def copyIn (src f : Reg) (o : Nat) (n : Nat := 32) : List Instr := Impl.Words.RISCV64.copyBytes .a5 src f 0 o n

/-! ## `vg_ed25519_public_key(out = a0, seed = a1, scratch = a2)`, `F` in `a3`

`F`: the digest at 0, the scalar at 64, the saves at 96. -/

def pkRegs : List Reg := [.s7, .s8, .s9, .s10]

def publicKey : Prog isa :=
  .seq (.block (saveRegs .a3 96 pkRegs ++ [mov .s7 .a0, mov .s8 .a1, mov .s9 .a2, mov .s10 .a3])) <|
  .seq (hashInit .s9) <|
  .seq (hashUpdate .s9 [.li .a1 0] .s8 0 [.li .a3 32]) <|
  .seq (hashFinalize .s9 [.li .a1 32] .s10 0) <|
  .seq (.block (prune .s10 0 64 ++ [mov .a0 .s7, .addi .a1 .s10 64, mov .a2 .s9])) <|
  .seq (.call "vg_ed25519_scalar_base" scalarBase) <|
  .block (restoreRegs .s10 96 pkRegs)

/-! ## `vg_ed25519_sign_cached(out = a0, seed = a1, pk = a2, message = a3, len = a4, scratch = a5)`,
`F` in `a6`

`F`: the scalar at 0, the nonce's prefix at 32, the nonce at 64, the challenge at 96, the digest at
128, a copy of `pk` at 192, the saves at 224. `out`, `message`, `len`, `scratch` and `F` are in
`s7`–`s11`; `pk` is copied first, and `seed`, in `s1`, is needed only for the first hash. -/

def signRegs : List Reg := [.s1, .s7, .s8, .s9, .s10, .s11]

/-- The setup: the registers saved, the pointers moved, `pk` copied. -/
def signSetup : List Instr :=
  saveRegs .a6 224 signRegs ++
    ([mov .s7 .a0, mov .s1 .a1, mov .s8 .a3, mov .s9 .a4, mov .s10 .a5, mov .s11 .a6] ++ copyIn .a2 .s11 192)

/-- The secret scalar and the nonce's prefix. -/
def signExpand : Prog isa :=
  .seq (hashInit .s10) <|
  .seq (hashUpdate .s10 [.li .a1 0] .s1 0 [.li .a3 32]) <|
  .seq (hashFinalize .s10 [.li .a1 32] .s11 128) <|
  .block (prune .s11 128 0 ++ copy32 .s11 160 32)

/-- The nonce, and `R`. -/
def signNonce : Prog isa :=
  .seq (hashInit .s10) <|
  .seq (hashUpdate .s10 [.li .a1 0] .s11 32 [.li .a3 32]) <|
  .seq (hashUpdate .s10 [.li .a1 32] .s8 0 [mov .a3 .s9]) <|
  .seq (hashFinalize .s10 [.addi .a1 .s9 32] .s11 128) <|
  .seq (.block [.addi .a0 .s11 64, .addi .a1 .s11 128, mov .a2 .s10]) <|
  .seq (.call "vg_ed25519_scalar_reduce" scalarReduce) <|
  .seq (.block [mov .a0 .s7, .addi .a1 .s11 64, mov .a2 .s10]) <|
  .call "vg_ed25519_scalar_base" scalarBase

/-- The challenge, and `S`. -/
def signChallenge : Prog isa :=
  .seq (hashInit .s10) <|
  .seq (hashUpdate .s10 [.li .a1 0] .s7 0 [.li .a3 32]) <|
  .seq (hashUpdate .s10 [.li .a1 32] .s11 192 [.li .a3 32]) <|
  .seq (hashUpdate .s10 [.li .a1 64] .s8 0 [mov .a3 .s9]) <|
  .seq (hashFinalize .s10 [.addi .a1 .s9 64] .s11 128) <|
  .seq (.block [.addi .a0 .s11 96, .addi .a1 .s11 128, mov .a2 .s10]) <|
  .seq (.call "vg_ed25519_scalar_reduce" scalarReduce) <|
  .seq (.block [.addi .a0 .s7 32, .addi .a1 .s11 64, .addi .a2 .s11 96, .addi .a3 .s11 0, mov .a4 .s10]) <|
  .call "vg_ed25519_scalar_mul_add" scalarMulAdd

def signCached : Prog isa :=
  .seq (.block signSetup) <| .seq signExpand <| .seq signNonce <| .seq signChallenge <|
  .block (restoreRegs .s11 224 signRegs)

/-! ## `vg_ed25519_verify(pk = a0, message = a1, len = a2, signature = a3, scratch = a4)`, `F` in `a5`

`F`: the challenge (64 bytes, its upper half zero) at 0, the digest at 64, a copy of the signature
at 128 and of `pk` at 192, the saves at 224. `message`, `len`, `scratch` and `F` are in `s7`–`s10`. -/

def verifyRegs : List Reg := [.s7, .s8, .s9, .s10]

/-- The setup, the challenge (reduced, its upper half zeroed) and the arguments of `verify_equation`. -/
def verifyHash : Prog isa :=
  .seq (.block (saveRegs .a5 224 verifyRegs ++
    ([mov .s7 .a1, mov .s8 .a2, mov .s9 .a4, mov .s10 .a5] ++ copyIn .a3 .s10 128 64 ++ copyIn .a0 .s10 192))) <|
  .seq (hashInit .s9) <|
  .seq (hashUpdate .s9 [.li .a1 0] .s10 128 [.li .a3 32]) <|
  .seq (hashUpdate .s9 [.li .a1 32] .s10 192 [.li .a3 32]) <|
  .seq (hashUpdate .s9 [.li .a1 64] .s7 0 [mov .a3 .s8]) <|
  .seq (hashFinalize .s9 [.addi .a1 .s8 64] .s10 64) <|
  .seq (.block [.addi .a0 .s10 0, .addi .a1 .s10 64, mov .a2 .s9]) <|
  .seq (.call "vg_ed25519_scalar_reduce" scalarReduce) <|
  .block [.li .a5 0, .store .d .a5 .s10 32, .store .d .a5 .s10 40, .store .d .a5 .s10 48,
    .store .d .a5 .s10 56, .addi .a0 .s10 192, .addi .a1 .s10 128, .addi .a2 .s10 0, mov .a3 .s9]

def verifyMessage : Prog isa :=
  .seq verifyHash <| .seq (.call "vg_ed25519_verify_equation" verifyEquation) <|
  .block (restoreRegs .s10 224 verifyRegs)

/-! ## The functions, with their frames -/

def publicKeyCode : Prog isa := Impl.StackScratch.RISCV64.withStackScratchWiped 144 .a3 17 publicKey
def signCachedCode : Prog isa := Impl.StackScratch.RISCV64.withStackScratchWiped 288 .a6 28 signCached
def verifyCode : Prog isa := Impl.StackScratch.RISCV64.withStackScratch 272 .a5 verifyMessage

end VG.Impl.Ed25519.RISCV64.Whole
