module

public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
public import VerifiedGarbage.Impl.Ed448.RISCV64.Scalar
public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.Impl.Sha3.RISCV64.Zero
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 on RISC-V: the whole functions

The PPC64LE design (`Impl/Ed448/PPC64LE/Whole.lean`), with RISC-V's
conventions as in Ed25519's port (`Impl/Ed25519/RISCV64/Whole.lean`):
`publicKey`, `signCached` and `verifyMessage` hash with the verified SHA-3
sponge functions and compute with the verified Ed448 functions, by calls.
Each is written for one more argument than its signature has, a frame
buffer `F` on the stack: in `a3` for `publicKey` and `a7` for `verify`
(`withStackScratch`), and for `signCached`, whose arguments fill `a0`–`a7`,
on the stack (`withStackScratchArgs`), read once at the start. The caller's
`scratch` holds the Keccak state (at 0) during a hash, and is the working
space of the Ed448 functions called; the sponge functions keep their working
space in frames of their own below ours. Everything that lives across calls
is in `F`: the hashes and scalars, the first ten bytes of `dom4(0, C)`,
copies of the public key and the signature, our caller's callee-saved
registers that we use, and `ra`.

The pointers and lengths stay in `s0`, `s1` and `s7`–`s11`, which no
function called writes (the sponge functions save and restore `s2`–`s6`;
the Ed448 functions use only caller-saved registers), so that the taint
analysis, to which a register restored from memory is secret, sees them
public after each call. That is seven registers: the signer copies `pk` into
`F` and keeps `seed`, read only by the first hash before any call, in `s2`;
the verifier copies `pk` and the signature into `F`, from where it hashes
them and passes them to `vg_ed448_verify_equation`. `F` is at a multiple of
8, so its slots take `ld`/`sd`; the arguments are read a byte at a time.

A hash (`hash`) zeroes the Keccak state, absorbs its pieces one after the
other, each from the position the previous one returned, pads with SHAKE's
suffix, and squeezes 114 bytes (`SHAKE256`, rate 136).
-/

@[expose] public section

namespace VG.Impl.Ed448.RISCV64.Whole

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.Ed25519.RISCV64.Whole (mov saveRegs restoreRegs copyIn)

/-- A piece's length: a constant, or a register. -/
inductive Len where
  | imm (n : Nat)
  | reg (r : Reg)

/-- `a4` set to the length. -/
def Len.set : Len → Instr
  | .imm n => .li .a4 n
  | .reg r => mov .a4 r

/-- A piece of the message: `off` bytes past the pointer in `base`. -/
structure Piece where
  base : Reg
  off : Nat
  len : Len

/-- `absorb(state = sc, rate = 136, pos, data, len)`: `pos` 0 for the first
piece, else the position the previous absorption returned. -/
def absorbArgs (sc : Reg) (first : Bool) (p : Piece) : List Instr :=
  [.addi .a3 p.base p.off, if first then .li .a2 0 else mov .a2 .a0, mov .a0 sc, .li .a1 136, p.len.set]

def callAbsorb : Prog isa := .call Spec.Sha3.absorbApi.name Impl.Sha3.RISCV64.Stream.absorb
def callPad : Prog isa := .call Spec.Sha3.padApi.name Impl.Sha3.RISCV64.Stream.pad
def callSqueeze : Prog isa := .call Spec.Sha3.squeezeApi.name Impl.Sha3.RISCV64.Stream.squeeze

/-- Absorbing the pieces `ps`. -/
def absorbs (sc : Reg) : Bool → List Piece → Prog isa
  | _, [] => .block []
  | first, p :: ps => .seq (.block (absorbArgs sc first p)) (.seq callAbsorb (absorbs sc false ps))

/-- `pad(state = sc, rate = 136, pos = a0, suffix = 0x1f)`. -/
def padArgs (sc : Reg) : List Instr := [mov .a2 .a0, mov .a0 sc, .li .a1 136, .li .a3 0x1f]

/-- `squeeze(state = sc, rate = 136, pos = 0, out = o(f), len = 114)`. -/
def squeezeArgs (sc f : Reg) (o : Nat) : List Instr :=
  [mov .a0 sc, .li .a1 136, .li .a2 0, .addi .a3 f o, .li .a4 114]

/-- `SHAKE256` of the concatenation of the pieces `ps`, 114 bytes, into `o(f)`. -/
def hash (sc : Reg) (ps : List Piece) (f : Reg) (o : Nat) : Prog isa :=
  .seq (.block (Impl.Sha3.RISCV64.zeroState sc)) <| .seq (absorbs sc true ps) <| .seq (.block (padArgs sc)) <|
  .seq callPad <| .seq (.block (squeezeArgs sc f o)) callSqueeze

/-- Pruning (`Spec.Ed448.prune`) in place on the 57 bytes at `o(f)`: bits 0–1 of
byte 0 cleared, bit 7 of byte 55 set, and byte 56 cleared. -/
def prune (f : Reg) (o : Nat) : List Instr :=
  [.load .b .a5 f o, .shift .srl .d .a5 .a5 2, .shift .sll .d .a5 .a5 2, .store .b .a5 f o,
    .load .b .a5 f (o + 55), .logicImm .or .a5 .a5 0x80, .store .b .a5 f (o + 55), .li .a5 0,
    .store .b .a5 f (o + 56)]

/-- The first ten bytes of `dom4(0, C)` at `0(f)`: `"SigEd448"` (its two
words built with `lui` and `addiw`), 0 and the length `c` (below 256). -/
def hdr (f c : Reg) : List Instr :=
  li32 .a5 0x38343464 ++ [.shift .sll .d .a5 .a5 32] ++ li32 .a6 0x45676953 ++
    [.logic .or .a5 .a5 .a6, .store .d .a5 f 0, .li .a5 0, .store .b .a5 f 8, .store .b c f 9]

/-- The `n` doublewords from `o(f)` zeroed. -/
def wipe (f : Reg) (o n : Nat) : List Instr := .li .a5 0 :: (List.range n).map fun k => .store .d .a5 f (o + 8 * k)

/-! ## `vg_ed448_public_key(out = a0, seed = a1, scratch = a2)`, `F` in `a3`

`F`: the hash at 0 (pruned in place), the saves at 120. -/

def pkRegs : List Reg := [.s7, .s8, .s9, .s10]

def publicKey : Prog isa :=
  .seq (.block (saveRegs .a3 120 pkRegs ++ [mov .s7 .a0, mov .s8 .a1, mov .s9 .a2, mov .s10 .a3])) <|
  .seq (hash .s9 [⟨.s8, 0, .imm 57⟩] .s10 0) <|
  .seq (.block (prune .s10 0 ++ [mov .a0 .s7, .addi .a1 .s10 0, mov .a2 .s9])) <|
  .seq (.call "vg_ed448_scalar_base" scalarBase) <|
  .block (restoreRegs .s10 120 pkRegs)

/-! ## `vg_ed448_sign_cached(out = a0, seed = a1, pk = a2, context = a3, ctxlen = a4, message = a5,
len = a6, scratch = a7)`, `F` at `0(sp)`

`F`: the header of `dom4` at 0, a hash at 16, `SHAKE256(seed, 114)` at 136 (the scalar `s`, pruned in
place, then the nonce's prefix at 193), the nonce `r` at 256, the challenge `k` at 320, a copy of `pk`
at 384, the saves at 448. `out`, `scratch`, `seed`, `context`, `ctxlen`, `message`, `len` and `F` are in
`s0`–`s2` and `s7`–`s11`. -/

def signRegs : List Reg := [.s0, .s1, .s2, .s7, .s8, .s9, .s10, .s11]

/-- `F`, the stack argument, read into `t0`. -/
def signFrame : List Instr := [.addSp .t0 0, .load .d .t0 .t0 0]

/-- The setup: the registers saved, the arguments moved, `pk` copied, the header written. -/
def signSetup : List Instr :=
  saveRegs .t0 448 signRegs ++
    [mov .s0 .a0, mov .s1 .a7, mov .s2 .a1, mov .s7 .a3, mov .s8 .a4, mov .s9 .a5, mov .s10 .a6,
      mov .s11 .t0] ++
    copyIn .a2 .s11 384 57 ++ hdr .s11 .s8

/-- `dom4(0, C)`: the header and the context. -/
def dom4Pieces (f ctx ctxlen : Reg) : List Piece := [⟨f, 0, .imm 10⟩, ⟨ctx, 0, .reg ctxlen⟩]

/-- `s` and the nonce's prefix. -/
def signExpand : Prog isa :=
  .seq (hash .s1 [⟨.s2, 0, .imm 57⟩] .s11 136) (.block (prune .s11 136))

/-- The nonce, and `R` into the first half of `out`. -/
def signNonce : Prog isa :=
  .seq (hash .s1 (dom4Pieces .s11 .s7 .s8 ++ [⟨.s11, 193, .imm 57⟩, ⟨.s9, 0, .reg .s10⟩]) .s11 16) <|
  .seq (.block [.addi .a0 .s11 256, .addi .a1 .s11 16, mov .a2 .s1]) <|
  .seq (.call "vg_ed448_scalar_reduce" scalarReduce) <|
  .seq (.block [mov .a0 .s0, .addi .a1 .s11 256, mov .a2 .s1]) <|
  .call "vg_ed448_scalar_base" scalarBase

/-- The challenge, and `S` into the second half of `out`. -/
def signChallenge : Prog isa :=
  .seq (hash .s1 (dom4Pieces .s11 .s7 .s8 ++ [⟨.s0, 0, .imm 57⟩, ⟨.s11, 384, .imm 57⟩, ⟨.s9, 0, .reg .s10⟩])
    .s11 16) <|
  .seq (.block [.addi .a0 .s11 320, .addi .a1 .s11 16, mov .a2 .s1]) <|
  .seq (.call "vg_ed448_scalar_reduce" scalarReduce) <|
  .seq (.block [.addi .a0 .s0 57, .addi .a1 .s11 256, .addi .a2 .s11 320, .addi .a3 .s11 136, mov .a4 .s1]) <|
  .call "vg_ed448_scalar_mul_add" scalarMulAdd

def signCached : Prog isa :=
  .seq (.block signFrame) <| .seq (.block signSetup) <| .seq signExpand <| .seq signNonce <| .seq signChallenge <|
  .block (wipe .s11 16 46 ++ restoreRegs .s11 448 signRegs)

/-! ## `vg_ed448_verify(pk = a0, context = a1, ctxlen = a2, message = a3, len = a4, signature = a5,
scratch = a6) -> a0`, `F` in `a7`

`F`: the header of `dom4` at 0, the hash at 16, the challenge `k` at 136, a copy of the signature at
200 and of `pk` at 320, the saves at 384. `scratch`, `context`, `ctxlen`, `message`, `len` and `F` are
in `s1` and `s7`–`s11`. If `ctxlen ≥ 256`, it returns 0 at once. -/

def verifyRegs : List Reg := [.s1, .s7, .s8, .s9, .s10, .s11]

/-- The setup, the challenge and the arguments of `verify_equation`. -/
def verifyHash : Prog isa :=
  .seq (.block (saveRegs .a7 384 verifyRegs ++
    [mov .s1 .a6, mov .s7 .a1, mov .s8 .a2, mov .s9 .a3, mov .s10 .a4, mov .s11 .a7, mov .t1 .a5] ++
    copyIn .t1 .s11 200 114 ++ copyIn .a0 .s11 320 57 ++ hdr .s11 .s8)) <|
  .seq (hash .s1 (dom4Pieces .s11 .s7 .s8 ++ [⟨.s11, 200, .imm 57⟩, ⟨.s11, 320, .imm 57⟩, ⟨.s9, 0, .reg .s10⟩])
    .s11 16) <|
  .seq (.block [.addi .a0 .s11 136, .addi .a1 .s11 16, mov .a2 .s1]) <|
  .seq (.call "vg_ed448_scalar_reduce" scalarReduce) <|
  .block [.addi .a0 .s11 320, .addi .a1 .s11 200, .addi .a2 .s11 136, mov .a3 .s1]

def verifyMain : Prog isa :=
  .seq verifyHash <| .seq (.call "vg_ed448_verify_equation" verifyEquation) <|
  .block (restoreRegs .s11 384 verifyRegs)

/-- `ctxlen < 256`: `ctxlen >> 8` is zero. -/
def verifyMessage : Prog isa :=
  .seq (.block [.shift .srl .d .t0 .a2 8]) (.ite (.zero .t0) verifyMain (.block [.li .a0 0]))

/-! ## The functions, with their frames -/

def publicKeyCode : Prog isa := Impl.StackScratch.RISCV64.withStackScratchWiped 160 .a3 15 publicKey
def signCachedCode : Prog isa := Impl.StackScratch.RISCV64.withStackScratchArgs 528 0 signCached
def verifyCode : Prog isa := Impl.StackScratch.RISCV64.withStackScratch 448 .a7 verifyMessage

end VG.Impl.Ed448.RISCV64.Whole
