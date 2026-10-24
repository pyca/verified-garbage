module

public import VerifiedGarbage.Impl.Ed448.PPC64LE.ScalarBase
public import VerifiedGarbage.Impl.Ed448.PPC64LE.Scalar
public import VerifiedGarbage.Impl.Ed448.PPC64LE.VerifyEquation
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Whole
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Sample
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args

/-!
# Ed448 on PPC64LE: the whole functions

As Ed25519's on this target (`Impl/Ed25519/PPC64LE/Whole.lean`):
`publicKey`, `signCached` and `verifyMessage` hash with the verified
SHA-3 sponge functions and compute with the verified Ed448 functions, by
calls. Each is written for one more argument than its signature has, a frame
buffer `F` on the stack: in `r6` for `publicKey` and `r10` for `verify`
(`withStackScratch`), and for `signCached`, whose arguments fill `r3`–`r10`,
on the stack (`withStackScratchArgs`), read once at the start. The caller's
`scratch` holds the Keccak state (at 0) and the sponge functions' working
space (at 200) during a hash, and is the working space of the Ed448
functions called; everything that lives across calls is in `F`: the hashes
and scalars, the first ten bytes of `dom4(0, C)`, our caller's nonvolatile
registers that we use, and the link register. The pointers and lengths stay
in `r20`–`r25` and `r28`–`r30`, which no function called writes (the Ed448
functions save `r14`–`r19`, `r26` and `r27` in their working space, and the
sponge functions `r14`–`r20` and `r26`–`r31`, restoring them).

A hash (`hash`) zeroes the Keccak state (as ML-KEM's do), absorbs its pieces one after the
other, each from the position the previous one returned, pads with SHAKE's
suffix, and squeezes 114 bytes (`SHAKE256`, rate 136).
-/

@[expose] public section

namespace VG.Impl.Ed448.PPC64LE.Whole

open VG.PPC64LE
open VG.Impl.Ed25519.PPC64LE.Whole (mov saveRegs restoreRegs)

/-- Where in `scratch` the sponge functions' working space is. -/
def KW : Nat := 200

/-- A piece's length: a constant, or a register. -/
inductive Len where
  | imm (n : Nat)
  | reg (r : Reg)

/-- `r7` set to the length. -/
def Len.set : Len → Instr
  | .imm n => .li .r7 n
  | .reg r => mov .r7 r

/-- A piece of the message: `off` bytes past the pointer in `base`. -/
structure Piece where
  base : Reg
  off : Nat
  len : Len

/-- `absorb(state = sc, rate = 136, pos, data, len, sc + 200)`: `pos` 0 for the
first piece, else the position the previous absorption returned. -/
def absorbArgs (sc : Reg) (first : Bool) (p : Piece) : List Instr :=
  [if first then .li .r5 0 else mov .r5 .r3, mov .r3 sc, .li .r4 136, .addi .r6 p.base p.off, p.len.set,
    .addi .r8 sc KW]

def callAbsorb : Prog isa := .call "vg_keccak_absorb_scratch" Impl.Sha3.PPC64LE.Stream.absorb
def callPad : Prog isa := .call "vg_keccak_pad_scratch" Impl.Sha3.PPC64LE.Stream.pad
def callSqueeze : Prog isa := .call "vg_keccak_squeeze_scratch" Impl.Sha3.PPC64LE.Stream.squeeze

/-- Absorbing the pieces `ps`. -/
def absorbs (sc : Reg) : Bool → List Piece → Prog isa
  | _, [] => .block []
  | first, p :: ps => .seq (.block (absorbArgs sc first p)) (.seq callAbsorb (absorbs sc false ps))

/-- `pad(state = sc, rate = 136, pos = r3, suffix = 0x1f, sc + 200)`. -/
def padArgs (sc : Reg) : List Instr := [mov .r5 .r3, mov .r3 sc, .li .r4 136, .li .r6 0x1f, .addi .r7 sc KW]

/-- `squeeze(state = sc, rate = 136, pos = 0, out = o(f), len = 114, sc + 200)`. -/
def squeezeArgs (sc f : Reg) (o : Nat) : List Instr :=
  [mov .r3 sc, .li .r4 136, .li .r5 0, .addi .r6 f o, .li .r7 114, .addi .r8 sc KW]

/-- `SHAKE256` of the concatenation of the pieces `ps`, 114 bytes, into `o(f)`. -/
def hash (sc : Reg) (ps : List Piece) (f : Reg) (o : Nat) : Prog isa :=
  .seq (.block (Impl.MlKem.PPC64LE.zeroState sc)) <| .seq (absorbs sc true ps) <| .seq (.block (padArgs sc)) <|
  .seq callPad <| .seq (.block (squeezeArgs sc f o)) callSqueeze

/-- Pruning (`Spec.Ed448.prune`) in place on the 57 bytes at `o(f)`: bits 0–1 of
byte 0 cleared, bit 7 of byte 55 set, and byte 56 cleared. -/
def prune (f : Reg) (o : Nat) : List Instr :=
  [.lbz .r8 f o, .lsr .d .r8 .r8 2, .lsl .r8 .r8 2, .stb .r8 f o,
    .lbz .r8 f (o + 55), .ori .r8 .r8 0x80, .stb .r8 f (o + 55), .li .r8 0, .stb .r8 f (o + 56)]

/-- The first ten bytes of `dom4(0, C)` at `0(f)`: `"SigEd448"`, 0 and the length `c` (below 256). -/
def hdr (f c : Reg) : List Instr :=
  [.lis .r8 0x3834, .ori .r8 .r8 0x3464, .lsl .r8 .r8 32, .oris .r8 .r8 0x4567, .ori .r8 .r8 0x6953,
    .store .d .r8 f 0, .li .r8 0, .stb .r8 f 8, .stb c f 9]

/-- The `n` doublewords from `o(f)` zeroed. -/
def wipe (f : Reg) (o n : Nat) : List Instr := .li .r8 0 :: (List.range n).map fun k => .store .d .r8 f (o + 8 * k)

/-! ## `vg_ed448_public_key(out = r3, seed = r4, scratch = r5)`, `F` in `r6`

`F`: the hash at 0 (pruned in place), the saves at 120. -/

def pkRegs : List Reg := [.r21, .r22, .r23, .r24]

def publicKey : Prog isa :=
  .seq (.block (saveRegs .r6 120 pkRegs ++ [mov .r21 .r3, mov .r22 .r4, mov .r23 .r5, mov .r24 .r6])) <|
  .seq (hash .r23 [⟨.r22, 0, .imm 57⟩] .r24 0) <|
  .seq (.block (prune .r24 0 ++ [mov .r3 .r21, .addi .r4 .r24 0, mov .r5 .r23])) <|
  .seq (.call "vg_ed448_scalar_base" scalarBase) <|
  .block (restoreRegs .r24 120 pkRegs)

/-! ## `vg_ed448_sign_cached(out = r3, seed = r4, pk = r5, context = r6, ctxlen = r7, message = r8,
len = r9, scratch = r10)`, `F` at `96(r1)`

`F`: the header of `dom4` at 0, a hash at 16, `SHAKE256(seed, 114)` at 136 (the scalar `s`, pruned in
place, then the nonce's prefix at 193), the nonce `r` at 256, the challenge `k` at 320, the saves at
384. -/

def signRegs : List Reg := [.r20, .r22, .r23, .r24, .r25, .r28, .r29, .r30, .r21]

/-- `F`, the stack argument, read into `r12`. -/
def signFrame : List Instr := [.addSp .r12 0, .load .d .r12 .r12 96]

/-- The setup: the registers saved, the arguments moved, the header written. -/
def signSetup : List Instr :=
  saveRegs .r12 384 signRegs ++
    [mov .r20 .r3, mov .r22 .r10, mov .r23 .r4, mov .r24 .r5, mov .r25 .r6, mov .r28 .r7, mov .r29 .r8,
      mov .r30 .r9, mov .r21 .r12] ++ hdr .r21 .r28

/-- `dom4(0, C)`: the header and the context. -/
def dom4Pieces (f ctx ctxlen : Reg) : List Piece := [⟨f, 0, .imm 10⟩, ⟨ctx, 0, .reg ctxlen⟩]

/-- `s` and the nonce's prefix. -/
def signExpand : Prog isa :=
  .seq (hash .r22 [⟨.r23, 0, .imm 57⟩] .r21 136) (.block (prune .r21 136))

/-- The nonce, and `R` into the first half of `out`. -/
def signNonce : Prog isa :=
  .seq (hash .r22 (dom4Pieces .r21 .r25 .r28 ++ [⟨.r21, 193, .imm 57⟩, ⟨.r29, 0, .reg .r30⟩]) .r21 16) <|
  .seq (.block [.addi .r3 .r21 256, .addi .r4 .r21 16, mov .r5 .r22]) <|
  .seq (.call "vg_ed448_scalar_reduce" scalarReduce) <|
  .seq (.block [mov .r3 .r20, .addi .r4 .r21 256, mov .r5 .r22]) <|
  .call "vg_ed448_scalar_base" scalarBase

/-- The challenge, and `S` into the second half of `out`. -/
def signChallenge : Prog isa :=
  .seq (hash .r22 (dom4Pieces .r21 .r25 .r28 ++ [⟨.r20, 0, .imm 57⟩, ⟨.r24, 0, .imm 57⟩, ⟨.r29, 0, .reg .r30⟩])
    .r21 16) <|
  .seq (.block [.addi .r3 .r21 320, .addi .r4 .r21 16, mov .r5 .r22]) <|
  .seq (.call "vg_ed448_scalar_reduce" scalarReduce) <|
  .seq (.block [.addi .r3 .r20 57, .addi .r4 .r21 256, .addi .r5 .r21 320, .addi .r6 .r21 136, mov .r7 .r22]) <|
  .call "vg_ed448_scalar_mul_add" scalarMulAdd

def signCached : Prog isa :=
  .seq (.block signFrame) <| .seq (.block signSetup) <| .seq signExpand <| .seq signNonce <| .seq signChallenge <|
  .block (wipe .r21 16 46 ++ restoreRegs .r21 384 signRegs)

/-! ## `vg_ed448_verify(pk = r3, context = r4, ctxlen = r5, message = r6, len = r7, signature = r8,
scratch = r9) -> r3`, `F` in `r10`

`F`: the header of `dom4` at 0, the hash at 16, the challenge `k` at 136, the saves at 200. If
`ctxlen ≥ 256`, it returns 0 at once. -/

def verifyRegs : List Reg := [.r20, .r21, .r22, .r23, .r24, .r25, .r28, .r29]

/-- The setup, the challenge and the arguments of `verify_equation`. -/
def verifyHash : Prog isa :=
  .seq (.block (saveRegs .r10 200 verifyRegs ++
    [mov .r20 .r3, mov .r21 .r4, mov .r22 .r5, mov .r23 .r6, mov .r24 .r7, mov .r25 .r8, mov .r28 .r9,
      mov .r29 .r10] ++ hdr .r29 .r22)) <|
  .seq (hash .r28 (dom4Pieces .r29 .r21 .r22 ++ [⟨.r25, 0, .imm 57⟩, ⟨.r20, 0, .imm 57⟩, ⟨.r23, 0, .reg .r24⟩])
    .r29 16) <|
  .seq (.block [.addi .r3 .r29 136, .addi .r4 .r29 16, mov .r5 .r28]) <|
  .seq (.call "vg_ed448_scalar_reduce" scalarReduce) <|
  .block [mov .r3 .r20, mov .r4 .r25, .addi .r5 .r29 136, mov .r6 .r28]

def verifyMain : Prog isa :=
  .seq verifyHash <| .seq (.call "vg_ed448_verify_equation" verifyEquation) <|
  .block (restoreRegs .r29 200 verifyRegs)

/-- `ctxlen < 256`: `ctxlen >> 8` is zero. -/
def verifyMessage : Prog isa :=
  .seq (.block [.lsr .d .r11 .r5 8]) (.ite (.zero .d .r11) verifyMain (.block [.li .r3 0]))

/-! ## The functions, with their frames -/

def publicKeyCode : Prog isa := Impl.StackScratch.PPC64LE.withStackScratchWiped 192 .r6 15 publicKey
def signCachedCode : Prog isa := Impl.StackScratch.PPC64LE.withStackScratchArgs 576 0 signCached
def verifyCode : Prog isa := Impl.StackScratch.PPC64LE.withStackScratch 304 .r10 verifyMessage

end VG.Impl.Ed448.PPC64LE.Whole
