module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Fn
public import VerifiedGarbage.Impl.Gcm.AArch64.Forward

/-!
# AES-GCM gather sealing directly into the output buffer

Each descriptor is read once. Whole blocks use out-of-place counter mode,
and a descriptor ending in a partial block leaves the unused keystream in
the state for the next descriptor. GHASH reads the resulting ciphertext.
-/

@[expose] public section
namespace VG.Impl.AesGcm.AArch64.DirectGather
open VG.AArch64

/-- Transfer at most fifteen bytes across a fragment boundary. The source,
destination and keystream cursor advance together. -/
def xorBytes : Prog isa :=
  .ite (.zero .x .x10) (.block []) <|
    .loop (.block [.ldrb .x13 .x23 0, .ldrb .x14 .x11 0, .logic .eor .w .x13 .x13 .x14,
      .strb .x13 .x26 0, ptr .x23 .x23 1, ptr .x11 .x11 1, ptr .x26 .x26 1,
      .subImm .x .x24 .x24 1, .subImm .x .x10 .x10 1]) (.nonzero .x .x10)

/-- Consume the unused suffix of the preceding counter block, if any.
`x25` holds the offset of the next byte within its block. -/
def leftover : Prog isa :=
  .ite (.zero .x .x25) (.block []) <|
    .seq minK <| .seq (.block [ptr .x11 .x20 64, .add .x .x11 .x11 .x25,
      .add .x .x25 .x25 .x10, imm .x9 15, .logic .and .x .x25 .x25 .x9]) xorBytes

/-- Encrypt the rest of a piece, beginning at a counter block boundary. -/
def alignedWith (c : Callees) (first tail : Prog isa) : Prog isa :=
  .seq (.block (crArgsG true)) <| .seq first <|
    .ite (.zero .x .x24) (.block []) <|
    .seq crSeg2 <| .seq (ctrCall c) <|
    .seq (.block [mov .x10 .x24, mov .x25 .x24, ptr .x11 .x20 64]) tail

def aligned (c : Callees) : Prog isa := alignedWith c (ctrCallG c true) xorBytes

/-- Pointers to the descriptors and their count, kept across nonce and AAD
processing in two unused words between the saved registers and scratch. -/
def descO := 336
def countO := 344

/-- The beginning of the ciphertext that has not yet been hashed. -/
def hashO := 352

/-- Build the interleaved table from the hash subkey in the ordinary key context. -/
def tableFromKey : List Instr :=
  [mov .x0 .x21] ++ Gcm.AArch64.Pmull.keyPrologue ++ Gcm.AArch64.Pmull.powersS ++ Stitch.tbl

/-- Before hashing a batch in the interleaved loop, finish hashing earlier
fragments up to the current (block-aligned) destination. -/
def hashPending (c : Callees) : Prog isa :=
  .seq (.block [.ldr .x .x2 .x19 hashO, .sub .x .x3 .x26 .x2, .lsr .x .x3 .x3 4]) <|
    .ite (.zero .x .x3) (.block [])
      (.seq (.block (ghArgs 16)) (ghCall c))

/-- With a fresh counter block, seal whole batches of a long piece while
authenticating them. The source and destination advance together, and the
remaining bytes can use the ordinary out-of-place counter loop. -/
def batches (c : Callees) (forward : Bool := false) (table : List Instr := tableFromKey) : Prog isa :=
  .seq (.block [.addImm .x .x9 .x24 (1024 - Stitch.minLen), .lsr .x .x9 .x9 10]) <|
  .ite (.zero .x .x9) (.block []) <|
    .seq (hashPending c) <|
    .seq (.block ([mov .x15 .x23, mov .x23 .x26, mov .x26 .x24] ++
        table)) <|
    .seq (Gcm.AArch64.Stitch.sealCallFor forward) <|
      .block ([mov .x26 .x9, mov .x23 .x15, imm .x10 127,
        .logic .and .x .x24 .x24 .x10, .str .x .x26 .x19 hashO])

/-- `x27` points to the descriptors, `x28` counts them and `x26` points to
the next destination byte. Empty descriptors consume no keystream. -/
def pieces (c : Callees) (stitch : Bool) : Prog isa :=
  .ite (.zero .x .x28) (.block []) <|
    .loop (.seq (.block [.ldr .x .x23 .x27 0, .ldr .x .x24 .x27 8, ptr .x27 .x27 16]) <|
      .seq leftover <| .seq (if stitch then batches c else .block []) <|
      .seq (.ite (.zero .x .x24) (.block []) (aligned c)) <|
        .block [.subImm .x .x28 .x28 1]) (.nonzero .x .x28)

/-- Generate seven AES counter blocks for a short record. One supplies the
tag mask and the remaining blocks supply the keystream. -/
def shortKeys (base nr : Nat) : Prog isa := Id.run do
  let lanes := (List.range 7).map Gcm.AArch64.Stitch.breg
  let seed : List Instr := [.ldr .x .x9 .x23 0, .ldr .w .x10 .x23 8,
    .vop (.ins .d2 .v31 0 .x9), .vop (.ins .s4 .v31 2 .x10)]
  let counters := (List.range 7).flatMap fun i =>
    let r := Gcm.AArch64.Stitch.breg i
    ([.vop (.logic .orr r .v31 .v31), .movz .w .x12 (BitVec.ofNat 16 (256 * (i+1))) 1,
      .vop (.ins .s4 r 3 .x12)] : List Instr)
  let rounds := (List.range (nr - 1)).flatMap fun i =>
    .ldrq .v30 .x21 (16 * i) :: lanes.flatMap fun r => [Instr.vop (.aese r .v30), .vop (.aesmc r r)]
  let last := [.ldrq .v30 .x21 (16 * (nr - 1))] ++ lanes.map (fun r => Instr.vop (.aese r .v30)) ++
    [.ldrq .v30 .x21 (16 * nr)] ++ (List.range 7).flatMap (fun i =>
      let r := Gcm.AArch64.Stitch.breg i
      ([.vop (.logic .eor r r .v30), .strq r .x19 (base + 16*i)] : List Instr))
  return .block (seed ++ counters ++ rounds ++ last)

/-- Load both ends before storing either one, since the two words may
overlap when the whole fragment is shorter than twice the word width. -/
def xorEnds (sz : Size) (n : Nat) : List Instr :=
  [.ldr sz .x14 .x0 0, .ldr sz .x15 .x1 0, .logic .eor sz .x13 .x14 .x15,
   .subImm .x .x12 .x12 n, .add .x .x0 .x0 .x12, .add .x .x1 .x1 .x12,
   .ldr sz .x14 .x0 0, .ldr sz .x15 .x1 0, .logic .eor sz .x14 .x14 .x15,
   .str sz .x13 .x2 0, .str sz .x13 .x3 0,
   .add .x .x2 .x2 .x12, .add .x .x3 .x3 .x12, .str sz .x14 .x2 0, .str sz .x14 .x3 0]

/-- The next keystream bytes and plaintext share no storage. Write the XOR
to both the caller and the padded GHASH input at the same time. -/
def shortPieceWith (input : List Instr) : Prog isa :=
  let step := fun n => [ptr .x0 .x0 n, ptr .x1 .x1 n, ptr .x2 .x2 n, ptr .x3 .x3 n]
  let blocks := [.ldrq .v0 .x0 0, .ldrq .v1 .x1 0, .vop (.logic .eor .v0 .v0 .v1),
    .strq .v0 .x2 0, .strq .v0 .x3 0] ++ step 16 ++ [.subImm .x .x13 .x13 1]
  let bytes := [.ldrb .x14 .x0 0, .ldrb .x15 .x1 0, .logic .eor .w .x14 .x14 .x15,
    .strb .x14 .x2 0, .strb .x14 .x3 0] ++ step 1 ++ [.subImm .x .x12 .x12 1]
  let overlap := fun sz n => .block (xorEnds sz n ++ step n)
  let tail := .seq (.block [.lsr .x .x14 .x12 3]) <|
    .ite (.nonzero .x .x14) (overlap .x 8) <|
    .seq (.block [.lsr .x .x14 .x12 2]) <|
    .ite (.nonzero .x .x14) (overlap .w 4) (.loop (.block bytes) (.nonzero .x .x12))
  .seq (.block (input ++ [.lsr .x .x13 .x12 4, imm .x14 15, .logic .and .x .x12 .x12 .x14])) <|
  .seq (.ite (.zero .x .x13) (.block []) (.loop (.block blocks) (.nonzero .x .x13))) <|
    .ite (.zero .x .x12) (.block []) tail

/-- The next descriptor supplies the source pointer and length. -/
def shortPiece : Prog isa :=
  shortPieceWith [.ldr .x .x0 .x6 0, .ldr .x .x12 .x6 8, ptr .x6 .x6 16]

open Gcm.AArch64.Pmull in
/-- Hash exactly eight blocks with the ordinary GHASH register convention. -/
def hashEight : List Instr := prologueT ++ powersS ++ body 8

/-- The accumulator initially holds zero. The hash ends in the register
used by the final tag operation. -/
def shortHashWith (base : Nat) (core : List Instr) : List Instr :=
  [ptr .x0 .x21 240, ptr .x1 .x19 (base+128), .vop (.movi0 .v0), .strq .v0 .x1 0,
   ptr .x2 .x19 base, imm .x3 8] ++ core ++ [.vop (.logic .orr .v16 .v0 .v0)]

abbrev shortHash (base : Nat) := shortHashWith base hashEight

/-- Fold eight authentication blocks with the powers supplied by the key. -/
abbrev hashEightWith := VG.Impl.Gcm.AArch64.Pmull.prologueW ++ VG.Impl.Gcm.AArch64.Pmull.body 8

/-- Process the descriptors after the nonce and AAD have been absorbed. -/
def text (c : Callees) (stitch : Bool) : Prog isa :=
  .seq (.block [.ldr .x .x27 .x19 descO, .ldr .x .x28 .x19 countO,
      .ldr .x .x26 .x19 dataO, .str .x .x26 .x19 hashO, imm .x25 0]) (pieces c stitch)

/-- The general nonce and AAD path. -/
def general (c : Callees) (stitch : Bool) : Prog isa :=
  .seq (j0 c) <| .seq (oneAad c) <|
  .seq (.block [.ldr .x .x25 .x19 alenO, imm .x9 15, .logic .and .x .x25 .x25 .x9]) <|
  .seq (flush c 16) <| .seq (text c stitch) <|
  .seq (.block [.ldr .x .x23 .x19 hashO, .sub .x .x24 .x26 .x23]) <|
  .seq (absorbAl c 16) <|
  .seq (.block [mov .x25 .x24]) <| .seq (flush c 16) <|
  .seq (.block finPrep) <| .seq (tag c 0) <|
  .block ([.ldr .x .x28 .x19 tlO] ++ tagOut ++ restore)

/-- Stack arguments: destination, total length, tag and workspace. -/
def body (c : Callees) (stitch : Bool) : Prog isa :=
  let entry : Prog isa :=
  .block (oneEntry 24 ++ [.str .x .x6 .x19 descO, .str .x .x7 .x19 countO,
      .ldrSp .x9 0, .str .x .x9 .x19 dataO, .ldrSp .x9 8, .str .x .x9 .x19 lenO] ++ stashArg 16)
  .seq entry (general c stitch)

/-! The short frame keeps seven keystream blocks at 0–111, saved registers
at 128–215, and eight hash blocks followed by the zero accumulator at 224–367. -/

def shortWork := 368
def streamO := 0
def authO := 224

/-- Save the caller and initialize the pointers and padded length. -/
def shortSetupAt (lengthOffset : Nat) : List Instr :=
  [.addSp .x9 0] ++ save .x9 ++
  [mov .x19 .x9, mov .x21 .x0, mov .x22 .x1, mov .x23 .x2, mov .x24 .x5,
   .ldrSp .x26 lengthOffset, .addImm .x .x25 .x26 15, .lsr .x .x25 .x25 4, .lsl .x .x25 .x25 4]

abbrev shortSetup := shortSetupAt (shortWork+8)

/-- Clear the eight input blocks for GHASH before filling the record. -/
def shortZero : List Instr :=
  .vop (.movi0 .v0) :: (List.range 8).map (fun i => .strq .v0 .x19 (authO+16*i))

def shortAad : Prog isa :=
  .seq (.block (Stitch.atP .x11 authO 0 ++ [mov .x12 .x4, mov .x13 .x24])) copy

def shortPointers : List Instr :=
  [ptr .x1 .x19 (streamO+16), .ldrSp .x2 shortWork] ++ Stitch.atP .x3 authO 1

def shortLoop : Prog isa :=
  .ite (.zero .x .x7) (.block []) (.loop (.seq shortPiece
    (.block [.subImm .x .x7 .x7 1])) (.nonzero .x .x7))

def shortLengths := Stitch.lengthsAt (authO + 112)

/-- XOR the GHASH result with the encrypted initial counter and store the tag. -/
def writeTag (maskOffset tagArgOffset : Nat) : List Instr :=
  [.ldrq .v0 .x19 maskOffset, .vop (.logic .eor .v16 .v16 .v0),
    .ldrSp .x10 tagArgOffset, .strq .v16 .x10 0]

def shortTagAt (offset : Nat) : List Instr :=
  .vop (.rev .rev64b .v16 .v16) :: writeTag streamO offset

abbrev shortTagOut := shortTagAt (shortWork+16)

def shortBody : Prog isa :=
  .seq (.block shortSetup) <| .seq (.block shortZero) <| .seq shortAad <|
  .seq (Gcm.AArch64.Stitch.byRounds (shortKeys streamO)) <| .seq (.block shortPointers) <|
  .seq shortLoop <| .block (shortLengths ++ shortHash authO ++ shortTagOut ++ restore)

/-- Leaf for a standard nonce, a single AAD block and at most six text blocks. -/
def shortLeaf : Prog isa :=
  Impl.Scrub.AArch64.scrubAll shortWork 0 Fn.own (.frame (.alloc shortWork) shortBody (.free shortWork))

/-- Select short records using the nonce, AAD and text lengths at entry. -/
def recordGuard (limit : Nat) : List Instr :=
  [.ldrSp .x12 8, .subImm .x .x10 .x3 12, imm .x9 17, .subs .x .x11 .x5 .x9,
    .csel .x .x10 .x9 .x10, imm .x9 (limit+1), .subs .x .x11 .x12 .x9,
    .csel .x .x10 .x9 .x10]

abbrev shortGuard := recordGuard 96

/-- Check all three public lengths before allocating either path's frame. -/
def chooseRecord (limit : Nat) (leaf other : Prog isa) : Prog isa :=
  .seq (.block (recordGuard limit)) (.ite (.zero .x .x10) leaf other)

abbrev chooseShort := chooseRecord 96 shortLeaf

/-- Seal the gathered plaintext directly with the chosen CTR and GHASH implementations. -/
def framed (v : Calls) : Prog isa :=
  Impl.StackScratch.AArch64.withStackArgScratch (v.pwWn+32) 3 (body v.callees v.stitch)

def longSeal (v : Calls) : Prog isa :=
  Impl.Scrub.AArch64.scrubAll (v.pwWn+32) 0 Fn.own (framed v)

end VG.Impl.AesGcm.AArch64.DirectGather
