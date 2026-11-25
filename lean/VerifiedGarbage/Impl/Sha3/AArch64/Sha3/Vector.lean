module

public import VerifiedGarbage.Impl.Sha3.AArch64.Lanes
public import VerifiedGarbage.Impl.Sha3.AArch64.RoundConstants
public import VerifiedGarbage.Impl.Sha3.AArch64.Callee

/-!
# Keccak-f[1600] on AArch64: two rounds in vector registers (FEAT_SHA3)

Lane `i` is in `v<i>` (both doublewords, each of its own state), in place as
`Lanes.lean` describes. XAR does θ's XOR and ρ's rotation at once, and writes
any register, so the two lanes of a row that break its cycle move for free.

`es` of the column parities and `bs` of the 25 χ steps are done with two
instructions of the base AdvSIMD rather than one of FEAT_SHA3: cores that
run FEAT_SHA3's on only some of their vector units are faster so.
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Sha3.Vector

open VG.AArch64
open VG.Impl.Sha3 (rhoOff)
open VG.Impl.Sha3.AArch64.Lanes

/-- `v<i>`. -/
def vreg (i : Nat) : VReg :=
  [VReg.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15,
    .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31].getD i .v0

/-- Lane `i`'s register before round `r`. -/
def reg (r i : Nat) : VReg := vreg (home r i)

/-- The parity of column `x`, in `v<25 + x>`. -/
def parity (es r x : Nat) : List Instr :=
  let a (y : Nat) : VReg := reg r (x + 5 * y)
  if x < es then
    [.vop (.logic .eor (vreg (25 + x)) (a 0) (a 1)), .vop (.logic .eor (vreg (25 + x)) (vreg (25 + x)) (a 2)),
      .vop (.logic .eor (vreg (25 + x)) (vreg (25 + x)) (a 3)), .vop (.logic .eor (vreg (25 + x)) (vreg (25 + x)) (a 4))]
  else [.vop (.eor3 (vreg (25 + x)) (a 0) (a 1) (a 2)), .vop (.eor3 (vreg (25 + x)) (vreg (25 + x)) (a 3) (a 4))]

/-- The register of `Dₓ`. -/
def dreg (x : Nat) : VReg := vreg ([30, 25, 26, 27, 28].getD x 30)

/-- The order of the `D`s: each over a parity that is not needed any more. -/
def dcol (x : Nat) : Instr := .vop (.rax1 (dreg x) (vreg (25 + (x + 4) % 5)) (vreg (25 + (x + 1) % 5)))

/-- θ, ρ on lane `i`, from its register to `d`. -/
def xar (r i : Nat) (d : VReg) : Instr := .vop (.xar d (reg r i) (dreg (i % 5)) ((64 - rhoOff i) % 64))

/-- `d = a ⊕ (b ∧ ¬c)`, step `n` of the round's 25 (`t` is a temporary that may be `d`). -/
def step (bs n : Nat) (d t a b c : VReg) : List Instr :=
  if n < bs then [.vop (.logic .bic t b c), .vop (.logic .eor d t a)] else [.vop (.bcax d a b c)]

/-- Row `y`. -/
def row (bs r y : Nat) : List Instr :=
  let b (k : Nat) : VReg :=
    if k % 5 = 1 then .v29 else if k % 5 = 3 then .v31 else reg r (rowSrc y (k % 5))
  let a (k : Nat) : VReg := reg r (rowSrc y k)
  let st (j k : Nat) (d t : VReg) : List Instr := step bs (5 * y + j) d t (b k) (b (k + 2)) (b (k + 1))
  ([xar r (rowSrc y 1) .v29, xar r (rowSrc y 3) .v31] : List Instr) ++
  st 0 3 (a 1) (a 1) ++ st 1 4 (a 3) (a 3) ++ st 2 2 (a 4) .v30 ++ st 3 0 (a 0) .v30 ++ st 4 1 (a 2) .v30

/-- A round but for ι: `r` is 0 or 1, its place in the loop's body. -/
def round (es bs r : Nat) : List Instr :=
  (List.range 5).flatMap (parity es r) ++ [0, 2, 4, 1, 3].map dcol ++
  ([.vop (.logic .eor (reg r 0) (reg r 0) (dreg 0))] : List Instr) ++
  (([0, 2, 4].flatMap fun x => (List.range 5).map fun y => x + 5 * y).filter (· != 0)).map (fun i => xar r i (reg r i)) ++
  (List.range 5).flatMap (row bs r)

/-! ## The rounds, in a loop

The round constants are copied to memory (`rcStore`), each twice, so that a
pointer that advances through them gives each iteration's two rounds theirs.
The permutation of one state, and the rounds that callers run on states they
keep in the vector registers, use FEAT_SHA3's instructions wherever they can. -/

open VG.Impl.Sha3.AArch64.RoundConstants (rcs2 sym2)

/-- The table of round constants, stored at `[b, #off]` (384 bytes). -/
def rcStore (b : Reg) (off : Nat) : List Instr :=
  ([.adrSym .x16 sym2] : List Instr) ++
  (List.range 24).flatMap fun r => [.ldrqTbl .v31 .x16 (16 * r) sym2 rcs2, .strq .v31 b (off + 16 * r)]

/-- ι of round `r` of the loop's body. -/
def iota (r : Nat) : List Instr := [.ldrq .v31 .x16 (16 * r), .vop (.logic .eor .v0 .v0 .v31)]

/-- Two rounds. -/
def body : List Instr := round 0 0 0 ++ iota 0 ++ round 0 0 1 ++ iota 1

/-- The 24 rounds, `b` pointing to the table. -/
def rounds (b : Reg) : Prog isa :=
  .seq (.block [.addImm .x .x16 b 0, .movz .x .x17 12 0])
    (.loop (.block (body ++ ([.addImm .x .x16 .x16 32, .subImm .x .x17 .x17 1] : List Instr))) (.nonzero .x .x17))

/-- ι of round `r`, the constant from the table in the code's constants, whose address is in `x16`. -/
def iotaTbl (r : Nat) : List Instr := [.ldrqTbl .v31 .x16 (16 * r) sym2 rcs2, .vop (.logic .eor .v0 .v0 .v31)]

/-- The 24 rounds, unrolled, for a caller with no memory for the table. -/
def unrolled : List Instr :=
  ([.adrSym .x16 sym2] : List Instr) ++ (List.range 24).flatMap fun r => round 0 0 (r % 2) ++ iotaTbl r

/-! ## The permutation of one state

`permute(state = x0, scratch = x1)`: in doubleword 0 of each register. -/

/-- The vector registers the calling convention preserves, saved at `[b, #off]`. -/
def save (b : Reg) (off : Nat) : List Instr := (List.range 8).map fun i => .strq (vreg (8 + i)) b (off + 16 * i)
def restore (b : Reg) (off : Nat) : List Instr := (List.range 8).map fun i => .ldrq (vreg (8 + i)) b (off + 16 * i)

/-- Load the state at `b`. -/
def load (b : Reg) : List Instr :=
  ((List.range 12).flatMap fun i => [.ldrq (vreg (2 * i)) b (16 * i),
    .vop (.ext (vreg (2 * i + 1)) (vreg (2 * i)) (vreg (2 * i)) 8)]) ++
  ([.ldr .x .x16 b 192, .vop (.dup .d2 .v24 .x16)] : List Instr)

/-- Store it. -/
def store (b : Reg) : List Instr :=
  ((List.range 12).flatMap fun i => [.vop (.perm .zip1 .d2 .v25 (vreg (2 * i)) (vreg (2 * i + 1))),
    .strq .v25 b (16 * i)]) ++
  ([.umov .x .x16 .v24 0, .str .x .x16 b 192] : List Instr)

def permute : Prog isa :=
  .seq (.block (save .x1 384 ++ rcStore .x1 0 ++ load .x0))
    (.seq (rounds .x1) (.block (store .x0 ++ restore .x1 384)))

/-! ## Absorbing blocks

`absorbBlocks(state = x0, rate = x1, data = x2, len = x3, scratch = x4)`
absorbs all of `data`'s whole blocks (at least one), with the state in
registers throughout, and returns the number of bytes left. -/

/-- The 16 bytes of data at `[p, #(16 k)]` XORed into lanes `i` and `i + 1`. -/
def xorPair (p : Reg) (k i : Nat) : List Instr :=
  [.ldrq .v25 p (16 * k), .vop (.logic .eor (vreg i) (vreg i) .v25), .vop (.ext .v25 .v25 .v25 8),
    .vop (.logic .eor (vreg (i + 1)) (vreg (i + 1)) .v25)]

/-- Lane `i` of the data at `x2` XORed into the state. -/
def xorOne (i : Nat) : List Instr :=
  [.ldr .x .x9 .x2 (8 * i), .vop (.dup .d2 .v25 .x9), .vop (.logic .eor (vreg i) (vreg i) .v25)]

/-- Lanes `i`, … of the data at `x2`, `n` pairs of them. -/
def xorPairs (i n : Nat) : List Instr :=
  ([.addImm .x .x10 .x2 (8 * i)] : List Instr) ++ (List.range n).flatMap fun k => xorPair .x10 k (i + 2 * k)

/-- Skip `c` if the rate is `rate`. -/
def unlessRate (rate : Nat) (c : Prog isa) : Prog isa :=
  .seq (.block [.subImm .x .x9 .x1 rate]) (.ite (.zero .x .x9) (.block []) c)

/-- A block of the data at `x2` XORed into the state. -/
def xorBlock : Prog isa :=
  .seq (.block (xorPairs 0 4 ++ xorOne 8))
  (unlessRate 72 (.seq (.block (xorPairs 9 2))
  (unlessRate 104 (.seq (.block (xorPairs 13 2))
  (unlessRate 136 (.seq (.block (xorOne 17))
  (unlessRate 144 (.block (xorPairs 18 1 ++ xorOne 20)))))))))

/-- A block absorbed; then `x9` is zero if another whole block is left. -/
def absorbStep : Prog isa :=
  .seq xorBlock (.seq (rounds .x4)
    (.block [.add .x .x2 .x2 .x1, .sub .x .x3 .x3 .x1, .sub .x .x9 .x3 .x1, .lsr .x .x9 .x9 63]))

def absorbBlocks : Prog isa :=
  .seq (.block (save .x4 384 ++ rcStore .x4 0 ++ load .x0))
    (.seq (.loop absorbStep (.zero .x .x9))
      (.block (store .x0 ++ restore .x4 384 ++ ([.addImm .x .x0 .x3 0] : List Instr))))

/-- The sponge's callee. -/
def callee : Callee where
  name := "vg_keccak_f1600_sha3"
  code := permute
  suffix := "_sha3"
  clear := Callee.sha3Clear
  pairedSha3 := true
  blocks := some ("vg_keccak_absorb_blocks_sha3", absorbBlocks)

end VG.Impl.Sha3.AArch64.Sha3.Vector
