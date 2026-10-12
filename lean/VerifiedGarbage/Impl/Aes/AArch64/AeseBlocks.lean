module

public import VerifiedGarbage.Impl.Aes.AArch64.Aese

/-!
# AES with the Armv8 Cryptographic Extension: encryption and decryption of whole blocks

`vg_aes_encrypt_blocks_aes(schedule = x0, rounds = x1, data = x2, n = x3, scratch = x4)`
and `vg_aes_decrypt_blocks_aes`, with the contracts of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` (`Spec/Aes/Contract.lean`),
for CPUs with FEAT_AES.

As `vg_aes_ctr32_aes` (`Aese.lean`) does: the round keys stay in `v16`–`v30`,
`x6 = rounds − 10` and `x7 = rounds − 12` choose the rounds that depend on the
key size, and the blocks go eight at a time (`v0`–`v7`), each round applied to
all eight, then one at a time; here each group of blocks is loaded from the
data and stored back in place.

Decryption runs FIPS 197's equivalent inverse cipher (§5.3.5): `aesd b, k` is
`InvSubBytes(InvShiftRows(b ⊕ k))` and `aesimc b, b` is `InvMixColumns(b)`, so
a middle round is `aesd` with `InvMixColumns` of the round key (the previous
round's `AddRoundKey`, moved through the linear `InvMixColumns`), then
`aesimc`. The round keys are loaded as for encryption, `k₀ … k₁₂` in
`v16`–`v28` and `k₁₃` in `v29`, and those of the middle rounds (`k₁ … k₁₃`)
replaced with their `InvMixColumns` (`aesimc`); `k_Nr` is in `v30`. A block
is `aesd` with `k_Nr`, `aesimc`, the middle rounds from round key `Nr − 1`
down to 2 (those above 9 chosen by `x6` and `x7`), then `aesd` with round key
1 and `eor` with `k₀`.

Neither uses `scratch` or writes a callee-saved register. Every branch and
every address depends only on the pointers, `rounds` and `n`.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64.Aese

open VG.AArch64

/-- Load the round keys `k₀ … k₁₂` into `v16`–`v28`, and set `x9` to the
last one, `x6 = rounds − 10`, `x7 = rounds − 12` and `x13 = n / 8`. -/
def keysCommon : List Instr :=
  (List.range 13).map (fun j => .ldrq (kreg j) .x0 (16 * j)) ++
  ([.lsl .x .x9 .x1 4, .add .x .x9 .x0 .x9, .ldrq .v30 .x9 0, .subImm .x .x6 .x1 10,
   .subImm .x .x7 .x1 12, .lsr .x .x13 .x3 3] : List Instr)

/-- The round keys for encryption: also `k_{Nr−1}` in `v29`. -/
def encSetup : List Instr := keysCommon ++ ([.subImm .x .x9 .x9 16, .ldrq .v29 .x9 0] : List Instr)

/-- The register of round key `j` (`1 ≤ j ≤ 13`) for decryption, through
`InvMixColumns`. -/
def dreg (j : Nat) : VReg := if j = 13 then .v29 else kreg j

/-- The round keys for decryption: `k₁₃` in `v29`, and `k₁ … k₁₃` through
`InvMixColumns`. -/
def decSetup : List Instr :=
  keysCommon ++ ([.ldrq .v29 .x0 208] : List Instr) ++
  (List.range 13).map fun j => .vop (.aesimc (dreg (j + 1)) (dreg (j + 1)))

/-- A middle round of the inverse cipher with the round key in `k`, of each
block register. -/
def drnd (regs : List VReg) (k : VReg) : List Instr :=
  regs.flatMap fun b => [.vop (.aesd b k), .vop (.aesimc b b)]

/-- The last round of the inverse cipher (`aesd` with round key 1, then
`AddRoundKey` with `k₀`). -/
def dlast (regs : List VReg) : List Instr :=
  regs.flatMap fun b => [.vop (.aesd b .v17), .vop (.logic .eor b b .v16)]

/-- The inverse cipher of each block register: `aesd` with `k_Nr` and the
middle rounds with round keys `Nr − 1 … 2` (`13 … 10` only for the larger
keys), then the last. -/
def aesDec (regs : List VReg) : Prog isa :=
  .seq (.block (drnd regs .v30))
    (.seq (.ite (.zero .x .x6) (.block [])
        (.seq (.ite (.zero .x .x7) (.block []) (.block (drnd regs .v29 ++ drnd regs .v28)))
          (.block (drnd regs .v27 ++ drnd regs .v26))))
      (.block ((List.range 8).flatMap (fun j => drnd regs (kreg (9 - j))) ++ dlast regs)))

/-- Load the data blocks `x2 + 16 (j + i)` into the registers. -/
def ldData : List VReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => .ldrq b .x2 (16 * j) :: ldData bs (j + 1)

/-- Store the registers to the data blocks `x2 + 16 (j + i)`. -/
def stData : List VReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => .strq b .x2 (16 * j) :: stData bs (j + 1)

/-- Eight blocks through `f`; `x13 = n / 8` for the blocks left. -/
def blk8 (f : List VReg → Prog isa) : Prog isa :=
  .seq (.block (ldData regs8 0))
    (.seq (f regs8)
      (.block (stData regs8 0 ++ ([.addImm .x .x2 .x2 128, .subImm .x .x3 .x3 8, .lsr .x .x13 .x3 3] : List Instr))))

/-- One block through `f`. -/
def blk1 (f : List VReg → Prog isa) : Prog isa :=
  .seq (.block (ldData [.v0] 0))
    (.seq (f [.v0]) (.block (stData [.v0] 0 ++ ([.addImm .x .x2 .x2 16, .subImm .x .x3 .x3 1] : List Instr))))

/-- The blocks, eight and then one at a time, after `setup`. -/
def blocks (setup : List Instr) (f : List VReg → Prog isa) : Prog isa :=
  .seq (.block setup)
    (.seq (.ite (.zero .x .x13) (.block []) (.loop (blk8 f) (.nonzero .x .x13)))
      (.ite (.zero .x .x3) (.block []) (.loop (blk1 f) (.nonzero .x .x3))))

def encryptBlocks : Prog isa := blocks encSetup aes
def decryptBlocks : Prog isa := blocks decSetup aesDec

end VG.Impl.Aes.AArch64.Aese
