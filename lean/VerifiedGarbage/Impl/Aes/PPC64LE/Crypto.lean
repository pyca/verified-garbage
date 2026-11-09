module

public import VerifiedGarbage.Impl.Vector.PPC64LE

/-! # POWER8 AES

Eight independent blocks share each loaded round key. The middle rounds
run in a loop, then `vcipherlast` or `vncipherlast` performs the final
round. A one-block loop handles the tail. All registers are volatile and
the scratch argument is unused.
-/

@[expose] public section
namespace VG.Impl.Aes.PPC64LE.Crypto
open VG.PPC64LE

abbrev key : VReg := .v8
abbrev data : VReg := .v9
abbrev mask : VReg := .v19
abbrev counterBase : VReg := .v10
abbrev counterStep : VReg := .v11

def byteMask : BitVec 128 := 0x07060504030201000f0e0d0c0b0a0908

def mov (d n : Reg) : Instr := .logic .or d n n

/-- One in the last word: `vadduwm` by it adds one to the counter, the
last 32 bits of the block, modulo 2³². -/
def counterOne : BitVec 128 := 1

def setMask (d : VReg) (x : BitVec 128) : List Instr :=
  Impl.Vector.PPC64LE.const64 .r11 (x.extractLsb' 64 64) ++
  Impl.Vector.PPC64LE.const64 .r12 (x.extractLsb' 0 64) ++
  Impl.Vector.PPC64LE.pair d .v1 .v0 .r11 .r12

def setup : List Instr :=
  [.li .r0 0, .vop (.logic .xor .v0 .v0 .v0)] ++ setMask mask byteMask

/-- Register byte zero is memory byte zero, as the AES instructions require. -/
def load (v : VReg) (p : Reg) : List Instr :=
  Impl.Vector.PPC64LE.loadPerm v p mask

def storePerm (d n : VReg) (p offset : Reg) : List Instr :=
  [.vop (.perm d n n mask), .stxvd2x d p offset]

def store (v : VReg) (p : Reg) : List Instr := storePerm v v p .r0

def xorKey (rs : List VReg) : List Instr := rs.map fun v => .vop (.logic .xor v v key)

def cipherRegs (inverse last : Bool) (k : VReg) (rs : List VReg) : List Instr :=
  rs.map fun v => .vop (.cipher inverse last v v k)

def round (inverse last : Bool) (rs : List VReg) : List Instr :=
  load key .r9 ++ cipherRegs inverse last key rs

def keyStep (inverse : Bool) : Instr :=
  if inverse then .subi .r9 .r9 16 else .addi .r9 .r9 16

def keyStart (inverse : Bool) : List Instr :=
  if inverse then [.lsl .r9 .r4 4, .add .r9 .r3 .r9] else [mov .r9 .r3]

def middleBody (inverse : Bool) (rs : List VReg) : List Instr :=
  round inverse false rs ++ [keyStep inverse, .subi .r10 .r10 1]

def initialBody (inverse : Bool) (rs : List VReg) : List Instr :=
  keyStart inverse ++ load key .r9 ++ xorKey rs ++ [keyStep inverse, .subi .r10 .r4 1]

/-- AES on the state registers, with the forward schedule at `r3`, `Nr` in
`r4`, and the byte-order mask already in `mask`. -/
def aes (inverse : Bool) (rs : List VReg) : Prog isa :=
  .seq (.block (initialBody inverse rs))
    (.seq (.loop (.block (middleBody inverse rs)) (.nonzero .d .r10))
      (.block (round inverse true rs)))

/-- The same eight registers are used by encryption, decryption and CTR. -/
def breg : Nat → VReg
  | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3
  | 4 => .v4 | 5 => .v5 | 6 => .v6 | _ => .v7

def batchRegs (n : Nat) : List VReg := (List.range n).map breg

/-- The counter block, and the counter block's last word plus one
(`vadduwm`, which adds modulo 2³² in each word). -/
def counter (v : VReg) : List Instr :=
  [.vop (.logic .or v counterBase counterBase), .vop (.add false counterBase counterBase counterStep)]

/-- The data pointer is advanced here; CTR's counter pointer stays fixed. -/
def readBlock (ctr : Bool) (v : VReg) : List Instr :=
  if ctr then counter v else load v .r6 ++ [.addi .r6 .r6 16]

/-- The block stored at `r6 + o` (`o` is `r0`, zero, in place; it holds
`dst - src` out of place), and `r6` advanced. -/
def storeAdvance (v : VReg) (o : Reg := .r0) : List Instr := storePerm v v .r6 o ++ [.addi .r6 .r6 16]

/-- CTR XORs the keystream into the data in `lxvd2x`'s order, after the
store's `vperm`: one `vperm` for the block, not one for the data and one for
the result. -/
def writeBlock (ctr : Bool) (v : VReg) (o : Reg := .r0) : List Instr :=
  if ctr then [.lxvd2x data .r6 .r0, .vop (.perm v v v mask), .vop (.logic .xor v v data), .stxvd2x v .r6 o,
    .addi .r6 .r6 16]
  else storeAdvance v o

def group (inverse ctr : Bool) (count : Nat) (o : Reg := .r0) : Prog isa :=
  let rs := batchRegs count
  .seq (.block (rs.flatMap (readBlock ctr) ++
      (if ctr then [] else [.subi .r6 .r6 (16 * rs.length)])))
    (.seq (aes inverse rs)
      (.block (rs.flatMap (fun v => writeBlock ctr v o) ++ [.subi .r7 .r7 rs.length])))

/-- `c` (1, 2 or 4) blocks if bit `c` of the number left, `r7`, is set. -/
def tailStep (inverse ctr : Bool) (c : Nat) (o : Reg := .r0) : Prog isa :=
  .seq (.block [.li .r12 c, .logic .and .r12 .r7 .r12])
    (.ite (.zero .d .r12) (.block []) (group inverse ctr c o))

/-- The data loops, storing each block at `r6 + o` (in place with `o = r0`):
eight blocks at a time, then the rest (fewer than eight) by four, two and
one, by the bits of their number. -/
def batches (inverse ctr : Bool) (o : Reg := .r0) : Prog isa :=
  .seq (.block [.lsr .d .r12 .r7 3])
    (.seq (.ite (.zero .d .r12) (.block [])
        (.loop (.seq (group inverse ctr 8 o) (.block [.lsr .d .r12 .r7 3])) (.nonzero .d .r12)))
      (.seq (tailStep inverse ctr 4 o) (.seq (tailStep inverse ctr 2 o) (tailStep inverse ctr 1 o))))

def blocks (inverse : Bool) : Prog isa :=
  .ite (.zero .d .r6) (.block [])
    (.seq (.block ([mov .r7 .r6, mov .r6 .r5] ++ setup)) (batches inverse false))

def encryptBlocks : Prog isa := blocks false

def decryptBlocks : Prog isa := blocks true

/-- The byte-order mask, `counterOne` in `counterStep` and the counter
block in `counterBase`. -/
def ctrSetup : List Instr :=
  setup ++ setMask counterStep counterOne ++ load counterBase .r5

/-- `vg_aes_ctr32(schedule = r3, rounds = r4, counter = r5, data = r6, n = r7,
scratch = r8)`: counter mode on the `n` blocks at `r6`, in place, and the
counter block, `n` further on, stored back. -/
def ctr32 : Prog isa :=
  .ite (.zero .d .r7) (.block [])
    (.seq (.block ctrSetup) (.seq (batches false true) (.block (store counterBase .r5))))

end VG.Impl.Aes.PPC64LE.Crypto
