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
abbrev counterWord : VReg := .v11
abbrev counterMask : VReg := .v18

def byteMask : BitVec 128 := 0x07060504030201000f0e0d0c0b0a0908

def mov (d n : Reg) : Instr := .logic .or d n n

def counterControl : BitVec 128 := 0x000102030405060708090a0b14151617

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

def regs : List VReg := batchRegs 8

/-- Insert the low 32 bits of the integer counter into the original
counter prefix. `vperm` selects only defined bytes of `mtvsrd`. -/
def counter (v : VReg) : List Instr :=
  [.mtvsrd counterWord .r8, .vop (.perm v counterBase counterWord counterMask), .addi .r8 .r8 1]

/-- The data pointer is advanced here; CTR's counter pointer stays fixed. -/
def readBlock (ctr : Bool) (v : VReg) : List Instr :=
  if ctr then counter v else load v .r6 ++ [.addi .r6 .r6 16]

def storeAdvance (v : VReg) : List Instr := store v .r6 ++ [.addi .r6 .r6 16]

def writeBlock (ctr : Bool) (v : VReg) : List Instr :=
  (if ctr then load data .r6 ++ [.vop (.logic .xor v v data)] else []) ++ storeAdvance v

def group (inverse ctr : Bool) (count : Nat) : Prog isa :=
  let rs := batchRegs count
  .seq (.block (rs.flatMap (readBlock ctr) ++
      (if ctr then [] else [.subi .r6 .r6 (16 * rs.length)])))
    (.seq (aes inverse rs)
      (.block (rs.flatMap (writeBlock ctr) ++ [.subi .r7 .r7 rs.length])))

def batches (inverse ctr : Bool) : Prog isa :=
  .seq (.block [.lsr .d .r12 .r7 3])
    (.seq (.ite (.zero .d .r12) (.block [])
        (.loop (.seq (group inverse ctr 8) (.block [.lsr .d .r12 .r7 3])) (.nonzero .d .r12)))
      (.ite (.zero .d .r7) (.block []) (.loop (group inverse ctr 1) (.nonzero .d .r7))))

def blocks (inverse : Bool) : Prog isa :=
  .ite (.zero .d .r6) (.block [])
    (.seq (.block ([mov .r7 .r6, mov .r6 .r5] ++ setup)) (batches inverse false))

def encryptBlocks : Prog isa := blocks false

def decryptBlocks : Prog isa := blocks true

def ctr32 : Prog isa :=
  .ite (.zero .d .r7) (.block [])
    (.seq (.block (setup ++ setMask counterMask counterControl ++
      [.li .r11 12, .loadRev .w .r8 .r5 .r11] ++ load counterBase .r5))
      (.seq (batches false true) (.block [.storeRev .w .r8 .r5 .r11])))

end VG.Impl.Aes.PPC64LE.Crypto
