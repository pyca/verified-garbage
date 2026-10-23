module

public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.ExpandKey

/-!
# Streaming TDEA-CMAC on PPC64LE

The streaming functions over the verified Triple DES key expansion
(`vg_triple_des_expand_key`) and block encryption
(`vg_triple_des_encrypt_block`), which they call, with the streaming state's
layout of `Spec.Cmac.tdesRepr`: the key schedule at 0, the subkeys at 384
and 392, the chaining value at 400 and the bytes held back at 408.

* `streamInit(state = r3, key = r4, key_len = r5, scratch = r6)` expands the
  key into the state, enciphers the zero block, derives the subkeys from it
  (`dbl` as a shift, and an XOR with `0x1b` under a mask made from the top
  bit) and zeroes the chaining value.
* `absorb(state = r3, count = r4, data = r5, len = r6, scratch = r7)`
  computes the number of bytes held back from `count`; if the data fit after
  them, copies them there; otherwise it completes the block held back,
  chains it, chains the data's whole blocks but its last 1 to 8 bytes, and
  holds those back.
* `finish(state = r3, count = r4, out = r5, scratch = r6)` XORs the chaining
  value with `K1` and the block held back if it is complete, else with `K2`
  and the bytes held back padded, enciphers it, and writes it to `out`.

The scratch buffer (`sb`, in `r5` while the block function is called):
the block function's working space (bytes 0 to 511), the block it enciphers
(`bufOff`), the padded last block (`padOff`), and the return address and
the caller's `r29`–`r31`. The analysis of constant time takes memory for
secret, so what the functions count across the block function's calls is in
`r29`–`r31`, which the block function never writes: the data pointer, the
blocks left and the bytes to hold back after them. Only the pointers,
`count`, `len` and `key_len` are public.
-/

@[expose] public section

namespace VG.Impl.CmacTripleDes.Stream.PPC64LE

open VG.PPC64LE

/-- `mr d, n` (`or d, n, n`). -/
def mr (d n : Reg) : Instr := .logic .or d n n

/-- The offsets in the scratch buffer. -/
def bufOff : Nat := 512
def padOff : Nat := 520
def lrOff : Nat := 528
def r29Off : Nat := 536
def r30Off : Nat := 544
def r31Off : Nat := 552

/-- A call of the block function, with the schedule at `r3`, the block at
`r4` and its working space at `r5`. -/
def encCall : Prog isa := .call "vg_triple_des_encrypt_block" Impl.TripleDes.PPC64LE.encryptBlock

/-- A call of the key expansion, with the key at `r3`, its length in `r4` and
the schedule's address in `r5`. -/
def keyCall : Prog isa := .call "vg_triple_des_expand_key" Impl.TripleDes.PPC64LE.Key.expandKey

/-- `r7 := dbl64 r7`, through `r8`–`r10`, with `r6 = 0`. -/
def dblCode : List Instr :=
  [.lsr .d .r8 .r7 63, .sub .r9 .r6 .r8, .li .r10 0x1b, .logic .and .r9 .r9 .r10, .lsl .r7 .r7 1,
   .logic .xor .r7 .r7 .r9]

/-- Copies the `r12` bytes at `r10` to `r11`, through `r0`, advancing `r10`
and `r11` past them. -/
def copyLoop : Prog isa :=
  .ite (.zero .d .r12) (.block [])
    (.loop (.block [.lbz .r0 .r10 0, .stb .r0 .r11 0, .addi .r10 .r10 1, .addi .r11 .r11 1,
      .subi .r12 .r12 1]) (.nonzero .d .r12))

/-- The number of bytes held back for a message of `r4` bytes, to `r8`
(through `r9`): none for the empty message, else 1 to 8. -/
def heldCode : Prog isa :=
  .ite (.zero .d .r4) (.block [.li .r8 0])
    (.block [.subi .r8 .r4 1, .li .r9 7, .logic .and .r8 .r8 .r9, .addi .r8 .r8 1])

/-! ## `stream_init` -/

def initSave : List Instr :=
  [.mflr .r0, .store .d .r0 .r6 lrOff, .store .d .r30 .r6 r30Off, .store .d .r31 .r6 r31Off,
   mr .r31 .r3, mr .r30 .r6, mr .r3 .r4, mr .r4 .r5, mr .r5 .r31]

/-- The zero block to the buffer, and the block function's arguments. -/
def initZero : List Instr :=
  [mr .r3 .r31, mr .r5 .r30, .addi .r4 .r30 bufOff, .li .r0 0, .store .d .r0 .r4 0]

/-- The subkeys from `L` (in the buffer, at `r4`), and the chaining value
zeroed. -/
def initSubkeys : List Instr :=
  [.li .r6 0, .loadRev .d .r7 .r4 .r6] ++ dblCode ++ [.li .r11 384, .storeRev .d .r7 .r3 .r11] ++
    dblCode ++ [.li .r11 392, .storeRev .d .r7 .r3 .r11, .li .r0 0, .store .d .r0 .r3 400]

def initRestore : List Instr :=
  [.load .d .r0 .r30 lrOff, .load .d .r31 .r30 r31Off, .load .d .r30 .r30 r30Off, .mtlr .r0]

def streamInit : Prog isa :=
  .seq (.block initSave) (.seq keyCall (.seq (.block initZero)
    (.seq encCall (.block (initSubkeys ++ initRestore)))))

/-! ## `absorb` -/

def absorbSave : List Instr :=
  [.mflr .r0, .store .d .r0 .r7 lrOff, .store .d .r29 .r7 r29Off, .store .d .r30 .r7 r30Off,
   .store .d .r31 .r7 r31Off, mr .r29 .r5, mr .r5 .r7]

/-- The room left in the block held back to `r9`, and to `r10` whether the
data do not fit in it: `len ≥ 16`, or `8 - held < len`. -/
def absorbFlag : List Instr :=
  [.li .r9 8, .sub .r9 .r9 .r8, .lsr .d .r10 .r6 4, .sub .r11 .r9 .r6, .lsr .d .r11 .r11 63,
   .logic .or .r10 .r10 .r11]

/-- The copy's arguments: `n` bytes from the data to the bytes held back. -/
def toHeld (n : Reg) : List Instr := [.addi .r11 .r3 408, .add .r11 .r11 .r8, mr .r10 .r29, mr .r12 n]

/-- After the block held back is complete: the data pointer past the bytes
that completed it to `r29`, the whole blocks to chain to `r30`, the bytes
to hold back after them to `r31`, and the block held back XORed into the
chaining value, in the buffer, at `r4`. -/
def chainSetup : List Instr :=
  [mr .r29 .r10, .sub .r30 .r6 .r9, .subi .r30 .r30 1, .lsr .d .r30 .r30 3, .sub .r31 .r6 .r9,
   .lsl .r12 .r30 3, .sub .r31 .r31 .r12, .load .d .r7 .r3 400, .load .d .r9 .r3 408,
   .logic .xor .r7 .r7 .r9, .store .d .r7 .r5 bufOff, .addi .r4 .r5 bufOff]

/-- One whole block of data XORed into the buffer, enciphered. -/
def chainBody : Prog isa :=
  .seq (.block [.load .d .r7 .r5 bufOff, .load .d .r9 .r29 0, .logic .xor .r7 .r7 .r9,
    .store .d .r7 .r5 bufOff, .addi .r29 .r29 8, .subi .r30 .r30 1]) encCall

def chainLoop : Prog isa := .ite (.zero .d .r30) (.block []) (.loop chainBody (.nonzero .d .r30))

/-- The chaining value back to the state, and the copy's arguments for the
bytes to hold back. -/
def chainDone : List Instr :=
  [.load .d .r7 .r5 bufOff, .store .d .r7 .r3 400, .addi .r11 .r3 408, mr .r10 .r29, mr .r12 .r31]

def chainPath : Prog isa :=
  .seq (.block (toHeld .r9)) (.seq copyLoop (.seq (.block chainSetup) (.seq encCall
    (.seq chainLoop (.seq (.block chainDone) copyLoop)))))

def fillPath : Prog isa := .seq (.block (toHeld .r6)) copyLoop

def absorbRestore : List Instr :=
  [.load .d .r0 .r5 lrOff, .load .d .r29 .r5 r29Off, .load .d .r30 .r5 r30Off,
   .load .d .r31 .r5 r31Off, .mtlr .r0]

def absorb : Prog isa :=
  .seq (.block absorbSave) (.seq heldCode (.seq (.block absorbFlag)
    (.seq (.ite (.nonzero .d .r10) chainPath fillPath) (.block absorbRestore))))

/-! ## `finish` -/

def finishSave : List Instr :=
  [.mflr .r0, .store .d .r0 .r6 lrOff, .store .d .r31 .r6 r31Off, mr .r31 .r5, mr .r5 .r6]

/-- The last block, complete: the chaining value XORed with it and `K1`, to
the buffer. -/
def complete : List Instr :=
  [.load .d .r7 .r3 408, .load .d .r9 .r3 384, .logic .xor .r7 .r7 .r9, .load .d .r9 .r3 400,
   .logic .xor .r7 .r7 .r9, .store .d .r7 .r5 bufOff]

/-- The padded block zeroed, and the copy's arguments for the bytes held
back. -/
def padStart : List Instr :=
  [.li .r0 0, .store .d .r0 .r5 padOff, .addi .r10 .r3 408, .addi .r11 .r5 padOff, mr .r12 .r8]

/-- The padding's first byte after the bytes held back (at `r11`), and the
chaining value XORed with the padded block and `K2`, to the buffer. -/
def padDone : List Instr :=
  [.li .r9 0x80, .stb .r9 .r11 0, .load .d .r7 .r5 padOff, .load .d .r9 .r3 392,
   .logic .xor .r7 .r7 .r9, .load .d .r9 .r3 400, .logic .xor .r7 .r7 .r9, .store .d .r7 .r5 bufOff]

def padded : Prog isa := .seq (.block padStart) (.seq copyLoop (.block padDone))

def finishOut : List Instr :=
  [.load .d .r7 .r5 bufOff, .store .d .r7 .r31 0, .load .d .r0 .r5 lrOff,
   .load .d .r31 .r5 r31Off, .mtlr .r0]

def finish : Prog isa :=
  .seq (.block finishSave) (.seq heldCode (.seq (.block [.subi .r9 .r8 8])
    (.seq (.ite (.zero .d .r9) (.block complete) padded)
      (.seq (.block [.addi .r4 .r5 bufOff]) (.seq encCall (.block finishOut))))))

end VG.Impl.CmacTripleDes.Stream.PPC64LE
