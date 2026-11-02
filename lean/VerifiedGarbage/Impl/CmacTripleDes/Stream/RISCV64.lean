module

public import VerifiedGarbage.Impl.TripleDes.RISCV64.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Ecb
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Words.RISCV64.XorBytes
public import VerifiedGarbage.Impl.Words.RISCV64.Loops
public import VerifiedGarbage.Impl.Cmac.RISCV64

/-!
# Streaming TDEA-CMAC on RISC-V

The streaming functions over the verified Triple DES key expansion
(`vg_triple_des_expand_key`) and ECB encryption (`vg_triple_des_ecb_encrypt`,
on one block in place), which they call, with the streaming state's layout
of `Spec.Cmac.tdesRepr`: the key schedule at 0, the subkeys at 384 and 392,
the chaining value at 400 and the bytes held back at 408. The state is the
schedule ECB reads, and ECB enciphers the chaining value in place in the
state, so the functions need no buffer of their own for a block but the
padded last block of `finish`. The contracts state no alignment for the
data and `out`, so every block is accessed a byte at a time, the state's
too.

* `streamInit(state = a0, key = a1, key_len = a2, scratch = a3)` expands the
  key into the state, zeroes the block of `K1` and enciphers it in place
  (`L`), doubles it there (`K1`) and into the block after it (`K2`), a byte at
  a time (`VG.Impl.Cmac.RISCV64.dbl`), and zeroes the chaining value.
* `absorb(state = a0, count = a1, data = a2, len = a3, scratch = a4)`
  computes the number of bytes held back `h` from `count`; if the data fit
  in the `8 - h` bytes after them, copies them there; otherwise it completes
  the block held back, XORs it into the chaining value and enciphers that,
  then does the same with each whole block of the data but its last 1 to 8
  bytes, which it holds back.
* `finish(state = a0, count = a1, out = a2, scratch = a3)` XORs into the
  chaining value the block held back and `K1` if it is complete, else the
  bytes held back padded (in the scratch buffer) and `K2`, enciphers it, and
  copies it to `out`.

The scratch buffer: from its address rounded up to a multiple of 8
(`savePtr`, since the contracts state no alignment for it), the return
address (which each call replaces) and the callee-saved registers the
functions keep across the calls (48 bytes), and `finish`'s padded block
(`padOff`, a byte at a time). The branches are on whether a
register is zero; the loops count blocks and bytes. Only the pointers,
`count`, `len` and `key_len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.CmacTripleDes.Stream.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.Cmac.RISCV64 (dbl)

/-- `mv d, n`. -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The padded block's offset in the scratch buffer. -/
def padOff : Nat := 64

/-- `t0 :=` the register `n` rounded up to a multiple of 8 (`(n + 7) & -8`),
where the registers are saved. -/
def savePtr (n : Reg) : List Instr := [.addi .t0 n 7, .logicImm .and .t0 .t0 (-8)]

/-- The key expansion's call, with the key at `a0`, its length in `a1` and
the schedule's address in `a2`. -/
def keyCall : Prog isa := .call "vg_triple_des_expand_key" Impl.TripleDes.RISCV64.Key.expandKey

/-- ECB's call, with the schedule at `a0`, the block at `a1` and one block in
`a2`. -/
def ecbCall : Prog isa := .call "vg_triple_des_ecb_encrypt" Impl.TripleDes.RISCV64.Ecb.encrypt

/-- ECB's arguments: the state (`s1`), as the schedule, and its block at
`off`. -/
def ecbArgs (off : Nat) : List Instr := [mov .a0 .s1, .addi .a1 .s1 off, .li .a2 1]

/-- Copies the `cnt` bytes at `src` to `dst`, through `tmp`, if there are
any. -/
def copy (tmp src dst cnt : Reg) : Prog isa :=
  .ite (.zero cnt) (.block []) (copyLoop tmp src dst cnt)

/-- The number of bytes held back for a message of `a1` bytes, to `t0`: none
for the empty message, else 1 to 8. -/
def heldCode : Prog isa :=
  .ite (.zero .a1) (.block [.li .t0 0])
    (.block [.addi .t0 .a1 (-1), .logicImm .and .t0 .t0 7, .addi .t0 .t0 1])

/-- Saves `rs` at their offsets from the scratch buffer at `n`, rounded up. -/
def saveRegs (n : Reg) (rs : List (Reg × Nat)) : List Instr :=
  savePtr n ++ rs.map fun (r, d) => .store .d r .t0 d

/-- Restores `rs` from the scratch buffer at `s2`, rounded up. -/
def restoreRegs (rs : List (Reg × Nat)) : List Instr :=
  savePtr .s2 ++ rs.map fun (r, d) => .load .d r .t0 d

/-! ## `stream_init` -/

def initSaved : List (Reg × Nat) := [(.ra, 0), (.s1, 8), (.s2, 16)]

/-- The registers saved, the state to `s1` and the scratch buffer to `s2`,
and the key expansion's arguments. -/
def initSave : List Instr :=
  saveRegs .a3 initSaved ++ [mov .s1 .a0, mov .s2 .a3, mov .a0 .a1, mov .a1 .a2, mov .a2 .s1]

/-- The block of `K1` zeroed, and ECB's arguments on it. -/
def initZero : List Instr := storeBytes .t0 .s1 384 (List.replicate 8 0) ++ ecbArgs 384

/-- `K1` from `L`, in place, `K2` after it, the chaining value zeroed, and the
registers restored. -/
def initTail : List Instr :=
  dbl 8 0x1b 384 384 ++ dbl 8 0x1b 384 392 ++ storeBytes .t0 .s1 400 (List.replicate 8 0) ++
    restoreRegs initSaved

def streamInit : Prog isa :=
  .seq (.block initSave) (.seq keyCall (.seq (.block initZero) (.seq ecbCall (.block initTail))))

/-! ## `absorb` -/

def absSaved : List (Reg × Nat) := [(.ra, 0), (.s1, 8), (.s2, 16), (.s3, 24), (.s4, 32), (.s5, 40)]

/-- The registers saved, the state to `s1`, the scratch buffer to `s2` and
the data pointer to `s3`. -/
def absSave : List Instr := saveRegs .a4 absSaved ++ [mov .s1 .a0, mov .s2 .a4, mov .s3 .a2]

/-- The room after the bytes held back to `t1`, and to `t2` whether the data
do not fit in it (`8 - h < len`). -/
def absFlag : List Instr := [.li .t1 8, .sub .t1 .t1 .t0, .sltu .t2 .t1 .a3]

/-- The copy's arguments: to the bytes held back, past the `t0` there, from
the data, `n` bytes. -/
def toHeld (n : Reg) : List Instr := [.addi .t3 .s1 408, .add .t3 .t3 .t0, mov .t4 .s3, mov .t5 n]

def fillPath : Prog isa := .seq (.block (toHeld .a3)) (copy .t6 .t4 .t3 .t5)

/-- After the block held back is complete: the data pointer past the bytes
that completed it, the blocks to chain after it to `s5` and the bytes to
hold back after them to `s4`, and the block held back XORed into the
chaining value, with ECB's arguments on it. -/
def chainSetup : List Instr :=
  [.add .s3 .s3 .t1, .addi .t2 .s4 (-1), .shift .srl .d .s5 .t2 3, .shift .sll .d .t2 .s5 3,
   .sub .s4 .s4 .t2, .addi .a0 .s1 400, .addi .a1 .s1 408] ++ xorBytes .t0 .t1 .a0 .a1 8 ++ ecbArgs 400

/-- CBC-MAC (SP 800-38B §6.2, step 6), one block at a time: `buf := Mⱼ ⊕
C`, and `C := CIPH_K(buf)` to the chaining value; the data are only read. -/
def macMode : Modes.Mode where
  pre := Modes.xorBlk 2 .buf .dat .chn
  post := Modes.copyBlk 2 .chn .buf
  step := 8
  ivOut := true

/-- The CBC-MAC of the `n = a3` blocks at `a2` into the chaining value at
`a1`, under the schedules at `a0`: Triple DES's core for the modes
(`dirCore .encrypt`), inlined, which copies the schedules once. -/
def macChain : Prog isa := (Impl.TripleDes.RISCV64.dirCore .encrypt).seq macMode

/-- The `s5` whole blocks of data at `s3` chained into the chaining value,
and the data pointer past them. -/
def chainLoop : Prog isa :=
  .seq (.block [mov .a0 .s1, .addi .a1 .s1 400, mov .a2 .s3, mov .a3 .s5, .shift .sll .d .t0 .s5 3,
    .add .s3 .s3 .t0]) macChain

def chainPath : Prog isa :=
  .seq (.block ([.sub .s4 .a3 .t1] ++ toHeld .t1)) (.seq (copy .t6 .t4 .t3 .t5)
    (.seq (.block chainSetup) (.seq ecbCall (.seq chainLoop
      (.seq (.block [.addi .t3 .s1 408, mov .t4 .s3, mov .t5 .s4]) (copy .t6 .t4 .t3 .t5))))))

def absorb : Prog isa :=
  .seq (.block absSave) (.seq heldCode (.seq (.block absFlag)
    (.seq (.ite (.nonzero .t2) chainPath fillPath) (.block (restoreRegs absSaved)))))

/-! ## `finish` -/

def finSaved : List (Reg × Nat) := [(.ra, 0), (.s1, 8), (.s2, 16), (.s3, 24)]

/-- The registers saved, the state to `s1`, the scratch buffer to `s2` and
`out` to `s3`. -/
def finSave : List Instr := saveRegs .a3 finSaved ++ [mov .s1 .a0, mov .s2 .a3, mov .s3 .a2]

/-- The last block, complete: itself (`t5`) and `K1` (`t6`). -/
def complete : List Instr := [.addi .t5 .s1 408, .addi .t6 .s1 384]

/-- The padded block zeroed, and the copy's arguments for the bytes held
back. -/
def padStart : List Instr :=
  storeBytes .t2 .s2 padOff (List.replicate 8 0) ++ [.addi .t3 .s2 padOff, .addi .t4 .s1 408, mov .t5 .t0]

/-- The padding's first byte after the bytes held back, and the padded block
(`t5`) and `K2` (`t6`). -/
def padDone : List Instr :=
  [.addi .t3 .s2 padOff, .add .t3 .t3 .t0, .li .t2 0x80, .store .b .t2 .t3 0, .addi .t5 .s2 padOff,
   .addi .t6 .s1 392]

def padded : Prog isa := .seq (.block padStart) (.seq (copy .t6 .t4 .t3 .t5) (.block padDone))

/-- The last block and its subkey XORed into the chaining value, with ECB's
arguments on it. -/
def finXor : List Instr :=
  [.addi .a0 .s1 400] ++ xorBytes .t2 .t3 .a0 .t5 8 ++ xorBytes .t2 .t3 .a0 .t6 8 ++ ecbArgs 400

/-- The MAC to `out`, and the registers restored. -/
def finOut : List Instr := copyBytes .t0 .s1 .s3 400 0 8 ++ restoreRegs finSaved

def finish : Prog isa :=
  .seq (.block finSave) (.seq heldCode (.seq (.block [.addi .t1 .t0 (-8)])
    (.seq (.ite (.zero .t1) (.block complete) padded)
      (.seq (.block finXor) (.seq ecbCall (.block finOut))))))

end VG.Impl.CmacTripleDes.Stream.RISCV64
