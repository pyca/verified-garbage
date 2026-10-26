module

public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64
public import VerifiedGarbage.Impl.Pbkdf2.RISCV64

/-!
# PBKDF2-HMAC over any streaming hash function: RISC-V implementation of the whole derivation

`pbkdf2(password = a0, password_len = a1, salt = a2, salt_len = a3, c = a4,
out = a5, out_len = a6)` computes PBKDF2-HMAC (RFC 8018 §5.2) from the
verified functions of one hash function (`Fns`): HMAC's `init` for a key of
any length makes the password's inner and outer states; each block `i` of
the output copies the inner state, absorbs the salt and `INT (i)` into it
with the streaming `update` and computes `U₁` with HMAC's `finalize`; `T`
starts as `U₁`, `iterate` runs the other `c - 1` steps, and as much of `T`
as the output still needs is copied to `out`.

It runs in two frames on the stack (`alloc`), since `addi` reaches only
2047 bytes: the outer one (`itB` bytes) is `iterate`'s working space, and
the inner one (`bytes` rounded up to a multiple of 16) holds our caller's
`ra` and `s1`–`s7`, then the key's two states, a working state, `U`, `T`
and `INT (i)`. The functions we call let their own callees use the stack
below the frames.

Our variables live in `s1`–`s7`: `s1` = the inner frame, `s2` = `salt_len`,
`s3` = `c`, `s4` = where the rest of the output goes, `s5` = how many bytes
of it are left, `s6` = `salt` and `s7` = the block number `i`. The functions
we call save and restore the callee-saved registers they write, so the
analysis of constant time relates the runs around those calls by their
contracts rather than following the registers through them. `c` is a 32-bit
argument whose other bits may be anything: only `iterate` reads it, and only
its low 32 bits. `INT (i)` is written big-endian, a byte at a time, before
it is absorbed. Whether fewer than `D` bytes of output are left is the sign
of their number minus `D`, which is less than `2⁶³`. The salt, the password
and `out` are argument buffers, whose alignment the contract does not state,
so they are accessed a byte at a time. Every address and branch depends only
on the pointers and the lengths.
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Impl.Pbkdf2.RISCV64 (It)

/-- The functions PBKDF2 calls, for one hash function: its streaming
functions with HMAC's `init` and `finalize` over them (`H`, with their
sizes), HMAC's names, and PBKDF2's `iterate` (with its code and the bytes
of working space it uses), with their names. -/
structure Fns where
  H : Hash
  hiN : String
  hfN : String
  itN : String
  itC : Prog isa
  itW : Nat

namespace Fns

variable (F : Fns)

/-- The key's inner and outer states and the working state, after our
caller's registers. -/
def st0O : Nat := 64
def st1O : Nat := st0O + F.H.S
def stWO : Nat := F.st1O + F.H.S

/-- `U`, `T` and `INT (i)`. -/
def uO : Nat := F.stWO + F.H.S
def tO : Nat := F.uO + F.H.D
def intO : Nat := F.tO + F.H.D

/-- The bytes of the inner frame we use. -/
def bytes : Nat := F.intO + 4

/-- The bytes of the inner frame (16-byte aligned). -/
def frB : Nat := (F.bytes + 15) / 16 * 16

/-- The bytes of `iterate`'s working space, the outer frame (16-byte aligned). -/
def itB : Nat := (F.itW + 15) / 16 * 16

/-- The bytes of stack the functions we call use below our frames: HMAC's
`init` and `finalize` in a frame of their own, above their callees'. -/
def X : Nat := max F.H.ibytes F.H.fbytes + F.H.F

/-- The registers we save, and where, at the start of the inner frame. -/
def saved : List (Reg × Nat) :=
  [(.ra, 0), (.s1, 8), (.s2, 16), (.s3, 24), (.s4, 32), (.s5, 40), (.s6, 48), (.s7, 56)]

/-- Where we restore them from, in order (`s1`, the base, last). -/
def restList : List (Reg × Nat) :=
  [(.ra, 0), (.s2, 16), (.s3, 24), (.s4, 32), (.s5, 40), (.s6, 48), (.s7, 56), (.s1, 8)]

/-- A call of HMAC's `init`. -/
def callHi : Prog isa := .call F.hiN F.H.init

/-- A call of HMAC's `finalize`. -/
def callHf : Prog isa := .call F.hfN F.H.finalize

/-- A call of `iterate`. -/
def callIt : Prog isa := .call F.itN F.itC

/-- Our caller's registers into the inner frame, which `s1` then holds; the
arguments into the registers that keep them; HMAC's `init`'s arguments. -/
def prologue : List Instr :=
  .addSp .t0 0 :: saved.map (fun (r, d) => .store .d r .t0 d) ++
    [mov .s1 .t0, mov .s2 .a3, mov .s3 .a4, mov .s4 .a5, mov .s5 .a6, mov .s6 .a2, mov .a2 .a0, mov .a3 .a1,
      .addi .a0 .s1 st0O, .addi .a1 .s1 F.st1O]

/-- `INT (1)`'s `i`. -/
def loopInit : List Instr := [.li .s7 1]

/-- The key's inner state copied into the working one, and `update`'s
arguments for the salt: the working state, from a `count` of `B`. -/
def saltArgs : List Instr :=
  It.cp .s1 .s1 st0O F.stWO F.H.S ++ [.addi .a0 .s1 F.stWO, .li .a1 F.H.B, mov .a2 .s6, mov .a3 .s2]

/-- `INT (i)`, big-endian, and `update`'s arguments for it: the working
state, and the bytes absorbed. -/
def updArgs : List Instr :=
  [.shift .srl .d .t1 .s7 24, .store .b .t1 .s1 F.intO, .shift .srl .d .t1 .s7 16, .store .b .t1 .s1 (F.intO + 1),
    .shift .srl .d .t1 .s7 8, .store .b .t1 .s1 (F.intO + 2), .store .b .s7 .s1 (F.intO + 3),
    .addi .a0 .s1 F.stWO, .addi .a1 .s2 F.H.B, .addi .a2 .s1 F.intO, .li .a3 4]

/-- HMAC's `finalize`'s arguments: the working state, the outer state, the
bytes absorbed and `U`. -/
def finArgs : List Instr :=
  [.addi .a0 .s1 F.stWO, .addi .a1 .s1 F.st1O, .addi .a2 .s2 (F.H.B + 4), .addi .a3 .s1 F.uO]

/-- `U` copied into `T`, and `iterate`'s arguments: the key's states, `U`,
`c - 1`, `T` and the outer frame. -/
def iterArgs : List Instr :=
  It.cp .s1 .s1 F.uO F.tO F.H.D ++
    [.addi .a0 .s1 st0O, .addi .a1 .s1 F.uO, .addi .a2 .s3 (-1), .addi .a3 .s1 F.tO, .addi .a4 .s1 F.frB]

/-- The bytes of `T` the output still needs, `min (s5, D)`, in `t2`. -/
def outLen : Prog isa :=
  .seq (.block [.addi .t1 .s5 (-(F.H.D : Int)), .shift .srl .d .t1 .t1 63, mov .t2 .s5])
    (.ite (.nonzero .t1) (.block []) (.block [.li .t2 F.H.D]))

/-- The loop copying `t2` bytes of `T` to `s4`, with `t3` the index. -/
def outLoop : Prog isa :=
  .seq (.block [.li .t3 0])
    (.loop (.block [.add .t4 .s1 .t3, .load .b .t1 .t4 F.tO, .add .t4 .s4 .t3, .store .b .t1 .t4 0,
      .addi .t3 .t3 1, .addi .t2 .t2 (-1)]) (.nonzero .t2))

/-- Past the bytes written, and the next `i`. -/
def advance : List Instr := [.add .s4 .s4 .t3, .sub .s5 .s5 .t3, .addi .s7 .s7 1]

/-- One block of the output. -/
def block : Prog isa :=
  .seq (.block F.saltArgs)
  (.seq F.H.callUpd
  (.seq (.block F.updArgs)
  (.seq F.H.callUpd
  (.seq (.block F.finArgs)
  (.seq F.callHf
  (.seq (.block F.iterArgs)
  (.seq F.callIt
  (.seq F.outLen
  (.seq F.outLoop
    (.block advance))))))))))

/-- Restore our caller's registers. -/
def restore : List Instr := restList.map fun (r, d) => .load .d r .s1 d

/-- `pbkdf2`, in its frames. -/
def main : Prog isa :=
  .seq (.block F.prologue)
  (.seq F.callHi
  (.seq (.block loopInit)
  (.seq (.ite (.zero .s5) (.block []) (.loop F.block (.nonzero .s5)))
    (.block restore))))

/-- PBKDF2. -/
def pbkdf2 : Prog isa :=
  .frame (.alloc F.itB) (.frame (.alloc F.frB) F.main (.free F.frB)) (.free F.itB)

end Fns

end VG.Impl.Pbkdf2.Whole.RISCV64
