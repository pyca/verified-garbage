module

public import VerifiedGarbage.Impl.Rc2.RISCV64.Block

/-! # RC2-CBC on RISC-V

`vg_rc2_cbc_{en,de}crypt(schedule = a0, iv = a1, data = a2, n = a3,
scratch = a4)` calls the block function on each block in turn, with the
first 256 bytes of the working space as its own, as on PPC64LE
(`Impl/Rc2/PPC64LE/Cbc.lean`). The block function writes only temporaries
and argument registers, so our variables live in `s1`–`s6` (`s1` the
schedule, `s2` the chaining value's buffer, `s3` the next block, `s4` the
blocks left, `s5` the working space, `s6` the input ciphertext block while
decrypting), and our caller's values of those registers are saved in the
working space at `256`, as is our return address, which each call
replaces. The IV and the data are accessed a byte at a time, as
little-endian doublewords, since the contracts state no alignment for them.
The code uses no stack. The loop counts down the public `n`.
-/

@[expose] public section

namespace VG.Impl.Rc2.RISCV64.Cbc

open VG.RISCV64
open VG.Impl.Words.RISCV64 (loadLE64 storeLE64)

/-- `mv d, n`. -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The preserved registers we use, and the return address, and where they
are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.s1, 256), (.s2, 264), (.s3, 272), (.s4, 280), (.s6, 296), (.ra, 304), (.s5, 288)]

/-- Save them, with `scratch` in `a4`. -/
def save : List Instr := saved.map fun (r, d) => .store .d r .a4 d

/-- Restore them from `scratch` in `s5` (`s5`, the base, last). -/
def restore : List Instr := saved.map fun (r, d) => .load .d r .s5 d

def setup : List Instr := [mov .s1 .a0, mov .s2 .a1, mov .s3 .a2, mov .s4 .a3, mov .s5 .a4]

/-- The block function's arguments: the schedule, the block, the working space. -/
def args : List Instr := [mov .a0 .s1, mov .a1 .s3, mov .a2 .s5]

/-- The block XORed with the chaining value, in place. -/
def xorIv : List Instr :=
  loadLE64 .t0 .a7 .t1 .s3 0 ++ loadLE64 .t2 .a7 .t1 .s2 0 ++ [.logic .xor .t0 .t0 .t2] ++
    storeLE64 .t0 .a7 .t1 .s3 0

def before (d : Spec.Rc2.Direction) : List Instr :=
  match d with
  | .encrypt => xorIv ++ args
  | .decrypt => loadLE64 .s6 .a7 .t1 .s3 0 ++ args

def after (d : Spec.Rc2.Direction) : List Instr :=
  match d with
  | .encrypt => loadLE64 .t0 .a7 .t1 .s3 0 ++ storeLE64 .t0 .a7 .t1 .s2 0
  | .decrypt => xorIv ++ storeLE64 .s6 .a7 .t1 .s2 0

def advance : List Instr := [.addi .s3 .s3 8, .addi .s4 .s4 (-1)]

def blockCall (d : Spec.Rc2.Direction) : Prog isa :=
  match d with
  | .encrypt => .call "vg_rc2_encrypt_block" encryptBlock
  | .decrypt => .call "vg_rc2_decrypt_block" decryptBlock

def body (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block (before d)) (.seq (blockCall d) (.block (after d ++ advance)))

def cbc (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite (.zero .s4) (.block []) (.loop (body d) (.nonzero .s4))) (.block restore))

def encrypt : Prog isa := cbc .encrypt
def decrypt : Prog isa := cbc .decrypt

end VG.Impl.Rc2.RISCV64.Cbc
