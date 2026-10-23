module

public import VerifiedGarbage.Impl.Rc2.PPC64LE.Block

/-! # RC2-CBC on PPC64LE

`vg_rc2_cbc_{en,de}crypt(schedule = r3, iv = r4, data = r5, n = r6,
scratch = r7)` calls the block function on each block in turn, with the
first 256 bytes of the working space as its own. The block function writes
only volatile registers, so our variables live in `r26`–`r31` (`r26` the
schedule, `r27` the chaining value's buffer, `r28` the next block, `r29`
the blocks left, `r30` the working space, `r31` the input ciphertext block
while decrypting), and our caller's values of those registers are saved in
the working space at `256`, as is our return address, which each call
replaces, through `r0`. The code uses no stack. The loop counts down the
public `n`.
-/

@[expose] public section

namespace VG.Impl.Rc2.PPC64LE.Cbc

open VG.PPC64LE

/-- `mr d, n` (as `addi d, n, 0`; `n` is not `r0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The nonvolatile registers we use, and the return address (in `r0`), and
where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r26, 256), (.r27, 264), (.r28, 272), (.r29, 280), (.r31, 296), (.r0, 304), (.r30, 288)]

/-- Save them, with `scratch` in `r7`. -/
def save : List Instr := .mflr .r0 :: saved.map fun (r, d) => .store .d r .r7 d

/-- Restore them from `scratch` in `r30` (`r30`, the base, last), and the
return address. -/
def restore : List Instr := saved.map (fun (r, d) => .load .d r .r30 d) ++ [.mtlr .r0]

def setup : List Instr := [mov .r26 .r3, mov .r27 .r4, mov .r28 .r5, mov .r29 .r6, mov .r30 .r7]

/-- The block function's arguments: the schedule, the block, the working space. -/
def args : List Instr := [mov .r3 .r26, mov .r4 .r28, mov .r5 .r30]

/-- The block XORed with the chaining value, in place. -/
def xorIv : List Instr :=
  [.load .d .r10 .r28 0, .load .d .r11 .r27 0, .logic .xor .r10 .r10 .r11, .store .d .r10 .r28 0]

def before (d : Spec.Rc2.Direction) : List Instr :=
  match d with
  | .encrypt => xorIv ++ args
  | .decrypt => [.load .d .r31 .r28 0] ++ args

def after (d : Spec.Rc2.Direction) : List Instr :=
  match d with
  | .encrypt => [.load .d .r10 .r28 0, .store .d .r10 .r27 0]
  | .decrypt => xorIv ++ ([.store .d .r31 .r27 0] : List Instr)

def advance : List Instr := [.addi .r28 .r28 8, .subi .r29 .r29 1]

def blockCall (d : Spec.Rc2.Direction) : Prog isa :=
  match d with
  | .encrypt => .call "vg_rc2_encrypt_block" encryptBlock
  | .decrypt => .call "vg_rc2_decrypt_block" decryptBlock

def body (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block (before d)) (.seq (blockCall d) (.block (after d ++ advance)))

def cbc (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite (.zero .d .r29) (.block []) (.loop (body d) (.nonzero .d .r29))) (.block restore))

def encrypt : Prog isa := cbc .encrypt
def decrypt : Prog isa := cbc .decrypt

end VG.Impl.Rc2.PPC64LE.Cbc
