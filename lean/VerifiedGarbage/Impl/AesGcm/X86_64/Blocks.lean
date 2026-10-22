module

public import VerifiedGarbage.Impl.AesGcm.X86_64

/-!
# AES-GCM on whole blocks: x86-64 implementation

`vg_aes_gcm_encrypt_blocks` and `vg_aes_gcm_decrypt_blocks`
`(ctx = rdi, rounds = rsi, counter = rdx, y = rcx, data = r8, n = r9,
scratch = [rsp + 8])`, generic over the implementations of `vg_aes_ctr32` and
`vg_ghash` they call, as the other functions of AES-GCM.

The entry keeps the arguments in `scratch` (`ctx`, `rounds`, `counter`, `y`,
`data` and `n` at `scratch` … `scratch + 40`). With a `piece` (loops that
interleave counter mode and GHASH, such as `Gcm.X86_64.Stitch`), the first
`16 ⌊n / 16⌋` blocks, if any, are encrypted and hashed in one pass by it
(with `scratch + 64` for its working space), and the arguments kept become
those of the rest; a `piece` that also takes the blocks after the last 16
(`full`) is given them all, the arguments kept first made those of no rest. The rest (all the blocks, without a `piece`) is then encrypted with `vg_aes_ctr32` and hashed with
`vg_ghash` (hashed first when decrypting), each called with `scratch + 64`,
reloading the arguments from `scratch` after each call.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.Blocks

open VG.X86_64

/-- Where the entry keeps the arguments, in `scratch`. -/
def argCtx : Nat := 0
def argRounds : Nat := 8
def argCtr : Nat := 16
def argY : Nat := 24
def argData : Nat := 32
def argN : Nat := 40

/-- The arguments kept, with `scratch` in `r11`. -/
def entry : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 8)), .store (at_ .r11 argCtx) .rdi, .store (at_ .r11 argRounds) .rsi,
    .store (at_ .r11 argCtr) .rdx, .store (at_ .r11 argY) .rcx, .store (at_ .r11 argData) .r8,
    .store (at_ .r11 argN) .r9]

/-- Leave the saved arguments intact, optionally rounding the working
space up to a cache-line boundary. The public scratch buffer has room
for the at most 63 bytes of padding and the 1024-byte interleaved region. -/
def scratchSetup (aligned : Bool) : List Instr :=
  if aligned then [.alu .add .r11 (imm 127), .alu .and .r11 (.imm (-64))]
  else [.alu .add .r11 (imm 64)]

/-- If there are at least 16 blocks, the first `16 ⌊n / 16⌋` by `piece`, with
`r11` at the powers, `scratch + 64`, rounded up to 64 bytes when `aligned`.
If `full` (a `piece` that also takes the blocks after the last 16), only
`r11` set and `piece`, which `blocks` runs once it has found at least 16
blocks. -/
def stitchPart (piece : Prog isa) (aligned : Bool := false) (full : Bool := false) : Prog isa :=
  if full then .seq (.block (scratchSetup aligned)) piece
  else
    .seq (.block [.alu .cmp .r9 (imm 16)])
      (.ite .b (.block [])
        (.seq (.block ([.mov .rax (.reg .r9), .alu .and .rax (imm 15), .alu .sub .r9 (.reg .rax)] ++
          scratchSetup aligned)) piece))

/-- The arguments of the rest: `n mod 16` blocks after the first
`16 ⌊n / 16⌋`. -/
def rest : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 8)), .mov .r8 (.mem (at_ .r11 argN)), .mov .rax (.reg .r8),
    .alu .and .r8 (imm 15), .alu .sub .rax (.reg .r8), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.mem (at_ .r11 argData)),
    .store (at_ .r11 argData) .rax, .store (at_ .r11 argN) .r8]

/-- The arguments of `vg_aes_ctr32` on the rest. -/
def ctrArgs : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 8)), .mov .rdi (.mem (at_ .r11 argCtx)), .mov .rsi (.mem (at_ .r11 argRounds)),
    .mov .rdx (.mem (at_ .r11 argCtr)), .mov .rcx (.mem (at_ .r11 argData)), .mov .r8 (.mem (at_ .r11 argN)),
    .mov .r9 (.reg .r11), .alu .add .r9 (imm 64)]

/-- The arguments of `vg_ghash` on the rest. -/
def ghArgs : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 8)), .mov .rdi (.mem (at_ .r11 argCtx)), .alu .add .rdi (imm 240),
    .mov .rsi (.mem (at_ .r11 argY)), .mov .rdx (.mem (at_ .r11 argData)), .mov .rcx (.mem (at_ .r11 argN)),
    .mov .r8 (.reg .r11), .alu .add .r8 (imm 64)]

variable (ctr gh : Fn)

/-- The rest, if any, with `first` and then `second`. -/
def tail (first second : Prog isa) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (at_ .rsp 8)), .mov .r8 (.mem (at_ .r11 argN)), .alu .test .r8 (.reg .r8)])
    (.ite .e (.block []) (.seq first second))

def ctrCall : Prog isa := .seq (.block ctrArgs) (.call ctr.name ctr.code)
def ghCall : Prog isa := .seq (.block ghArgs) (.call gh.name gh.code)

/-- The first blocks by `piece`, if any, then the rest. -/
def head (piece : Option (Prog isa)) (aligned : Bool := false) : Prog isa :=
  match piece with
  | some piece => .seq (stitchPart piece aligned) (.block rest)
  | none => .block []

/-- The fewest blocks a `piece` that also takes fewer than 16 takes: 2, or 5
with `small4` (fewer go to `first` and `second`, which cost less for
them). -/
def smallMin (small4 : Bool) : Nat := if small4 then 5 else 2

/-- Whether a multiple of 4 blocks (8 or 12) goes to `first` and `second`
too: with `small4`, to encrypt (not `dec`), where the counter mode encrypts
them in batches of eight and four, with no single blocks, and they are
hashed together, as fast as `pieceS` or faster. -/
def skip4 (small4 dec : Bool) : Bool := small4 && !dec

/-- From `smallMin` blocks on, fewer than 16: `pieceS`, or, with `skip4`,
`calls` on a multiple of 4 blocks. -/
def smallPart (pieceS calls : Prog isa) (aligned skip : Bool) : Prog isa :=
  if skip then .seq (.block [.alu .test .r9 (imm 3)]) (.ite .e calls (stitchPart pieceS aligned true))
  else stitchPart pieceS aligned true

/-- With a `piece` that takes all the blocks: all of them by it if at least
16, or, if `small`, by `pieceS` (by default `piece`) if at least
`smallMin small4` (but a multiple of 4 with `skip4 small4 dec`), else all of them with
`first` and `second`. `pieceS`
runs only on fewer than 16 blocks, and its code comes after `piece`'s, which
keeps its addresses whatever `pieceS` is. -/
def fullBody (piece first second : Prog isa) (aligned : Bool := false) (small : Bool := false)
    (small4 : Bool := false) (pieceS : Option (Prog isa) := none) (dec : Bool := false) : Prog isa :=
  .seq (.block [.alu .cmp .r9 (imm 16)])
    (.ite .b
      (if small then
        .seq (.block [.alu .cmp .r9 (imm (smallMin small4))])
          (.ite .b (.seq (.block rest) (tail first second))
            (smallPart (pieceS.getD piece) (.seq (.block rest) (tail first second)) aligned (skip4 small4 dec)))
      else .seq (.block rest) (tail first second))
      (stitchPart piece aligned true))

/-- After the entry: the blocks by `piece` (all of them if `full`, and by
`pieceS` from `smallMin small4` on if also `small`), and the rest with
`first` and `second`. -/
def body (piece : Option (Prog isa)) (first second : Prog isa) (aligned : Bool := false) (full : Bool := false)
    (small : Bool := false) (small4 : Bool := false) (pieceS : Option (Prog isa) := none) (dec : Bool := false) : Prog isa :=
  match piece, full with
  | some piece, true => fullBody piece first second aligned small small4 pieceS dec
  | piece, _ => .seq (head piece aligned) (tail first second)

def blocks (piece : Option (Prog isa)) (first second : Prog isa) (aligned : Bool := false) (full : Bool := false)
    (small : Bool := false) (small4 : Bool := false) (pieceS : Option (Prog isa) := none) (dec : Bool := false) : Prog isa :=
  .seq (.block entry) (body piece first second aligned full small small4 pieceS dec)

/-- `vg_aes_gcm_encrypt_blocks`, with the encrypting `piece`, if any (taking
all the blocks if `full`, from 1 on if also `small`; see `body`). -/
def encrypt (piece : Option (Prog isa)) (aligned : Bool := false) (full : Bool := false) (small : Bool := false)
    (small4 : Bool := false) (pieceS : Option (Prog isa) := none) : Prog isa :=
  blocks piece (ctrCall ctr) (ghCall gh) aligned full small small4 pieceS

/-- `vg_aes_gcm_decrypt_blocks`, with the decrypting `piece`, if any (taking
all the blocks if `full`, from 1 on if also `small`; see `body`). -/
def decrypt (piece : Option (Prog isa)) (aligned : Bool := false) (full : Bool := false) (small : Bool := false)
    (small4 : Bool := false) (pieceS : Option (Prog isa) := none) : Prog isa :=
  blocks piece (ghCall gh) (ctrCall ctr) aligned full small small4 pieceS true

end VG.Impl.AesGcm.X86_64.Blocks
