module

public import VerifiedGarbage.Impl.StackScratch.X86_64

/-!
# A scratch buffer on the stack, chosen slots of it wiped after use (x86-64)

`withStackArgScratchWipedSlots bytes m z ss c` is `withStackArgScratch bytes
m c`, then zeroes the slots `ss` of the buffer: for a function whose working
space holds secrets only there, which wiping all of it would cost more than
the function on short inputs. `withStackArgScratchSlots` is the same, but
without slots it is `withStackArgScratch`, for registrations whose
implementations differ in what they leave.
-/

@[expose] public section

namespace VG.Impl.StackScratch.X86_64

open VG.X86_64

/-! ## Wiping chosen slots of the buffer -/

/-- How `wipeSlots` zeroes the register it stores: `xmm0` with SSE2's
`pxor`, or with AVX's 128-bit `vpxor`, which zeroes all of `zmm0` (Intel SDM,
`PXOR`: "VEX.128 encoded version: … DEST[MAXVL-1:128] := 0") without leaving
the upper halves dirty after the code's `vzeroupper`, as a 256- or 512-bit
write would. -/
inductive Zero where
  | sse
  | vex

/-- The instruction zeroing the register. -/
def Zero.instr : Zero → Instr
  | .sse => .xop (.bin .pxor .xmm0 .xmm0)
  | .vex => .vop (.vbin .vpxor .l128 .xmm0 .xmm0 .xmm0)

/-- A slot of the buffer that `wipeSlots` zeroes, at byte `d` of it: 16
bytes with SSE2's `movdqu`, 16 or 32 with VEX's `vmovdqu`, or 64 with
AVX-512's `vmovdqu32`. -/
inductive Slot where
  | x (d : Nat)
  | v16 (d : Nat)
  | v32 (d : Nat)
  | z (d : Nat)

/-- Where the slot starts in the buffer. -/
def Slot.disp : Slot → Nat
  | .x d | .v16 d | .v32 d | .z d => d

/-- How many bytes it has. -/
def Slot.size : Slot → Nat
  | .x _ | .v16 _ => 16
  | .v32 _ => 32
  | .z _ => 64

/-- Its store, of the zeroed register, with the buffer at `rsp + off`. -/
def Slot.instr (off : Nat) : Slot → Instr
  | .x d => .movdquStore { base := .rsp, disp := ((off + d : Nat) : Int) } .xmm0
  | .v16 d => .vmovdquStore .l128 { base := .rsp, disp := ((off + d : Nat) : Int) } .xmm0
  | .v32 d => .vmovdquStore .l256 { base := .rsp, disp := ((off + d : Nat) : Int) } .xmm0
  | .z d => .vmovdqu32Store { base := .rsp, disp := ((off + d : Nat) : Int) } .xmm0

/-- Zeroes the slots `ss` of the buffer at `rsp + off`. -/
def wipeSlots (z : Zero) (off : Nat) (ss : List Slot) : List Instr := z.instr :: ss.map (·.instr off)

/-- `withStackArgScratch`, zeroing the slots `ss` of the buffer (at `rsp +
16 + 8m`) after the code, for a function that leaves secrets only there. -/
def withStackArgScratchWipedSlots (bytes m : Nat) (z : Zero) (ss : List Slot) (c : Prog isa) : Prog isa :=
  withStackArgScratch bytes m (.seq c (.block (wipeSlots z (16 + 8 * m) ss)))


/-- `withStackArgScratchWipedSlots`, or with no slots, `withStackArgScratch`. -/
def withStackArgScratchSlots (bytes m : Nat) (z : Zero) (ss : List Slot) (c : Prog isa) : Prog isa :=
  if ss.isEmpty then withStackArgScratch bytes m c else withStackArgScratchWipedSlots bytes m z ss c

end VG.Impl.StackScratch.X86_64
