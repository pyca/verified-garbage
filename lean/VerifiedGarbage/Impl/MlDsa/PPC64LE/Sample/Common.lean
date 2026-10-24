module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Sample

/-!
# ML-DSA on PPC64LE: sampling from SHAKE

The sampling functions `vg_mldsa_rej_ntt_poly`, `vg_mldsa_rej_bounded_poly`,
`vg_mldsa_expand_mask_poly` and `vg_mldsa_sample_in_ball`, as on 32-bit ARM
(`Impl/MlDsa/Arm/Sample/Common.lean`), with the sponge's arguments all in
registers, as `vg_mlkem_sample_ntt` passes them
(`Impl/MlKem/PPC64LE/Sample.lean`).

They share a layout and a prologue. Each saves its caller's `r27`–`r31` and
its return address in `scratch[2000..2048)` (`pro`) and restores them at the
end (`epi`); from the prologue on, `r31` is `scratch` (2048 bytes), `r30` its
output polynomial, `r29` the message hashed, `r28` its length and `r27` its
parameter (`eta`, `gamma1` or `tau`), which the functions it calls preserve.
`scratch` holds, from byte 0, the Keccak state (200 bytes), the working space
of the sponge functions (640 bytes) and, from byte 840, the XOF output (at
most 1008 bytes). The functions have no stack frame of their own; the sponge
functions' frames use the 48 bytes below the stack pointer.

`sponge rate outlen` hashes the message: it zeroes the state (the empty
message), absorbs the message with `vg_keccak_absorb`, pads it with
`vg_keccak_pad` (SHAKE's suffix `0x1f`) from the position absorbing returns,
and squeezes `outlen` bytes to `scratch + 840` with `vg_keccak_squeeze`:
whole blocks of the rate, so that no permutation is wasted. Its addresses
and branches depend only on the pointers and the length.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Sample

open VG.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Impl.MlKem.PPC64LE (zeroState)

/-- Where the XOF output starts in `scratch`. -/
abbrev outOff : Nat := 840

/-- Where our caller's registers are saved in `scratch`. -/
abbrev saveOff : Nat := 2000

/-- Save `r27`–`r31` and the return address at `scr + 2000`, and set up the
layout: `r31` = `scr`, `r30` = `a`, `r29` = `msg`, then `len` (which sets
`r28`) and `prm` (which sets `r27`). `scr`, `a` and `msg` are argument
registers, so none of them is among `r27`–`r31`. -/
def pro (scr a msg : Reg) (len prm : List Instr) : List Instr :=
  [.mflr .r0, .store .d .r27 scr 2000, .store .d .r28 scr 2008, .store .d .r29 scr 2016,
    .store .d .r30 scr 2024, .store .d .r31 scr 2032, .store .d .r0 scr 2040, mov .r31 scr, mov .r30 a,
    mov .r29 msg] ++ len ++ prm

/-- `absorb(state, rate, 0, msg, len, scratch + 200)`, the state zeroed first. -/
def absArgs (rate : Nat) : List Instr :=
  zeroState .r31 ++ [mov .r3 .r31, .li .r4 rate, .li .r5 0, mov .r6 .r29, mov .r7 .r28, .addi .r8 .r31 200]

/-- `pad(state, rate, pos, 0x1f, scratch + 200)`, with `pos` from `absorb`. -/
def padArgs (rate : Nat) : List Instr :=
  [mov .r5 .r3, mov .r3 .r31, .li .r4 rate, .li .r6 0x1f, .addi .r7 .r31 200]

/-- `squeeze(state, rate, 0, scratch + 840, outlen, scratch + 200)`. -/
def sqzArgs (rate outlen : Nat) : List Instr :=
  [mov .r3 .r31, .li .r4 rate, .li .r5 0, .addi .r6 .r31 840, .li .r7 outlen, .addi .r8 .r31 200]

def callAbsorb : Prog isa := .call "vg_keccak_absorb_scratch" Impl.Sha3.PPC64LE.Stream.absorb
def callPad : Prog isa := .call "vg_keccak_pad_scratch" Impl.Sha3.PPC64LE.Stream.pad
def callSqueeze : Prog isa := .call "vg_keccak_squeeze_scratch" Impl.Sha3.PPC64LE.Stream.squeeze

/-- `outlen` bytes of SHAKE with the rate `rate` of the message at `r29`, of
`r28` bytes, to `r31 + 840`. -/
def sponge (rate outlen : Nat) : Prog isa :=
  .seq (.seq (.block (absArgs rate)) callAbsorb)
    (.seq (.seq (.block (padArgs rate)) callPad) (.seq (.block (sqzArgs rate outlen)) callSqueeze))

/-- Our caller's `r27`–`r31` and return address restored (`r31`, the base,
last). -/
def epi : List Instr :=
  [.load .d .r0 .r31 2040, .mtlr .r0, .load .d .r27 .r31 2000, .load .d .r28 .r31 2008,
    .load .d .r29 .r31 2016, .load .d .r30 .r31 2024, .load .d .r31 .r31 2032]

/-- `r3 ← r5 >> 8`: 1 if `j` = `r5` is 256, 0 if it is less. -/
def retJ : List Instr := [.lsr .d .r3 .r5 8]

/-- `q` in `r7`. -/
def loadQ : List Instr := [.lis .r7 0x7F, .ori .r7 .r7 0xE001]

/-- `r12 ≠ 0` iff `j` = `r5` is less than 256 and the value `d` is less than
`bound` (as `subi`, or `sub` from a register): the AND of two sign bits, through
`r11`. -/
def testJ (lt : List Instr) : List Instr :=
  lt ++ [.lsr .d .r12 .r12 63, .subi .r11 .r5 256, .lsr .d .r11 .r11 63, .logic .and .r12 .r12 .r11]

/-- The value `v` stored as the next coefficient (at `r4`) if `r12 ≠ 0`. -/
def accept (v : Reg) : Prog isa :=
  .ite (.zero .d .r12) (.block []) (.block [.store .w v .r4 0, .addi .r4 .r4 4, .addi .r5 .r5 1])

/-- `v ← v + q` if `v` is negative (as a 64-bit number), with `r11` the sign
bit and `q` in `r7`. -/
def addQNeg (v : Reg) : List Instr := [.lsr .d .r11 v 63, .mul .r11 .r11 .r7, .add v v .r11]

end VG.Impl.MlDsa.PPC64LE.Sample
