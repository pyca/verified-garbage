module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Sample
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Encode

/-!
# ML-DSA on RISC-V: sampling from SHAKE

The sampling functions `vg_mldsa_rej_ntt_poly`, `vg_mldsa_rej_bounded_poly`,
`vg_mldsa_expand_mask_poly` and `vg_mldsa_sample_in_ball`, as on PPC64LE
(`Impl/MlDsa/PPC64LE/Sample/`), with the sponge's arguments in registers, as
`vg_mlkem_sample_ntt` passes them (`Impl/MlKem/RISCV64/Sample.lean`).

They share a layout and a prologue. Each saves its caller's `s7`–`s11` and
its return address in `scratch[2000..2048)` (`pro`) and restores them at the
end (`epi`); from the prologue on, `s11` is `scratch` (2048 bytes), `s10` its
output polynomial, `s9` the message hashed, `s8` its length and `s7` its
parameter (`eta`, `gamma1` or `tau`), which the Keccak functions it calls
keep. The parameter is a `u32`, whose register's upper bits the ABI leaves
unspecified, so only 32-bit instructions read it (`Pack.sel`'s `subw`, and
`subw`). `scratch` holds, from byte 0, the Keccak state (200 bytes) and,
from byte 840, the XOF output (at most 1008 bytes). The functions have no
stack frame of their own; the Keccak functions' frames use the 1168 bytes
below the stack pointer.

`sponge rate outlen` hashes the message: it zeroes the state (the empty
message), absorbs the message with `vg_keccak_absorb`, pads it with
`vg_keccak_pad` (SHAKE's suffix `0x1f`) from the position absorbing returns,
and squeezes `outlen` bytes to `scratch + 840` with `vg_keccak_squeeze`.
Its addresses and branches depend only on the pointers and the length.

* `vg_mldsa_rej_ntt_poly(seed = a0, a = a1, scratch = a2) -> a0` squeezes
  `3 N` bytes of SHAKE128 of the 34 bytes of the seed, which `N` iterations
  of `RejNTTPoly`'s loop take 3 bytes at a time: the value of the 3 bytes is
  stored to `a[j]` and `j` incremented if it is less than `q` and `j < 256`
  (`rnTry N`). Almost every value is less than `q`, so 840 bytes (280
  iterations) almost always give 256 coefficients: it tries those first,
  and only if they fall short tries again from the start with 1008 bytes
  (336 iterations). It returns `j >> 8`.
* `vg_mldsa_rej_bounded_poly(seed = a0, eta = a1, a = a2, scratch = a3) -> a0`
  squeezes 544 bytes of SHAKE256 of the 66 bytes of the seed, two half-bytes
  of each of which `CoeffFromHalfByte` takes, for `η` 2 or 4.
* `vg_mldsa_expand_mask_poly(seed = a0, gamma1 = a1, a = a2, scratch = a3)`
  squeezes 640 bytes of SHAKE256 of the 66 bytes of the seed and unpacks
  `γ₁ - x` of each field of 18 or 20 bits (`Pack.unpackLoop`).
* `vg_mldsa_sample_in_ball(rho = a0, len = a1, tau = a2, c = a3,
  scratch = a4) -> a0` squeezes 272 bytes of SHAKE256 of `ρ`, zeroes `c` and
  runs `SampleInBall`'s loop over the 264 bytes after the 8 bytes of sign
  bits.

The loops' branches and the addresses of their stores (and whether
`vg_mldsa_rej_ntt_poly` tries again) depend on the XOF output, a function
of the seed, which the contracts let them leak.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.Sample

open VG.RISCV64
open VG.Impl.Sha3.RISCV64.Stream (mov)
open VG.Impl.MlKem.RISCV64 (zeroState)

/-! ## The layout and the sponge -/

/-- Where the XOF output starts in `scratch`. -/
abbrev outOff : Nat := 840

/-- Where our caller's registers are saved in `scratch`. -/
abbrev saveOff : Nat := 2000

/-- Save `s7`–`s11` and the return address at `scr + 2000`, and set up the
layout: `s11` = `scr`, `s10` = `a`, `s9` = `msg`, then `len` (which sets
`s8`) and `prm` (which sets `s7`). -/
def pro (scr a msg : Reg) (len prm : List Instr) : List Instr :=
  [.store .d .s7 scr 2000, .store .d .s8 scr 2008, .store .d .s9 scr 2016, .store .d .s10 scr 2024,
    .store .d .s11 scr 2032, .store .d .ra scr 2040, mov .s11 scr, mov .s10 a, mov .s9 msg] ++ len ++ prm

/-- `absorb(state, rate, 0, msg, len)`, the state zeroed first. -/
def absArgs (rate : Nat) : List Instr :=
  zeroState .s11 ++ [mov .a0 .s11, .li .a1 rate, .li .a2 0, mov .a3 .s9, mov .a4 .s8]

/-- `pad(state, rate, pos, 0x1f)`, with `pos` from `absorb`. -/
def padArgs (rate : Nat) : List Instr :=
  [mov .a2 .a0, mov .a0 .s11, .li .a1 rate, .li .a3 0x1f]

/-- `squeeze(state, rate, 0, scratch + 840, outlen)`. -/
def sqzArgs (rate outlen : Nat) : List Instr :=
  [mov .a0 .s11, .li .a1 rate, .li .a2 0, .addi .a3 .s11 840, .li .a4 outlen]

def callAbsorb : Prog isa := .call "vg_keccak_absorb" Impl.Sha3.RISCV64.Stream.absorb
def callPad : Prog isa := .call Spec.Sha3.padApi.name Impl.Sha3.RISCV64.Stream.pad
def callSqueeze : Prog isa := .call Spec.Sha3.squeezeApi.name Impl.Sha3.RISCV64.Stream.squeeze

/-- `outlen` bytes of SHAKE with the rate `rate` of the message at `s9`, of
`s8` bytes, to `s11 + 840`. -/
def sponge (rate outlen : Nat) : Prog isa :=
  .seq (.seq (.block (absArgs rate)) callAbsorb)
    (.seq (.seq (.block (padArgs rate)) callPad) (.seq (.block (sqzArgs rate outlen)) callSqueeze))

/-- Our caller's `s7`–`s11` and return address restored (`s11`, the base,
last). -/
def epi : List Instr :=
  [.load .d .ra .s11 2040, .load .d .s7 .s11 2000, .load .d .s8 .s11 2008, .load .d .s9 .s11 2016,
    .load .d .s10 .s11 2024, .load .d .s11 .s11 2032]

/-- `a0 ← a2 >> 8`: 1 if `j` = `a2` is 256, 0 if it is less. -/
def retJ : List Instr := [.shift .srl .d .a0 .a2 8]

/-- `q` in `a4`. -/
def loadQ : List Instr := Pack.loadQ

/-- `t2 ≠ 0` iff `j` = `a2` is less than 256 and the value is less than its
bound (`lt` leaves the difference in `t2`): the AND of two sign bits, through
`t1`. -/
def testJ (lt : List Instr) : List Instr :=
  lt ++ [.shift .srl .d .t2 .t2 63, .addi .t1 .a2 (-256), .shift .srl .d .t1 .t1 63, .logic .and .t2 .t2 .t1]

/-- The value `v` stored as the next coefficient (at `a1`) if `t2 ≠ 0`. -/
def accept (v : Reg) : Prog isa :=
  .ite (.zero .t2) (.block []) (.block [.store .w v .a1 0, .addi .a1 .a1 4, .addi .a2 .a2 1])

/-- `v ← v + q` if `v` is negative (as a 64-bit number), with `t1` the sign
bit and `q` in `a4`. -/
def addQNeg (v : Reg) : List Instr := [.shift .srl .d .t1 v 63, .mul .t1 .t1 .a4, .add v v .t1]

/-! ## `vg_mldsa_rej_ntt_poly` -/

/-- The value of the 3 bytes at `a0` in `a7`. -/
def rnLoad : List Instr :=
  [.load .b .a5 .a0 0, .load .b .a6 .a0 1, .load .b .a7 .a0 2, .shift .sll .d .a6 .a6 8,
    .shift .sll .d .a7 .a7 57, .shift .srl .d .a7 .a7 41, .add .a7 .a7 .a6, .add .a7 .a7 .a5]

def rnBody : Prog isa :=
  .seq (.block (rnLoad ++ testJ [.sub .t2 .a7 .a4]))
    (.seq (accept .a7) (.block [.addi .a0 .a0 3, .addi .a3 .a3 (-1)]))

/-- `N` iterations of the loop, from the XOF output at `scratch + 840`. -/
def rnLoop (N : Nat) : Prog isa :=
  .seq (.block ([.addi .a0 .s11 840, mov .a1 .s10, .li .a2 0, .li .a3 N] ++ loadQ))
    (.loop rnBody (.nonzero .a3))

/-- A try: `3 N` bytes of output, and `N` iterations on them. -/
def rnTry (N : Nat) : Prog isa := .seq (sponge 168 (3 * N)) (rnLoop N)

def rejNTT : Prog isa :=
  .seq (.block (pro .a2 .a1 .a0 [.li .s8 34] []))
    (.seq (rnTry 280)
    (.seq (.block [.shift .srl .d .t0 .a2 8])
    (.seq (.ite (.zero .t0) (rnTry 336) (.block [])) (.block (retJ ++ epi)))))

/-! ## `vg_mldsa_rej_bounded_poly` -/

/-- `a6 ← a6 - s`, plus `s` if that is negative, for `s` 10 or 5, through
`a7` and `t1`. -/
def csub (s : Nat) : List Instr :=
  ([.addi .a6 .a6 (-(s : Int)), .shift .srl .d .t1 .a6 63] : List Instr) ++
    (if s = 10 then [.shift .sll .d .a7 .t1 3, .add .a6 .a6 .a7, .shift .sll .d .a7 .t1 1, .add .a6 .a6 .a7]
      else [.shift .sll .d .a7 .t1 2, .add .a6 .a6 .a7, .add .a6 .a6 .t1])

/-- The coefficient of the half-byte `a6`, modulo `q`, in `a7`: `η - (b mod 5)`
for `η = 2`, `η - b` for `η = 4`. -/
def rbVal : Nat → List Instr
  | 2 => csub 10 ++ csub 5 ++ ([.li .a7 2, .sub .a7 .a7 .a6] : List Instr) ++ addQNeg .a7
  | _ => ([.li .a7 4, .sub .a7 .a7 .a6] : List Instr) ++ addQNeg .a7

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def rbBound : Nat → Nat
  | 2 => 15
  | _ => 9

/-- The half-byte `a6`: its coefficient in `a7`, and `t2 ≠ 0` iff it is
accepted and `j < 256`. -/
def rbHalf (η : Nat) : List Instr := testJ [.addi .t2 .a6 (-(rbBound η : Int))] ++ rbVal η

def rbBody (η : Nat) : Prog isa :=
  .seq (.block ([.load .b .a5 .a0 0, .shift .sll .d .a6 .a5 60, .shift .srl .d .a6 .a6 60] ++ rbHalf η))
    (.seq (accept .a7)
      (.seq (.block (.shift .srl .d .a6 .a5 4 :: rbHalf η))
        (.seq (accept .a7) (.block [.addi .a0 .a0 1, .addi .a3 .a3 (-1)]))))

/-- The loop over `N` bytes, from the XOF output at `scratch + 840`. -/
def rbLoop (N η : Nat) : Prog isa :=
  .seq (.block ([.addi .a0 .s11 840, mov .a1 .s10, .li .a2 0, .li .a3 N] ++ loadQ))
    (.loop (rbBody η) (.nonzero .a3))

/-- A try: `N` bytes of output, and the loop for `η` over them. -/
def rbTry (N : Nat) : Prog isa := .seq (sponge 136 N) (Pack.sel .s7 2 (rbLoop N 2) (rbLoop N 4))

/-- Two blocks (272 bytes) almost always give 256 coefficients, for `η` 2 and
4: the function tries those first, and only if they fall short tries again
from the start with 544 bytes. -/
def rejBounded : Prog isa :=
  .seq (.block (pro .a3 .a2 .a0 [.li .s8 66] [mov .s7 .a1]))
    (.seq (rbTry 272)
    (.seq (.block [.shift .srl .d .t0 .a2 8])
    (.seq (.ite (.zero .t0) (rbTry 544) (.block [])) (.block (retJ ++ epi)))))

/-! ## `vg_mldsa_expand_mask_poly` -/

/-- The fields, from the XOF output at `scratch + 840` to `a`, with `γ₁` in
`a1` and `q` in `a4`. -/
def emLoop (c : Nat) : Prog isa :=
  .seq (.block ([.addi .a7 .s11 840, mov .t1 .s10] ++ Pack.loadQ ++
      Pack.loadB .a1 (if c = 18 then 131072 else 524288)))
    (if c = 18 then Pack.unpackLoop Pack.buFin 18 4 9 else Pack.unpackLoop Pack.buFin 20 2 5)

def expandMask : Prog isa :=
  .seq (.block (pro .a3 .a2 .a0 [.li .s8 66] [mov .s7 .a1]))
    (.seq (sponge 136 640)
      (.seq (Pack.sel .s7 131072 (emLoop 18) (emLoop 20))
        (.block epi)))

/-! ## `vg_mldsa_sample_in_ball` -/

/-- The 256 coefficients of `c` zeroed, through `a1` and `t2`, `a3` counting. -/
def bZero : Prog isa :=
  .seq (.block [.li .t2 0, mov .a1 .s10, .li .a3 256])
    (.loop (.block [.store .w .t2 .a1 0, .addi .a1 .a1 4, .addi .a3 .a3 (-1)]) (.nonzero .a3))

/-- The sign bits in `a6`, `i = 256 - τ` in `a2`, `a1` at `c[i]`, `a0` at the
byte after the sign bits, `a3` = 264 and `a4` = `q - 2`. -/
def bSetup : List Instr :=
  [.load .d .a6 .s11 840, .li .a2 256, .subw .a2 .a2 .s7, .shift .sll .d .a1 .a2 2, .add .a1 .s10 .a1,
    .addi .a0 .s11 848, .li .a3 264] ++ Arith.loadImm .a4 8380415

/-- `c[i] ← c[j]`, `c[j] ← ±1`, the sign bits shifted, `i` incremented. -/
def bSet : List Instr :=
  [.shift .sll .d .a7 .a5 2, .add .a7 .s10 .a7, .load .w .t1 .a7 0, .store .w .t1 .a1 0,
    .shift .sll .d .t2 .a6 63, .shift .srl .d .t2 .t2 63, .mul .t2 .t2 .a4, .addi .t2 .t2 1,
    .store .w .t2 .a7 0, .shift .srl .d .a6 .a6 1, .addi .a1 .a1 4, .addi .a2 .a2 1]

/-- The byte `j` at `a0`, into `a5`, accepted unless `i < j`. -/
def bTry : Prog isa :=
  .seq (.block [.load .b .a5 .a0 0, .sub .t1 .a2 .a5, .shift .srl .d .t1 .t1 63])
    (.ite (.zero .t1) (.block bSet) (.block []))

def bBody : Prog isa :=
  .seq (.block [.addi .t2 .a2 (-256), .shift .srl .d .t2 .t2 63])
    (.seq (.ite (.zero .t2) (.block []) bTry) (.block [.addi .a0 .a0 1, .addi .a3 .a3 (-1)]))

def bLoop : Prog isa := .seq (.block bSetup) (.loop bBody (.nonzero .a3))

def sampleInBall : Prog isa :=
  .seq (.block (pro .a4 .a3 .a0 [mov .s8 .a1] [mov .s7 .a2]))
    (.seq (sponge 136 272) (.seq bZero (.seq bLoop (.block (retJ ++ epi)))))

end VG.Impl.MlDsa.RISCV64.Sample
