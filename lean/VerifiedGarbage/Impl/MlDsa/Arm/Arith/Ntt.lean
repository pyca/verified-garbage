module

public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Common
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_ntt` and `vg_mldsa_inv_ntt`

`ntt(f = r0, scratch = r1)` and `nttInv(f = r0, scratch = r1)` save
`r4`–`r10` (`saving`: 28 bytes of stack) and store a table of 256 zetas to
`scratch` as `u32`s (`storeTab`, through `r12`): `ζ^BitRev8(m) mod q` for
`NTT`, and its negation `-ζ^BitRev8(m) mod q` for `NTT⁻¹` (the `z` of
Algorithm 42). With `-q` in `r4`, each of the eight layers runs its blocks,
with `r0` pointing at coefficient `j` of `f`, `r1` at the zeta of the block,
`r2` counting the blocks down and `r3` the butterflies of a block; a block
puts its zeta in `r6` and the zeta's `zp` in `r7` (`quot`), for `mulz`. The
layers are separate code, each with its `len` in the offsets of its loads
and stores.

The butterflies are lazy: each reduces only its product, to `mulz`'s value
below `1.5 · 2²³ < 2q`, and stores the sum and the difference as they are,
the coefficients between layers being any words congruent to the
specification's.

* `NTT` (Algorithm 41): the layers with `len` = 128, 64, …, 1, whose zetas
  are consecutive, from `m = 1` up. A butterfly computes
  `t = ζ · f[j + len]` (`mulz`), and stores `f[j] + 2q - t` (`2q` in `r5`,
  so that it is not negative) to `f[j + len]` and `f[j] + t` to `f[j]`:
  each layer adds less than `2q` to the coefficients, which stay less than
  `17q`. A last loop reduces them (`canonBody`: `red`, then `csub`, with
  `q` in `r5`).
* `NTT⁻¹` (Algorithm 42): the layers with `len` = 1, 2, …, 128, whose zetas
  are consecutive from `m = 255` down. A butterfly stores
  `f[j] + f[j + len]` to `f[j]` and `z · (f[j] + 128q - f[j + len])`
  (`128q` in `r5`; `mulz`) to `f[j + len]`: each layer at most doubles the
  bound of the coefficients, which stay less than `256q < 2³¹`. Then every
  coefficient is multiplied by `8347681 = 256⁻¹ mod q` (`mulz`) and reduced
  (`csub`, with `q` in `r5`).

A block ends with `r0` advanced past its upper half, so a layer ends with
`r0` at `f + 1024`, and moves it back. Every address and branch depends
only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.Arm.Arith

open VG.Arm

/-- `ζ^BitRev8(m) mod q`. -/
def zetaTab (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m % 8380417

/-- `-ζ^BitRev8(m) mod q`. -/
def negZetaTab (m : Nat) : Nat := (8380417 - zetaTab m) % 8380417

/-- `t i` to `[r1 + 4i]`, through `r12`. -/
def tabStep (t : Nat → Nat) (i : Nat) : List Instr :=
  [.movw .r12 (BitVec.ofNat 16 (t i % 65536)), .movt .r12 (BitVec.ofNat 16 (t i / 65536)),
   .str .r12 .r1 (4 * i)]

/-- The table `t 0, …, t (n - 1)` at `r1`. -/
def storeTab (t : Nat → Nat) (n : Nat) : List Instr := (List.range n).flatMap (tabStep t)

/-- The registers the transforms save. -/
def nttSaved : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- `r5 ← 2q = 0xFFC002`. -/
def loadTwoQ : List Instr := [.movw .r5 0xC002, .movt .r5 0xFF]

/-- `r5 ← 128q = 0x3FF00080`. -/
def loadBias : List Instr := [.movw .r5 0x80, .movt .r5 0x3FF0]

/-- A butterfly of `NTT` on `[r0]` and `[r0 + 4len]`, with the zeta in `r6`
and `r7` and `2q` in `r5`. -/
def bfly (len : Nat) : List Instr :=
  ([.ldr .r9 .r0 (4 * len)] : List Instr) ++ mulz .r10 .r9 .r12 ++
    ([.ldr .r8 .r0 0, .dp .add .r12 .r8 (.reg .r10), .dp .add .r8 .r8 (.reg .r5), .dp .sub .r8 .r8 (.reg .r10),
      .str .r8 .r0 (4 * len), .str .r12 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)] : List Instr)

/-- A butterfly of `NTT⁻¹` on `[r0]` and `[r0 + 4len]`, with the zeta in
`r6` and `r7` and `128q` in `r5`. -/
def bflyInv (len : Nat) : List Instr :=
  ([.ldr .r8 .r0 0, .ldr .r9 .r0 (4 * len), .dp .add .r12 .r8 (.reg .r9), .str .r12 .r0 0,
    .dp .add .r8 .r8 (.reg .r5), .dp .sub .r9 .r8 (.reg .r9)] : List Instr) ++ mulz .r10 .r9 .r12 ++
    ([.str .r10 .r0 (4 * len), .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)] : List Instr)

/-- A block of `len` butterflies `b`: its zeta, at `r1`, which then moves by
4 bytes (`op` is `add` or `sub`), and the zeta's `zp`. -/
def nttBlk (b : List Instr) (len : Nat) (op : DpOp) : Prog isa :=
  .seq (.block (([.ldr .r6 .r1 0] : List Instr) ++ quot .r7 .r6 ++
      ([.dp op .r1 .r1 (.imm 4), .mov .r3 (.imm (BitVec.ofNat 32 len))] : List Instr)))
    (.seq (.loop (.block b) .ne)
      (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4 * len))), .subs .r2 .r2 (.imm 1)]))

/-- A layer: its `128 / len` blocks, then `r0` back to `f`. -/
def nttLay (b : List Instr) (len : Nat) (op : DpOp) : Prog isa :=
  .seq (.block [.mov .r2 (.imm (BitVec.ofNat 32 (128 / len)))])
    (.seq (.loop (nttBlk b len op) .ne) (.block [.dp .sub .r0 .r0 (.imm 1024)]))

/-- The layers of `NTT` with `len` in `lens`. -/
def nttLays : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (nttLay (bfly len) len .add) (nttLays lens)

/-- The layers of `NTT⁻¹` with `len` in `lens`. -/
def nttInvLays : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (nttLay (bflyInv len) len .sub) (nttInvLays lens)

/-- A coefficient reduced, with `q` in `r5`. -/
def canonBody : List Instr :=
  ([.ldr .r8 .r0 0] : List Instr) ++ red .r8 .r12 .r4 ++ csub .r8 .r12 .r5 ++
    ([.str .r8 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)] : List Instr)

def ntt : Prog isa :=
  saving nttSaved (.seq (.block (storeTab zetaTab 256 ++ loadNQ .r4 ++ loadTwoQ ++
      ([.dp .add .r1 .r1 (.imm 4)] : List Instr)))
    (.seq (nttLays [128, 64, 32, 16, 8, 4, 2, 1])
      (.seq (.block (loadQ .r5 ++ ([.mov .r3 (.imm 256)] : List Instr))) (.loop (.block canonBody) .ne))))

/-- A coefficient times the zeta in `r6` and `r7`, reduced, with `q` in `r5`. -/
def scaleBody : List Instr :=
  ([.ldr .r9 .r0 0] : List Instr) ++ mulz .r10 .r9 .r12 ++ csub .r10 .r12 .r5 ++
    ([.str .r10 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)] : List Instr)

/-- `q` in `r5`, `8347681 = 0x7F6021` and its `zp` in `r6` and `r7`, and the
count in `r3`. -/
def scalePre : List Instr :=
  loadQ .r5 ++ ([.movw .r6 0x6021, .movt .r6 0x7F] : List Instr) ++ quot .r7 .r6 ++
    ([.mov .r3 (.imm 256)] : List Instr)

def nttInv : Prog isa :=
  saving nttSaved (.seq (.block (storeTab negZetaTab 256 ++ loadNQ .r4 ++ loadBias ++
      ([.dp .add .r1 .r1 (.imm 1020)] : List Instr)))
    (.seq (nttInvLays [1, 2, 4, 8, 16, 32, 64, 128])
      (.seq (.block scalePre) (.loop (.block scaleBody) .ne))))

end VG.Impl.MlDsa.Arm.Arith
