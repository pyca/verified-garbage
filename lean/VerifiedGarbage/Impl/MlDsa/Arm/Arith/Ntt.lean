module

public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Common
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_ntt` and `vg_mldsa_inv_ntt`

`ntt(f = r0, scratch = r1)` and `nttInv(f = r0, scratch = r1)` save
`r4`–`r10` (`saving`: 28 bytes of stack) and store a table of 256 zetas to
`scratch` as `u32`s (`storeTab`, through `r12`): `ζ^BitRev8(m) mod q` for
`NTT`, and its negation `-ζ^BitRev8(m) mod q` for `NTT⁻¹` (the `z` of
Algorithm 42). With `-q` in `r4` and `q` in `r5`, each of the eight layers
runs its blocks, with `r0` pointing at the first coefficient of a group of
butterflies of `f`, `r1` at the zeta of the block and `r2` counting the
blocks down; a block puts its zeta in `r6` and the zeta's `zp` in `r7`
(`zetaPre`), for `mulz`. The layers are separate code, each with its `len`
in the offsets of its loads and stores. A block of `len ≤ 4` butterflies is
straight-line code (`nttBlkS`); a longer one runs them four at a time
(`nttBlkL`, `r3` counting the groups), each at its offset from `r0`.

The butterflies are lazy: each reduces only its product, to `mulz`'s value
below `1.5 · 2²³ < 2q`, and stores the sum and the difference as they are,
the coefficients between layers being any words congruent to the
specification's.

* `NTT` (Algorithm 41): the layers with `len` = 128, 64, …, 1, whose zetas
  are consecutive, from `m = 1` up. A butterfly (`bfly`) computes
  `t = ζ · f[j + len]` (`mulz`), and stores `f[j] + 2q - t` (so that it is
  not negative) to `f[j + len]` and `f[j] + t` to `f[j]`: each layer adds
  less than `2q` to the coefficients, which stay less than `15q` before the
  last, whose butterflies (`bflyC`) reduce what they store (`red`, then
  `csub`).
* `NTT⁻¹` (Algorithm 42): the layers with `len` = 1, 2, …, 128, whose zetas
  are consecutive from `m = 255` down. A butterfly (`bflyInv`) stores
  `f[j] + f[j + len]` to `f[j]` and `z · (f[j] + 128q - f[j + len])`
  (`mulz`) to `f[j + len]`: each layer at most doubles the bound of the
  coefficients, which stay less than `128q` before the last. The last
  layer's butterflies (`bflyInvS`) also multiply by `8347681 = 256⁻¹ mod q`
  (in `r1`, with its `zp` in `r2`: `mulzF`), the difference by the product
  of that and the zeta (`scaleZeta`, in `r6`), and reduce what they store.

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

/-- A butterfly of `NTT` on `[r0 + 4o]` and `[r0 + 4(o + len)]`, with the
zeta in `r6` and `r7` and `q` in `r5`. -/
def bfly (len o : Nat) : List Instr :=
  ([.ldr .r9 .r0 (4 * (o + len))] : List Instr) ++ mulz .r10 .r9 .r12 ++
    ([.ldr .r8 .r0 (4 * o), .dp .add .r12 .r8 (.reg .r10), .dp .add .r8 .r8 (.shifted .r5 .lsl 1),
      .dp .sub .r8 .r8 (.reg .r10), .str .r8 .r0 (4 * (o + len)), .str .r12 .r0 (4 * o)] : List Instr)

/-- A butterfly of the last layer of `NTT`: `bfly`, with what it stores
reduced. -/
def bflyC (len o : Nat) : List Instr :=
  ([.ldr .r9 .r0 (4 * (o + len))] : List Instr) ++ mulz .r10 .r9 .r12 ++
    ([.ldr .r8 .r0 (4 * o), .dp .add .r12 .r8 (.reg .r10), .dp .add .r8 .r8 (.shifted .r5 .lsl 1),
      .dp .sub .r8 .r8 (.reg .r10)] : List Instr) ++
    red .r12 .r9 .r4 ++ csub .r12 .r9 .r5 ++ red .r8 .r9 .r4 ++ csub .r8 .r9 .r5 ++
    ([.str .r8 .r0 (4 * (o + len)), .str .r12 .r0 (4 * o)] : List Instr)

/-- A butterfly of `NTT⁻¹` on `[r0 + 4o]` and `[r0 + 4(o + len)]`, with the
zeta in `r6` and `r7` and `q` in `r5` (`128q` is `q << 7`). -/
def bflyInv (len o : Nat) : List Instr :=
  ([.ldr .r8 .r0 (4 * o), .ldr .r9 .r0 (4 * (o + len)), .dp .add .r12 .r8 (.reg .r9), .str .r12 .r0 (4 * o),
    .dp .add .r8 .r8 (.shifted .r5 .lsl 7), .dp .sub .r9 .r8 (.reg .r9)] : List Instr) ++ mulz .r10 .r9 .r12 ++
    ([.str .r10 .r0 (4 * (o + len))] : List Instr)

/-- `mulz` with the multiplier and its `zp` in `r1` and `r2`. -/
def mulzF (acc b t : Reg) : List Instr := red b t .r4 ++ mulq acc b .r1 .r2 t .r4 ++ red acc t .r4

/-- A butterfly of the last layer of `NTT⁻¹`: the sum times `256⁻¹` (in `r1`
and `r2`), and the difference times the zeta's product with it (in `r6` and
`r7`), each reduced. -/
def bflyInvS (len o : Nat) : List Instr :=
  ([.ldr .r8 .r0 (4 * o), .ldr .r9 .r0 (4 * (o + len)), .dp .add .r12 .r8 (.reg .r9),
    .dp .add .r8 .r8 (.shifted .r5 .lsl 7), .dp .sub .r9 .r8 (.reg .r9)] : List Instr) ++
    mulzF .r10 .r12 .r8 ++ csub .r10 .r8 .r5 ++ ([.str .r10 .r0 (4 * o)] : List Instr) ++
    mulz .r10 .r9 .r12 ++ csub .r10 .r12 .r5 ++ ([.str .r10 .r0 (4 * (o + len))] : List Instr)

/-- The butterflies `b 0`, …, `b (u - 1)`. -/
def grp (b : Nat → List Instr) (u : Nat) : List Instr := (List.range u).flatMap b

/-- The zeta at `r1` to `r6`, and its `zp` to `r7`; `r1` then moves by 4
bytes (`op` is `add` or `sub`). -/
def zetaPre (op : DpOp) : List Instr :=
  ([.ldr .r6 .r1 0] : List Instr) ++ quot .r7 .r6 ++ ([.dp op .r1 .r1 (.imm 4)] : List Instr)

/-- A block of `len ≤ 4` butterflies `b`: its zeta, the butterflies, and
`r0` past the block. -/
def nttBlkS (b : Nat → List Instr) (len : Nat) (op : DpOp) : Prog isa :=
  .block (zetaPre op ++ grp b len ++
    ([.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (8 * len))), .subs .r2 .r2 (.imm 1)] : List Instr))

/-- The butterflies of a block four at a time, `r3` counting. -/
def grpLoop (b : Nat → List Instr) : Prog isa :=
  .loop (.block (grp b 4 ++ ([.dp .add .r0 .r0 (.imm 16), .subs .r3 .r3 (.imm 1)] : List Instr))) .ne

/-- A block of `len` butterflies `b`, `len` a multiple of 4: its zeta, the
butterflies four at a time, and `r0` past the block. -/
def nttBlkL (b : Nat → List Instr) (len : Nat) (op : DpOp) : Prog isa :=
  .seq (.block (zetaPre op ++ ([.mov .r3 (.imm (BitVec.ofNat 32 (len / 4)))] : List Instr)))
    (.seq (grpLoop b)
      (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4 * len))), .subs .r2 .r2 (.imm 1)]))

/-- A layer: its `128 / len` blocks `blk`, then `r0` back to `f`. -/
def nttLay (blk : Prog isa) (len : Nat) : Prog isa :=
  .seq (.block [.mov .r2 (.imm (BitVec.ofNat 32 (128 / len)))])
    (.seq (.loop blk .ne) (.block [.dp .sub .r0 .r0 (.imm 1024)]))

/-- The layers with `len` in `lens`, each of blocks `blk len`. -/
def lays (blk : Nat → Prog isa) : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (nttLay (blk len) len) (lays blk lens)

def ntt : Prog isa :=
  saving nttSaved (.seq (.block (storeTab zetaTab 256 ++ loadNQ .r4 ++ loadQ .r5 ++
      ([.dp .add .r1 .r1 (.imm 4)] : List Instr)))
    (.seq (lays (fun len => nttBlkL (bfly len) len .add) [128, 64, 32, 16, 8])
      (.seq (lays (fun len => nttBlkS (bfly len) len .add) [4, 2])
        (nttLay (nttBlkS (bflyC 1) 1 .add) 1))))

/-- The zeta of the last layer of `NTT⁻¹` times `256⁻¹`, modulo `q`. -/
def scaleZeta : Nat := negZetaTab 1 * 8347681 % 8380417

/-- `8347681 = 0x7F6021` and its `zp` in `r1` and `r2`, `scaleZeta` and its
`zp` in `r6` and `r7`, and the count of the groups in `r3`. -/
def scalePre : List Instr :=
  ([.movw .r1 0x6021, .movt .r1 0x7F] : List Instr) ++ quot .r2 .r1 ++
    ([.movw .r6 (BitVec.ofNat 16 (scaleZeta % 65536)), .movt .r6 (BitVec.ofNat 16 (scaleZeta / 65536))] :
      List Instr) ++ quot .r7 .r6 ++ ([.mov .r3 (.imm 32)] : List Instr)

def nttInv : Prog isa :=
  saving nttSaved (.seq (.block (storeTab negZetaTab 256 ++ loadNQ .r4 ++ loadQ .r5 ++
      ([.dp .add .r1 .r1 (.imm 1020)] : List Instr)))
    (.seq (lays (fun len => nttBlkS (bflyInv len) len .sub) [1, 2, 4])
      (.seq (lays (fun len => nttBlkL (bflyInv len) len .sub) [8, 16, 32, 64])
        (.seq (.block scalePre) (grpLoop (bflyInvS 128))))))

end VG.Impl.MlDsa.Arm.Arith
