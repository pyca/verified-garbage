module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.VNtt

/-!
# ML-DSA on PPC64LE: `vg_mldsa_inv_ntt` with VMX

Algorithm 42 as `vg_mldsa_ntt` (`VNtt.lean`) does Algorithm 41, its layers in
the other order: the layers of `len = 1` and `len = 2` sixteen coefficients at
a time through the transpose (`narrowInv`), then those of `len = 4 … 128`
(`wideInv`), then the product by `f = 256⁻¹ · R mod q`, 8347681 (`scale`).

* A butterfly takes `a + b`, reduced by `min(s, s − q)`, and `z·(b − a)`,
  `b − a` reduced by `min(d, d + q)` and then multiplied by `z` as Shoup does
  (`ibfly`): Algorithm 42's `−ζ·(a − b)`.
* The `scratch` space holds `z'` of each zeta at `invK`'s positions: the
  blocks of `len ≥ 4` in the order they run, from position 1; a group's
  zetas of `len = 1` and `len = 2` where the forward transform has its own
  (`scrK`), so that each lane loads its own.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.VNtt

open VG.PPC64LE

/-- The zeta whose `z'` is at position `p` of `scratch`: the blocks of
`len ≥ 4` run from zeta 63 down to 1, a group's blocks of `len = 2` and
`len = 1` (`127 − c` and `255 − c`) in the lanes the forward transform loads
its own blocks' (`64 + c`, `128 + c`). -/
def invK (p : Nat) : Nat := (if p < 64 then 64 else if p < 128 then 191 else 383) - scrK p

/-- `(a, b) ← (a + b, z·(b − a))`, through `v6` and `v7`. -/
def ibfly (a b z zp : VReg) : List Instr :=
  [.vop (.sub true .v6 b a), .vop (.add false .v7 .v6 .v4), .vop (.minu true .v6 .v6 .v7),
   .vop (.add false .v7 a b), .vop (.sub true a .v7 .v4), .vop (.minu true a .v7 a),
   .vop (.mulu false true .v7 .v6 zp), .vop (.mulu true true b .v6 zp), .vop (.perm .v7 .v7 b .v5),
   .vop (.muluwm b .v6 z), .vop (.muluwm .v7 .v7 .v4), .vop (.sub true b b .v7),
   .vop (.sub true .v7 b .v4), .vop (.minu true b b .v7)]

/-! ## `len ≥ 4` -/

def iStepBody : List Instr :=
  [.lxvd2x .v0 .r5 .r9, .lxvd2x .v1 .r5 .r8] ++ ibfly .v0 .v1 .v2 .v3 ++
  [.stxvd2x .v0 .r5 .r9, .stxvd2x .v1 .r5 .r8, .addi .r5 .r5 16, .subi .r10 .r10 1]

def iBlockCode : Prog isa :=
  .seq (.block ([.lxvd2x .v3 .r7 .r9, .vop (.splat true .v3 .v3 0), .addi .r7 .r7 4] ++ zcalc ++
      [.lsr .d .r10 .r8 4]))
    (.seq (.loop (.block iStepBody) (.nonzero .d .r10))
      (.block [.add .r5 .r5 .r8, .sub .r12 .r5 .r11]))

/-- A layer: its blocks, from `f`; then `len` doubles, until it passes 128. -/
def iLayerCode : Prog isa :=
  .seq (.block [.addi .r5 .r3 0])
    (.seq (.loop iBlockCode (.nonzero .d .r12)) (.block [.lsl .r8 .r8 1, .subi .r12 .r8 1024]))

/-- The six layers of `len = 4 … 128`. -/
def wideInv : Prog isa :=
  .seq (.block [.li .r8 16, .addi .r11 .r3 1024, .li .r9 0, .addi .r7 .r4 0])
    (.loop iLayerCode (.nonzero .d .r12))

/-! ## `len = 1` and `len = 2` -/

/-- As `groupBody`: transposed, `v9`, `v8`, `v11`, `v10` hold coefficients
`4r … 4r+3` of the group in lane `r`. The `z'` of `len = 1` are at `[r7]`
and `[r7 + 16]`, of `len = 2` at `[r6]`. -/
def iGroupBody : List Instr :=
  [.lxvd2x .v8 .r5 .r9, .lxvd2x .v9 .r5 .r8, .lxvd2x .v10 .r5 .r11, .lxvd2x .v11 .r5 .r12] ++
  transpose ++
  [.lxvd2x .v3 .r7 .r9] ++ zcalc ++ ibfly .v9 .v8 .v2 .v3 ++
  [.lxvd2x .v3 .r7 .r8] ++ zcalc ++ ibfly .v11 .v10 .v2 .v3 ++
  [.lxvd2x .v3 .r6 .r9] ++ zcalc ++ [.addi .r6 .r6 16, .addi .r7 .r7 32] ++
  ibfly .v9 .v11 .v2 .v3 ++ ibfly .v8 .v10 .v2 .v3 ++
  transpose ++
  [.stxvd2x .v8 .r5 .r9, .stxvd2x .v9 .r5 .r8, .stxvd2x .v10 .r5 .r11, .stxvd2x .v11 .r5 .r12,
   .addi .r5 .r5 64, .subi .r10 .r10 1]

def narrowInv : Prog isa :=
  .seq (.block [.addi .r5 .r3 0, .li .r9 0, .li .r8 16, .li .r11 32, .li .r12 48, .li .r10 16,
      .addi .r6 .r4 256, .addi .r7 .r4 512])
    (.loop (.block iGroupBody) (.nonzero .d .r10))

/-! ## The product by `f` -/

def fInv : Nat := 8347681

/-- `a ← f·a`, with `f` in each lane of `v2` and `f'` of `v3`; through `v6`
and `v7`. -/
def smul (a : VReg) : List Instr :=
  [.vop (.mulu false true .v6 a .v3), .vop (.mulu true true .v7 a .v3), .vop (.perm .v6 .v6 .v7 .v5),
   .vop (.muluwm .v7 a .v2), .vop (.muluwm .v6 .v6 .v4), .vop (.sub true .v7 .v7 .v6),
   .vop (.sub true .v6 .v7 .v4), .vop (.minu true a .v7 .v6)]

def scaleBody : List Instr :=
  [.lxvd2x .v8 .r5 .r9, .lxvd2x .v9 .r5 .r8, .lxvd2x .v10 .r5 .r11, .lxvd2x .v11 .r5 .r12] ++
  smul .v8 ++ smul .v9 ++ smul .v10 ++ smul .v11 ++
  [.stxvd2x .v8 .r5 .r9, .stxvd2x .v9 .r5 .r8, .stxvd2x .v10 .r5 .r11, .stxvd2x .v11 .r5 .r12,
   .addi .r5 .r5 64, .subi .r10 .r10 1]

def scale : Prog isa :=
  .seq (.block (loadImm .r12 fInv ++ [.mtvsrd .v2 .r12, .vop (.splat true .v2 .v2 1)] ++
      loadImm .r12 (shoup fInv) ++ [.mtvsrd .v3 .r12, .vop (.splat true .v3 .v3 1),
      .addi .r5 .r3 0, .li .r8 16, .li .r11 32, .li .r12 48, .li .r10 16]))
    (.loop (.block scaleBody) (.nonzero .d .r10))

/-! ## `vg_mldsa_inv_ntt` -/

def nttInv : Prog isa := .seq (.block (fillK invK ++ consts)) (.seq narrowInv (.seq wideInv scale))

end VG.Impl.MlDsa.PPC64LE.VNtt
