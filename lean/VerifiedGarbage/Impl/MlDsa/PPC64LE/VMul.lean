module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.VNttInv

/-!
# ML-DSA on PPC64LE: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt` with VMX

Four coefficients at a time, on the word lanes (Power ISA 2.07):

* `f·g·2⁻³² mod q`, as Montgomery reduces: `m = (f·g mod 2³²)·q⁻¹ mod 2³²`
  (`vmuluwm`), so that `f·g − m·q` is a multiple of `2³²`; the high words of
  `f·g` and of `m·q` (`vmuleuw`, `vmulouw`, `vperm`), their difference, which is
  `(f·g − m·q) / 2³²`, in `(−q, q)`, reduced by `min(d, d + q)` (`mont`);
* times `2³² mod q` as Shoup multiplies by a constant (`smul`, `VNttInv.lean`),
  which gives `f·g mod q`;
* plus `h`, reduced by `min(s, s − q)`, for `vg_mldsa_multiply_add_ntt`.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.VNtt

open VG.PPC64LE

/-- `q⁻¹ mod 2³²`. -/
def qInv : Nat := 58728449

/-- `2³² mod q`. -/
def rMod : Nat := 4193792

/-- `v` in each lane of `d`, through `r12`. -/
def splatW (d : VReg) (v : Nat) : List Instr :=
  loadImm .r12 v ++ ([.mtvsrd d .r12, .vop (.splat true d d 1)] : List Instr)

/-- `q`, the control of the high words, `q⁻¹`, `2³² mod q` and its `z'`;
the counter. -/
def mulConsts : List Instr :=
  consts ++ splatW .v13 qInv ++ splatW .v2 rMod ++ splatW .v3 (shoup rMod) ++ [.li .r9 0, .li .r10 64]

/-- `v8 ← v8 · v9 · 2⁻³² mod q`, through `v6`, `v7`, `v10` and `v11`. -/
def mont : List Instr :=
  [.vop (.muluwm .v10 .v8 .v9), .vop (.muluwm .v10 .v10 .v13),
   .vop (.mulu false true .v6 .v8 .v9), .vop (.mulu true true .v7 .v8 .v9), .vop (.perm .v11 .v6 .v7 .v5),
   .vop (.mulu false true .v6 .v10 .v4), .vop (.mulu true true .v7 .v10 .v4), .vop (.perm .v6 .v6 .v7 .v5),
   .vop (.sub true .v8 .v11 .v6), .vop (.add false .v7 .v8 .v4), .vop (.minu true .v8 .v8 .v7)]

def vmulBody : List Instr :=
  [.lxvd2x .v8 .r4 .r9, .lxvd2x .v9 .r5 .r9] ++ mont ++ smul .v8 ++
  [.stxvd2x .v8 .r3 .r9, .addi .r3 .r3 16, .addi .r4 .r4 16, .addi .r5 .r5 16, .subi .r10 .r10 1]

def vmulAddBody : List Instr :=
  [.lxvd2x .v8 .r4 .r9, .lxvd2x .v9 .r5 .r9] ++ mont ++ smul .v8 ++
  [.lxvd2x .v9 .r3 .r9, .vop (.add false .v6 .v8 .v9), .vop (.sub true .v7 .v6 .v4), .vop (.minu true .v8 .v6 .v7),
   .stxvd2x .v8 .r3 .r9, .addi .r3 .r3 16, .addi .r4 .r4 16, .addi .r5 .r5 16, .subi .r10 .r10 1]

def vmul : Prog isa := .seq (.block mulConsts) (.loop (.block vmulBody) (.nonzero .d .r10))

def vmulAdd : Prog isa := .seq (.block mulConsts) (.loop (.block vmulAddBody) (.nonzero .d .r10))

end VG.Impl.MlDsa.PPC64LE.VNtt
