module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.P521Fast
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WindowJ

/-!
# P-521's 4-bit windows on x86-64 with BMI2 and ADX, by the fast field steps

`WinCfg.windowJ` with its doublings in place (`dblCmsSteps`, `R = 2R` four
times a window, `quadF`) and its mixed addition (`maddJ`) by the steps of
`P521Fast.lean` (`stepProg`): products by calls of `vg_p521_sqr_adx`,
`vg_p521_mul_adx` and `vg_p521_mulw_adx` (whose results only a `cms` reads:
`weakOp`), the sums and differences and `cmsF` inline. The calls change
`rbx` and `rsi`, which a point operation keeps in `xmm15` and `xmm14`
(`save`, `restore`).
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.P521F

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64

/-- `rbx` and `rsi` into `xmm15` and `xmm14`. -/
def save : List Instr := [.xop (.movq .xmm15 .rbx), .xop (.movq .xmm14 .rsi)]

/-- `rbx` and `rsi` back. -/
def restore : List Instr := [.movqR .rbx .xmm15, .movqR .rsi .xmm14]

/-- The products only `cms` reads: `X Y²` (into `t5`) and `t3 x2p` (into `t4`). -/
def weakOp (S : RcbSlots) (o a : Nat) : Bool := o == S.t5 || (o == S.t4 && a == S.t3)

/-- A step's code. -/
def stepProg (S : RcbSlots) : DStep → Prog isa
  | .op (.mul o a b) => pmul (weakOp S o a) o a b
  | .op (.add o a b) => .block (sAdd o a b)
  | .op (.sub o a b) => .block (sSub o a b)
  | .cms o C a D b => .block (cmsF o C a D b)

/-- `p = 2p` in place. -/
def dbl (S : RcbSlots) (p : Pt) : Prog isa :=
  .seq (.block save) (.seq (progs ((dblCmsSteps S p).map (stepProg S))) (.block restore))

/-- The slots no product of `maddJ` writes weakly. -/
def maddS : RcbSlots := ⟨0, 0, 1, 1, 1, 1, 1, 1⟩

/-- `o = p + q` for an affine `q`, by `maddJ`. -/
def madd (S : RcbSlots) (p q o : Pt) : Prog isa :=
  .seq (.block save) (.seq (progs ((maddJ S p q o).map fun f => stepProg maddS (.op f))) (.block restore))

namespace Win

variable (K : WinCfg)

/-- `R = 16 R`: four doublings in place, the public count in the bits of `rbx`
above the window index. -/
def quadF : Prog isa := .seq (.block [.alu .add .rbx (.imm 16384)])
  (.loop (.seq (dbl K.S K.R) (.block [.alu .sub .rbx (.imm 4096), .alu .cmp .rbx (.imm 4096)])) .ae)

/-- `WinCfg.stepJ` by `quadF` and `madd`. -/
def stepF : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <| .seq (quadF K) <|
  .seq (.block ((WinCfg.tc K).digit ++ WinCfg.select K)) <| .seq (.block (WinCfg.tc K).negY) <|
  .seq (.seq (madd K.S K.R K.E K.D) (.block (WinCfg.selSum K))) <| .block [.alu .cmp .rbx (.imm 1)]

/-- `WinCfg.windowJ` by `stepF`. -/
def windowF (inv : Prog isa) : Prog isa :=
  .seq (WinCfg.build K) <| .seq (WinCfg.normTbl K inv) <| .seq (.block (WinCfg.init K)) <|
  .seq (.loop (stepF K) .ne) (WinCfg.stepLast K)

end Win

end VG.Impl.Weierstrass.X86_64.P521F
