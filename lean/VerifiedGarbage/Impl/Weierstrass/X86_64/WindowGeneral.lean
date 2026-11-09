module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Window

/-!
# Short Weierstrass curves on x86-64: windows for any `a`

The window method of `Window.lean` (`WinCfg.window`) for a curve whose `a` is
not `-3`: the same recoding, table, selection of entries and loop, but

* the table's additions and the addition of each entry are the complete
  ones for any `a` (`rcb`, Algorithm 1 of Renes, Costello and Batina), with
  `a R mod p` in `S.a` and `3 b R mod p` in `S.b3` (where `window` has
  `b R mod p` for `rcb3`);
* the four doublings of each iteration are the Jacobian doubling for any `a`
  (`dblJGen`, dbl-2007-bl: `M = 3 X² + a Z⁴`, with `a` read from `S.a`).

`windowA` computes `[k]P` as `window` does, from the table of the bits of
`k + offset J`.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

namespace WinCfg

variable (K : WinCfg)

/-- `o = 2p` in Jacobian coordinates for any `a`, at the slot `S.a`
(dbl-2007-bl, with `Z' = 2YZ` as a product): `A = X²`, `B = Y²`, `C = B²`,
`D = 2 ((X + B)² - A - C)`, `M = 3A + a (Z²)²`, `Z' = 2YZ`, `X' = M² - 2D`,
`Y' = M (D - X') - 8C`; temporaries `t0 … t5`, `o` apart from `p`. -/
def dblJGen (S : RcbSlots) (p o : Pt) : List FOp :=
  [.mul S.t0 p.x p.x, .mul S.t1 p.y p.y, .mul S.t2 S.t1 S.t1, .add S.t3 p.x S.t1,
   .mul S.t3 S.t3 S.t3, .sub S.t3 S.t3 S.t0, .sub S.t3 S.t3 S.t2, .add S.t3 S.t3 S.t3,
   .mul S.t4 p.z p.z, .mul S.t4 S.t4 S.t4, .mul S.t4 S.a S.t4, .add S.t5 S.t0 S.t0,
   .add S.t5 S.t5 S.t0, .add S.t4 S.t4 S.t5, .mul o.z p.y p.z, .add o.z o.z o.z,
   .mul o.x S.t4 S.t4, .sub o.x o.x S.t3, .sub o.x o.x S.t3, .sub o.y S.t3 o.x,
   .mul o.y S.t4 o.y, .add S.t2 S.t2 S.t2, .add S.t2 S.t2 S.t2, .add S.t2 S.t2 S.t2,
   .sub o.y o.y S.t2]

/-- An entry of the table, as `buildStep`, by the complete addition for any `a`. -/
def buildStepA : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <| .seq (fprogB K.M (rcb K.S K.E K.P K.D)) <|
  .seq (.block (copyPt K.M.n K.E K.D)) <| .seq (storeEntry K 6) (.block [.alu .test .rbx (.reg .rbx)])

/-- The table, as `build`, by `buildStepA`. -/
def buildA : Prog isa :=
  .seq (.block (copyPt K.M.n (K.tblPt 1) K.P ++ copyPt K.M.n K.E K.P ++ [.mov32 .rbx (.imm 7)]))
    (.loop (buildStepA K) .ne)

/-- A pair of Jacobian doublings for any `a`, as `jacPair`. -/
def jacPairA : Prog isa :=
  .seq (fprogB K.M (dblJGen K.S K.E K.D)) <|
  .seq (fprogB K.M (dblJGen K.S K.D K.E)) <|
  .block [.alu .sub .rbx (.imm 4096), .alu .cmp .rbx (.imm 4096)]

/-- `R = 16 R` but where it is `O`, as `jac`, by `jacPairA`. -/
def jacA : Prog isa :=
  .seq (fprogB K.M (toJ K.S K.R (zeroPt K) K.E)) <|
  .seq (.block [.alu .add .rbx (.imm 8192)]) <|
  .seq (.loop (jacPairA K) .ae) <|
  fprogB K.M (fromJ K.S K.E (zeroPt K) K.R)

/-- `R = 16 R`. -/
def quadA : Prog isa := .seq (jacA K) (.block (ySel K))

/-- Iteration `j = rbx - 1`, as `step`: `R = 16 R + [d_j]P`, the addition the
complete one for any `a`. -/
def stepA : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (quadA K) <|
  .seq (.block ((tc K).digit ++ select K)) <|
  .seq (.block (tc K).negY) <|
  .seq (.seq (fprogB K.M (rcb K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))) <|
  .block [.alu .test .rbx (.reg .rbx)]

/-- `[k]P` into `R`, for the table of the bits of `k + offset J` at `K.bits`. -/
def windowA : Prog isa := .seq (buildA K) (.seq (.block (init K)) (.loop (stepA K) .ne))

end WinCfg

end VG.Impl.Weierstrass.X86_64
