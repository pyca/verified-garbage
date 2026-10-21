module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.JointFixed
public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCache
public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCacheBuild
public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCoZ
public import VerifiedGarbage.Impl.Weierstrass.X86_64.FastNaf
public import VerifiedGarbage.Impl.Weierstrass.X86_64.PointOps

/-! Interleaved public multiplication with cached peer and fixed-generator digits. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Joint
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass

structure Cfg where
  K : WinCfg
  gBits : Nat
  tsym : String
  cache : Nat
  selected : Nat
  /-- The curve whose functions run the digits' additions
  (`Spec/Weierstrass/PointOps.lean`), if they are calls, else inline. -/
  pts : Option Spec.Weierstrass.PointOps.Curve := none
  /-- Whether the top digit's additions are a copy before the loop, rather
  than its first iteration (`guardDouble`): faster on some CPUs for some
  curves (P-256 on Intel). -/
  peel : Bool := false
  /-- Whether the cache of `Z²` and `Z³` is built unrolled rather than in a
  loop: faster on some CPUs for some curves (P-521 on Zen 5). Without BMI2
  and ADX, by the loop's steps unrolled (`Naf.cacheStaged`), whose nine-word
  products are calls; with them, written out (`Naf.cacheUnrolled`), which
  was faster on Zen 3. -/
  cacheUnroll : Bool := false
  /-- Whether the table of `Q`'s odd multiples is built by co-Z arithmetic
  (`Naf.tableCoZ`, from an affine `Q`) rather than by Jacobian additions
  (`Naf.table`). -/
  coZ : Bool := false
  /-- The width of the generator's digits: seven, stored as bytes, or nine,
  as sixteen-bit words (`FastNaf.prepN16`), for a table of `[m]G` for
  `m ≤ 256` at `tsym`. -/
  gw : Nat := 7

def prep (c : Cfg) (u v : Nat) : Prog isa :=
  .seq (if c.gw=9 then FastNaf.prepN16 c.K.M.n u c.gBits else FastNaf.prepN c.K.M.n u c.gBits 7)
    (FastNaf.prepN c.K.M.n v c.K.bits 5)

/-- `R = R + E`, `E`'s `Z²` and `Z³` at `selected`. -/
def cachedAdd (c : Cfg) : Prog isa :=
  match c.pts with
  | some C => PointOps.addCachedCall C c.K c.selected
  | none => PointOps.addCachedBody c.K c.selected

/-- `R = R + E`, `E` affine. -/
def fixedAdd (c : Cfg) : Prog isa :=
  match c.pts with
  | some C => PointOps.addAffineCall C c.K
  | none => PointOps.addAffineBody c.K

def cachedDigit (c : Cfg) : Prog isa :=
  .seq (.block (Naf.digitRead c.K)) <|
    .ite .e (.block []) (.seq (Naf.signedCachedEntry c.K c.cache c.selected) (cachedAdd c))

/-- The generator's digit `rbx`, zero-extended into `r8`, and its test. -/
def fixedRead (c : Cfg) : List Instr :=
  if c.gw=9 then [.movzx16 .r8 (FastNaf.tbl16 c.gBits),.alu .test .r8 (.reg .r8)]
  else Naf.digitRead {c.K with bits := c.gBits}

def fixedDigit (c : Cfg) : Prog isa :=
  .seq (.block (fixedRead c)) <|
    .ite .e (.block []) (.seq (if c.gw=9 then fixedEntryW c.K c.tsym else fixedEntry c.K c.tsym)
      (fixedAdd c))

def digits (c : Cfg) : Prog isa := .seq (cachedDigit c) (fixedDigit c)

/-- The loop's first value of the counter `rbx`. -/
def top (c : Cfg) : Nat := if c.peel then 64*c.K.M.n else 64*c.K.M.n+1

/-- The doubling but in the first iteration (`rbx = 64 n`, the counter
public), where `R` is `O`: the loop runs the top digit's additions too,
rather than a copy of them before it (unless `peel`). -/
def guardDouble (c : Cfg) (double : Prog isa) : Prog isa :=
  if c.peel then double
  else .seq (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 (64*c.K.M.n)))]) (.ite .e (.block []) double)

def step (c : Cfg) (double : Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
    .seq (guardDouble c double) (.seq (digits c) (.block [.alu .test .rbx (.reg .rbx)]))

def run (c : Cfg) (double : Prog isa) : Prog isa :=
  if c.peel then .seq (digits c) (.loop (step c double) .ne) else .loop (step c double) .ne

/-- The cache of the eight entries' `Z²` and `Z³`. -/
def cacheCode (c : Cfg) : Prog isa :=
  if c.cacheUnroll then
    if c.K.M.adx then Naf.cacheUnrolled c.K.M c.K.tbl c.cache 8 else Naf.cacheStaged c.K.M c.K.tbl c.cache c.K.E.x
  else Naf.cacheTable c.K.M c.K.tbl c.cache c.K.E.x

/-- The table of `Q`'s odd multiples. -/
def tableCode (c : Cfg) : Prog isa := if c.coZ then Naf.tableCoZ c.K else Naf.table c.K

def window (c : Cfg) (double : Prog isa) : Prog isa :=
  .seq (tableCode c) <| .seq (cacheCode c) <|
    .seq (.block (Jacobian.infinity c.K c.K.R ++ [.mov32 .rbx (.imm (BitVec.ofNat 32 (top c)))])) (run c double)

end VG.Impl.Weierstrass.X86_64.Joint
