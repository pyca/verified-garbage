import VerifiedGarbage.Impl.Weierstrass.X86_64.JointFixed
import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCache
import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCacheBuild
import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJac
import VerifiedGarbage.Impl.Weierstrass.X86_64.JacMixedForward
import VerifiedGarbage.Impl.Weierstrass.X86_64.FastNaf
import VerifiedGarbage.Impl.Weierstrass.X86_64.PointOps

/-! Interleaved public multiplication with cached peer and fixed-generator digits. -/
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

def prep (c : Cfg) (u v : Nat) : Prog isa :=
  .seq (FastNaf.prepN c.K.M.n u c.gBits 7) (FastNaf.prepN c.K.M.n v c.K.bits 5)

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

def fixedDigit (c : Cfg) : Prog isa :=
  .seq (.block (Naf.digitRead {c.K with bits := c.gBits})) <|
    .ite .e (.block []) (.seq (fixedEntry c.K c.tsym) (fixedAdd c))

def digits (c : Cfg) : Prog isa := .seq (cachedDigit c) (fixedDigit c)

def step (c : Cfg) (double : Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
    .seq double (.seq (digits c) (.block [.alu .test .rbx (.reg .rbx)]))

def run (c : Cfg) (double : Prog isa) : Prog isa :=
  .seq (digits c) (.loop (step c double) .ne)

def window (c : Cfg) (double : Prog isa) : Prog isa :=
  .seq (Naf.table c.K) <| .seq (Naf.cacheTable c.K.M c.K.tbl c.cache 8) <|
    .seq (.block (Jacobian.infinity c.K c.K.R ++ [.mov32 .rbx (.imm (BitVec.ofNat 32 (64*c.K.M.n)))])) (run c double)

end VG.Impl.Weierstrass.X86_64.Joint
