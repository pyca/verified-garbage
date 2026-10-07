import VerifiedGarbage.Impl.Weierstrass.X86_64.JointFixed
import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCache
import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCacheBuild
import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJac
import VerifiedGarbage.Impl.Weierstrass.X86_64.JacMixedForward
import VerifiedGarbage.Impl.Weierstrass.X86_64.FastNaf

/-! Interleaved public multiplication with cached peer and fixed-generator digits. -/
namespace VG.Impl.Weierstrass.X86_64.Joint
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass

structure Cfg where
  K : WinCfg
  gBits : Nat
  tsym : String
  cache : Nat
  selected : Nat

def prep (c : Cfg) (u v : Nat) : Prog isa :=
  .seq (FastNaf.prep u c.gBits 7) (FastNaf.prep v c.K.bits 5)

def cachedDigit (c : Cfg) : Prog isa :=
  .seq (.block (Naf.digitRead c.K)) <|
    .ite .e (.block []) (.seq (Naf.signedCachedEntry c.K c.cache c.selected) <|
      .seq (CachedJac.add c.K c.K.R c.K.E c.K.D c.selected)
        (.block (copyPt 4 c.K.R c.K.D)))

def fixedDigit (c : Cfg) : Prog isa :=
  .seq (.block (Naf.digitRead {c.K with bits := c.gBits})) <|
    .ite .e (.block []) (.seq (fixedEntry c.K c.tsym) <|
      .seq (Jacobian.jacMixedForward c.K c.K.R c.K.E c.K.D)
        (.block (copyPt 4 c.K.R c.K.D)))

def digits (c : Cfg) : Prog isa := .seq (cachedDigit c) (fixedDigit c)

def step (c : Cfg) (double : Prog isa) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
    .seq double (.seq (digits c) (.block [.alu .test .rbx (.reg .rbx)]))

def run (c : Cfg) (double : Prog isa) : Prog isa :=
  .seq (digits c) (.loop (step c double) .ne)

def window (c : Cfg) (double : Prog isa) : Prog isa :=
  .seq (Naf.table c.K) <| .seq (Naf.cacheTable c.K.M c.K.tbl c.cache 8) <|
    .seq (.block (Jacobian.infinity c.K c.K.R ++ [.mov32 .rbx (.imm 256)])) (run c double)

end VG.Impl.Weierstrass.X86_64.Joint
