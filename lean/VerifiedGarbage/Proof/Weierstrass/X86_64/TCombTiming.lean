module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
public import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Block

/-! Direct lookup addresses are determined by the public scalar and table. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

def publicLoads (K : TCombCfg) : List Instr :=
  TCombCfg.publicMask ++ K.publicLoad ++ K.selOne

def publicRest (K : TCombCfg) : Prog isa :=
  .seq (.block K.negY) <|
  .seq (fprogB K.M (rcb3m K.S K.A K.E K.D)) <|
  .block (K.digit ++ eqMask 0 ++ selPt K.M.n K.A K.D K.A ++ [.alu .test .rbx (.reg .rbx)])

end VG.Proof.Weierstrass.X86_64
