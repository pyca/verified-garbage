module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scan
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bound
public import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ScanRawCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scan
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bound
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ScanRawCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH on x86-64: bound selection depends only on the public domain -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Secret random bytes are existential; domain data is shared between runs. -/
def I (p : GkP) (s : State) : Prop := ∃ rb, Inputs p rb s

end VG.Proof.Ffdh.X86_64.GenerateKey
