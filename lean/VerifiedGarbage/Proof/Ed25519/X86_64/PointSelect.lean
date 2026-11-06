module

public import VerifiedGarbage.Impl.Ed25519.X86_64.PointSelect
public import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Point selection reuses the verified constant-time field swaps. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr mask F cswap_ok)

def swapEnv (a b : Slot) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e a (if sw then e b else e a)) b (if sw then e a else e b)

end VG.Proof.Ed25519.X86_64
