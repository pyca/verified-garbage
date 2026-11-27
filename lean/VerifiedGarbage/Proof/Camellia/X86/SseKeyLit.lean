module

public import VerifiedGarbage.Impl.Camellia.X86.SseExpandKey
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Camellia.X86.SseExpandKey
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # Camellia's key schedule on x86 (32-bit) in XMM registers: the code as a literal -/

@[expose] public section

namespace VG.Proof.Camellia.X86.SseKey

materialize_code expandKeyCode := Impl.Camellia.X86.SseKey.expandKey

end VG.Proof.Camellia.X86.SseKey
