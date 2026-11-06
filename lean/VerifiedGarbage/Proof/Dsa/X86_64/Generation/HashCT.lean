module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration

/-! # Seed-hash selection and streaming calls have public traces -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem seedHashAt_ct {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream}
    (h1 : Calls.StreamOK G1) (h256 : Calls.StreamOK G256)
    (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) (len : Nat) :
    RelCT isa (Two (LW n)) (Impl.Dsa.X86_64.Generation.seedHashAt G1 G256 len)
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.seedHashAt
  split
  · exact hashLabel_ct h1 n hn (Or.inl rfl)
  · exact hashLabel_ct h256 n hn (Or.inl rfl)

end VG.Proof.Dsa.X86_64.Generation
