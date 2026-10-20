module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit
public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
public import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
import VerifiedGarbage.Impl.Sha256.X86.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Md5.X86.Compress
import VerifiedGarbage.Proof.Pbkdf2.MdHmac
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
meta import VerifiedGarbage.Impl.Sha256.X86.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Md5.X86.Compress
meta import VerifiedGarbage.Proof.Pbkdf2.MdHmac
meta import VerifiedGarbage.Proof.Pbkdf2.Memory
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Proof.Sha256.X86.Compress
meta import VerifiedGarbage.Proof.Sha512.Spec
meta import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
meta import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the functions it calls, and its code as literals

For each hash function of `Proof/Pbkdf2/Md/X86/Hashes.lean`, the functions
`pbkdf2` calls (`Fns`): its streaming functions, HMAC's `init` and
`finalize` and PBKDF2's `iterate` (`Impl/Pbkdf2/Md/X86.lean`) for it, by the names they are registered with; and
`pbkdf2` as a literal (`materialize_code`, `Proof/Framework/Lit.lean`), which
the registration files' `spSafe` checks evaluate.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Pbkdf2.Md.X86

/-- The functions `pbkdf2` calls for the hash function `M` of the instance
`I`, with the working space of `I`'s functions. -/
def fnsOf (I : Spec.Hmac.Instance) (M : Impl.Pbkdf2.Md.X86.Hash) : Fns where
  H := M.st
  W := I.scratch
  hiN := I.initScratchApi.name
  hiC := M.hmacInit
  hfN := I.finalizeScratchApi.name
  hfC := M.hmacFin
  itN := I.iterateApi.name
  itC := M.iterate

def md5F : Fns := fnsOf Spec.Hmac.md5I md5M
def sha384F : Fns := fnsOf Spec.Hmac.sha384I sha384M
def sha512F : Fns := fnsOf Spec.Hmac.sha512I sha512M'
def sha512_224F : Fns := fnsOf Spec.Hmac.sha512_224I sha512_224M
def sha512_256F : Fns := fnsOf Spec.Hmac.sha512_256I sha512_256M

materialize_code md5Pbkdf2 := md5F.pbkdf2
materialize_code sha384Pbkdf2 := sha384F.pbkdf2
materialize_code sha512Pbkdf2 := sha512F.pbkdf2
materialize_code sha512_224Pbkdf2 := sha512_224F.pbkdf2
materialize_code sha512_256Pbkdf2 := sha512_256F.pbkdf2

end VG.Proof.Pbkdf2.Whole.X86
