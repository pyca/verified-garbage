module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
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
import VerifiedGarbage.Spec.Pbkdf2.Generic
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
# HMAC's `init` and `finalize` and PBKDF2's `iterate` on x86 (32-bit): the code as literals

`Hash.hmacInit`, `Hash.hmacFin` and `Hash.iterate` (`Impl/Pbkdf2/Md/X86.lean`) at each hash
function of `Hashes.lean`, as literals (`materialize_code`,
`Proof/Framework/Lit.lean`) that refer to the literals of the functions they
call (the compression functions, and the streaming `init` and `finalize`): the
registration files' `spSafe` checks evaluate them.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86

materialize_code md5MInit := md5M.hmacInit
materialize_code md5MFinalize := md5M.hmacFin
materialize_code md5MIterate := md5M.iterate
materialize_code sha384MInit := sha384M.hmacInit
materialize_code sha384MFinalize := sha384M.hmacFin
materialize_code sha384MIterate := sha384M.iterate
materialize_code sha512MInit := sha512M'.hmacInit
materialize_code sha512MFinalize := sha512M'.hmacFin
materialize_code sha512MIterate := sha512M'.iterate
materialize_code sha512_224MInit := sha512_224M.hmacInit
materialize_code sha512_224MFinalize := sha512_224M.hmacFin
materialize_code sha512_224MIterate := sha512_224M.iterate
materialize_code sha512_256MInit := sha512_256M.hmacInit
materialize_code sha512_256MFinalize := sha512_256M.hmacFin
materialize_code sha512_256MIterate := sha512_256M.iterate

end VG.Proof.Pbkdf2.Md.X86
