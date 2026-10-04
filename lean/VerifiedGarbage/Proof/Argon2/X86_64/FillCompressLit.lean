import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.FillWrite

/-! A checked literal for the block write after compression. -/

namespace VG

materialize_code Impl.Argon2.X86_64.FillWrite.code

end VG
