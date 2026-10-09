module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Md5.X86_64.Stream
meta import VerifiedGarbage.Impl.Md5.X86_64.Stream

/-!
# MD5 on x86-64: the code as literals
-/

@[expose] public section


namespace VG

materialize_code Impl.Md5.X86_64.compress
materialize_code Impl.Md5.X86_64.Stream.update
materialize_code Impl.Md5.X86_64.Stream.finalize

end VG
