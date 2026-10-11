import VerifiedGarbage.Proof.Idea.X86_64.Lit
import VerifiedGarbage.Impl.Idea.X86_64.Modes

/-! # IDEA-CBC, -OFB and -CFB64's x86-64 code as literals, for kernel-evaluated checks -/

namespace VG

/-! The block code the functions share, evaluated once. -/

materialize_value Impl.Idea.X86_64.cryptBlock

/-! The functions. -/

materialize_code Impl.Idea.X86_64.cbcEncrypt
materialize_code Impl.Idea.X86_64.cbcDecrypt
materialize_code Impl.Idea.X86_64.ofb
materialize_code Impl.Idea.X86_64.cfbEncrypt
materialize_code Impl.Idea.X86_64.cfbDecrypt

end VG
