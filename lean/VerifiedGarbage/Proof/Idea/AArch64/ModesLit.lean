import VerifiedGarbage.Proof.Idea.AArch64.Lit
import VerifiedGarbage.Impl.Idea.AArch64.Modes

/-! # IDEA-CBC, -OFB and -CFB64's AArch64 code as literals, for kernel-evaluated checks -/

namespace VG

/-! The block code the functions share, evaluated once. -/

materialize_value Impl.Idea.AArch64.cryptBlock

/-! The functions. -/

materialize_code Impl.Idea.AArch64.cbcEncrypt
materialize_code Impl.Idea.AArch64.cbcDecrypt
materialize_code Impl.Idea.AArch64.ofb
materialize_code Impl.Idea.AArch64.cfbEncrypt
materialize_code Impl.Idea.AArch64.cfbDecrypt

end VG
