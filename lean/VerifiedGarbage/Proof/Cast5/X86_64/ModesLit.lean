module

public import VerifiedGarbage.Proof.Cast5.X86_64.Lit
meta import VerifiedGarbage.Proof.Cast5.X86_64.Lit
public import VerifiedGarbage.Impl.Cast5.X86_64.Modes
meta import VerifiedGarbage.Impl.Cast5.X86_64.Modes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # CAST5-CBC, -OFB and -CFB64's x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

/-! The block code the functions share, evaluated once. -/

materialize_value Impl.Cast5.X86_64.encryptBlock
materialize_value Impl.Cast5.X86_64.decryptBlock

/-! The functions. -/

materialize_code Impl.Cast5.X86_64.cbcEncrypt
materialize_code Impl.Cast5.X86_64.cbcDecrypt
materialize_code Impl.Cast5.X86_64.ofb
materialize_code Impl.Cast5.X86_64.cfbEncrypt
materialize_code Impl.Cast5.X86_64.cfbDecrypt

end VG
