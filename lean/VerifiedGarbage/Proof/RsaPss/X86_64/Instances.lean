module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCT
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# RSASSA-PSS verification with cached public-key values on x86-64: the stack pointer

That no instruction of the verification made with a hash function `v` and an
implementation `c` of the public operation writes the stack pointer, which
`Generic/MdHash/RsaPublicPrecomputed/X86_64/RsaPss.lean` registers.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

theorem code_spSafe (v : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.PublicImpl) :
    (Impl.RsaPss.X86_64.Precomputed.code v.H c.name c.code).all
      (fun i => !X86_64.isa.writesSp i) = true := by
  have h := code_safe v.ok v.K c
  rw [safeI_eq, allInstrs_and, Bool.and_eq_true] at h
  exact Code.all_of_allInstrs h.1

end VG.Proof.RsaPss.X86_64.Pc
