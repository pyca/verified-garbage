import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
import VerifiedGarbage.Proof.Bignum.X86_64.PcCode

/-!
# Implementations of `vg_rsa_private_crt` on x86-64

A `CrtImpl` is what `vg_rsa_private_checked` needs of the implementation of
`vg_rsa_private_crt` it calls, so that its proof holds for each of them:
each is a variant of the interface `RsaPrivateCrt` on x86-64
(`Variants/RsaPrivateCrt/X86_64/`), and `vg_rsa_private_checked`
(`Generic/RsaPrivateCrt/X86_64/Rsa.lean`) is emitted once for each. Every
implementation is proven against `crtContract` for callers that keep its
buffers off the return address of its calls (`Contract.clear`), and its
calls (of Montgomery multiplication) make no calls. It comes with the
`vg_rsa_public_precompute` of its Montgomery multiplication and an
independently verified `vg_rsa_public_precomputed_checked` operation that
checks its result, which are proven the same way. Both need no more CPU
features.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Rsa.X86_64

/-- An implementation of `vg_rsa_private_crt` on x86-64. -/
structure CrtImpl where
  /-- Its symbol and code. -/
  name : String
  code : Prog isa
  /-- Its calls make no calls. -/
  depth : code.depth = 1
  ok : ∀ s, crtContract.clear.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ crtContract.post s s'
  ct : ConstantTime isa crtContract.clear.pre crtContract.pub code
  /-- It never writes the stack pointer. -/
  nosp : NoSp code
  spSafe : code.all (fun i => !isa.writesSp i) = true
  /-- The suffix of the name of `vg_rsa_public_precompute`, and its code. -/
  montSuffix : String
  pc : Prog isa
  pcOk : ∀ s, pcContract.clear.pre s → ∃ t s', Exec isa pc s t s' ∧ abiPreserved s s' ∧ pcContract.post s s'
  pcCt : ConstantTime isa pcContract.clear.pre pcContract.pub pc
  pcMx : pc.allInstrs (fun i => !loadsMxcsr i) = true
  /-- The independently verified public operation used to check the result. -/
  pubOp : PublicImpl
  pcNosp : NoSp pc
  pcDepth : pc.depth = 1
  pcSpSafe : pc.all (fun i => !isa.writesSp i) = true
  /-- What the names of `vg_rsa_private_checked`'s instances end with (e.g.
  `_adx`; nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code and that of the public operation require,
  which `vg_rsa_private_checked` requires too. -/
  features : List String


end VG.Proof.Rsa.X86_64
