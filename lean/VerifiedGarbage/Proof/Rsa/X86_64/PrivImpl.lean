module

public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
public import VerifiedGarbage.Proof.Bignum.X86_64.PcCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Implementations of `vg_rsa_private_crt` on x86-64

A `CrtImpl` is what `vg_rsa_private_checked` needs of the implementation of
`vg_rsa_private_crt` it calls, so that its proof holds for each of them:
each is a variant of the interface `RsaPrivateCrt` on x86-64
(`Variants/RsaPrivateCrt/X86_64/`), and `vg_rsa_private_checked`, an
internal function of the padding functions, is emitted once for each. Every
implementation is proven against `crtContract` for callers that keep its
buffers off the return address of its calls (`Contract.clear`), and its
calls (of Montgomery multiplication) make no calls. It comes with the
`vg_rsa_public_precompute` of its Montgomery multiplication and an
independently verified `vg_rsa_public_precomputed_checked` operation that
checks its result, which are proven the same way. Both need no more CPU
features.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Rsa.X86_64

/-- An implementation of `vg_rsa_private_crt_precomputed` on x86-64. -/
structure CrtImpl where
  /-- The independently verified public operation used to check the result. -/
  pubOp : PublicImpl
  /-- What the names of `vg_rsa_private_checked_precomputed`'s instances end with (e.g.
  `_adx`; nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code and that of the public operation require,
  which `vg_rsa_private_checked_precomputed` requires too. -/
  features : List String
  /-- `vg_rsa_private_crt_precomputed`'s instance, which copies `R² mod n`
  from the key's precomputed values: its symbol and code, proven against
  `crtContractP`. -/
  nameP : String
  codeP : Prog isa
  depthP : codeP.depth = 1
  okP : ∀ s, crtContractP.clear.pre s → ∃ t s', Exec isa codeP s t s' ∧ abiPreserved s s' ∧ crtContractP.post s s'
  ctP : ConstantTime isa crtContractP.clear.pre crtContractP.pub codeP
  nospP : NoSp codeP
  spSafeP : codeP.all (fun i => !isa.writesSp i) = true
  /-- The CPU features it is chosen only with, besides those its code
  requires (`Registration.extra` of the functions that call it). -/
  extra : List String := []

/-! ## Octets and words of a buffer, in memories that agree on it

For the postconditions of the functions that return without secret residue
(`X86_64.Scrub.PostOut`), which read the memory on return only in their
buffers. -/

theorem bytesAt_agree {m₁ m₂ : Mem} {p : Addr} {n k : Nat} (hk : k ≤ n) (hn : n < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.bytesAt m₂ p k = Spec.Rsa.bytesAt m₁ p k := by
  unfold Spec.Rsa.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (Offset.contains_base _ (by omega_using [hk, this]) (by omega_using [hk, hn, this]))).symm

theorem readW_agree {m₁ m₂ : Mem} {p : Addr} {n : Nat} (hk : 8 ≤ n) (hn : n < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    m₂.readW p 64 = m₁.readW p 64 :=
  Mem.readW_congr fun i hi => (h _ (Offset.contains_base _ (by omega) (by omega_using [hi]))).symm

end VG.Proof.Rsa.X86_64
